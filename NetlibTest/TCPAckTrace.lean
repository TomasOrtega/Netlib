import Netlib.Protocol.TCP.AckTrace

namespace NetlibTest.TCPAckTrace

open Netlib Packet Protocol
namespace A
export TCP.ApplicationTrace (Step Event Chain Chronological)
end A

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def fails (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "An unresolved or unsupported ACK trace received assurance.")

private def tuple : Packet.Header := ⟨3221225986, 3325256706, Packet.Protocol.tcp, 41000, 9000⟩

private def seed : TCP.Endpoint.State := {
  core := ⟨tuple, TCP.Seq.ofNat 100, 4096, [], TCP.Seq.ofNat 200, TCP.Seq.ofNat 200, []⟩
  pending := []
  pendingLimit := 4096
  sendWindow := 4096
  sendWL1 := TCP.Seq.ofNat 0
  sendWL2 := TCP.Seq.ofNat 200
  effectiveMSS := 800
  ipSendLimit := 1500
  localReceiveMSS := .present ⟨⟨1200, by decide⟩, by decide⟩ }

structure Replay where
  current : TCP.Endpoint.State
  valid : current.Valid
  steps : List A.Step
  chain : A.Chain seed steps current
  ordered : A.Chronological steps
  nextStamp : Nat

private def Replay.initial : Replay := ⟨seed, by decide, [], .nil _, .nil, 0⟩

private def Replay.append (before : Replay) (event : A.Event) : Except String Replay := do
  if earlier : before.steps.all (fun step => decide (step.stamp < before.nextStamp)) = true then
    let step := TCP.ApplicationTrace.Step.make before.current before.valid event before.nextStamp
    have prior : ∀ previous ∈ before.steps, previous.stamp < step.stamp := by
      change ∀ previous ∈ before.steps, previous.stamp < before.nextStamp
      simpa only [List.all_eq_true, decide_eq_true_eq] using earlier
    return ⟨step.result.state, step.valid, before.steps ++ [step], before.chain.snoc,
      TCP.ApplicationTrace.chronological_snoc before.ordered prior, before.nextStamp + 1⟩
  else throw "The focused endpoint replay has inconsistent ordinal stamps."

private def Replay.assure (replay : Replay) : Except String (TCP.AckTrace.Assurance seed replay.steps replay.current) :=
  TCP.AckTrace.assure replay.chain replay.ordered rfl

private def Replay.reaction (replay : Replay) : IO TCP.AckReaction.State :=
  match replay.current.ackReaction with
  | none => throw (IO.userError "The replay did not enable ACK scheduling.")
  | some state => pure state

private def packet (sequence count start : Nat) : IO TCP.EstablishedReceive.Input := do
  let peer : TCP.EstablishedReceive.State :=
    ⟨TCP.Output.reverse tuple, TCP.Seq.ofNat 200, 4096, [], TCP.Seq.ofNat 100, TCP.Seq.ofNat 100, []⟩
  let payload := (List.range count).map (fun index => UInt8.ofNat ((start + index) % 251))
  load (TCP.Output.emitAt peer (TCP.Seq.ofNat sequence) payload)

private def base : IO Replay := do
  let recovery ← load (Replay.initial.append .enableRecovery)
  let enabled ← load (recovery.append .enableAck)
  load (enabled.append (.advanceClock 100))

private theorem selected_response {replay : Replay}
    (value : TCP.AckTrace.Assurance seed replay.steps replay.current) (issuer : A.Step)
    (member : issuer ∈ replay.steps) (demand : TCP.AckReaction.Demand) (delay : Nat)
    (requested : TCP.AckTrace.request issuer.before issuer.event issuer.result = some (demand, delay)) :
    let cause := Theory.TimedReaction.fresh (TCP.AckTrace.work issuer.before) issuer.before.now demand delay
    ∃ completion, ∃ response : TCP.AckTrace.Causal replay.steps completion cause,
      response.issuer.stamp < response.response.step.stamp ∧
      response.response.step.before.now - response.issuer.before.now < 500 ∧
      cause.demand.cursor.add (completion.output.position - cause.demand.position) =
        response.response.output.packet.segment.acknowledgment := by
  obtain ⟨completion, _, _, ⟨response⟩⟩ := value.issued_response issuer member demand delay requested
  exact ⟨completion, response, response.strict_earlier value.ordered, response.strict_delay, response.sequence_coverage.2⟩

private def auditIssuer {replay : Replay} (value : TCP.AckTrace.Assurance seed replay.steps replay.current) (stamp : Nat) : IO Unit := do
  match found : replay.steps.find? (fun step => decide (step.stamp = stamp)) with
  | none => throw (IO.userError "The actual issuer operation is missing.")
  | some issuer =>
    match requested : TCP.AckTrace.request issuer.before issuer.event issuer.result with
    | none => throw (IO.userError "The selected actual operation did not issue an ACK cause.")
    | some (demand, delay) =>
      let _ := value.issued_response issuer (List.mem_of_find?_eq_some found) demand delay requested
      let _ := TCP.AckTrace.request_source issuer demand delay requested
      let _ := selected_response value issuer (List.mem_of_find?_eq_some found) demand delay requested
      match event : issuer.event with
      | .read count =>
        let _ := TCP.AckTrace.read_source issuer count event demand delay requested
        pure ()
      | _ => pure ()
      pure ()

private def auditCompletions {replay : Replay} (value : TCP.AckTrace.Assurance seed replay.steps replay.current) : IO Unit := do
  for completion in (TCP.AckTrace.work replay.current).completed do
    for cause in completion.causes do
      unless cause.issuedAt ≤ completion.time && completion.time ≤ cause.due &&
          TCP.AckReaction.covers cause.demand completion.output do
        throw (IO.userError "An actual completion lost time or cursor coverage.")
  let _ := value.history
  pure ()

private def piggyback : IO Unit := do
  let first ← load ((← base).append (.receive (← packet 100 400 17)))
  let clock ← load (first.append (.advanceClock 200))
  let second ← load (clock.append (.receive (← packet 500 400 33)))
  let pending ← second.reaction
  ensure (pending.credit == 2 && pending.due == some 599 && pending.rmss == 1200 &&
      second.current.effectiveMSS == 800 && pending.advertisement.frontier == 800)
    "Actual partial arrivals must coalesce without extending the first deadline or confusing the two MSS values."
  fails second.assure
  let written ← load (second.append (.write [9, 10]))
  let sent ← load (written.append (.send 2 true))
  let value ← load sent.assure
  let reaction ← sent.reaction
  ensure (reaction.credit == 0 && reaction.work.completed.length == 1 &&
      sent.current.core.received.length == 800 &&
      (sent.steps.flatMap TCP.ApplicationTrace.Step.emitted) == [9, 10])
    "The actual new data output must discharge both causes without duplicating stream bytes."
  let output ← load (TCP.ApplicationTrace.findOutput sent.steps 7)
  ensure (output.val.output.packet.segment.acknowledgment == TCP.Seq.ofNat 900 &&
      output.val.output.packet.segment.window.val == 3296 && output.val.output.packet.segment.payload == [9, 10])
    "The checked piggyback packet must carry the current cumulative ACK and actual advertised window."
  auditIssuer value 3
  auditIssuer value 5
  auditCompletions value
  let extra ← load (sent.append (.emitAck true))
  let some last := extra.steps.getLast? | throw (IO.userError "The extra ACK operation is missing.")
  ensure (last.result.decision == .reject (.ack .noCredit) && last.result.output.isNone)
    "A pure ACK must not reuse already discharged input credit."
  let small ← load (sent.append (.read 799))
  ensure ((← small.reaction).credit == 0 && TCP.Endpoint.outputWindow small.current == 3296)
    "A read below the selected SWS threshold must not grant credit or expose a small window advance."
  let reopened ← load (small.append (.read 1))
  ensure ((← reopened.reaction).credit == 1 && TCP.Endpoint.outputWindow reopened.current == 4096)
    "Actual accumulated consumption must reach the outgoing-MSS SWS threshold before it grants window credit."
  fails reopened.assure
  let updated ← load (reopened.append (.dispatchAck true))
  let windowValue ← load updated.assure
  auditIssuer windowValue 9
  auditCompletions windowValue
  let windowOutput ← load (TCP.ApplicationTrace.findOutput updated.steps 10)
  ensure (windowOutput.val.output.packet.segment.acknowledgment == TCP.Seq.ofNat 900 &&
      windowOutput.val.output.packet.segment.window.val == 4096)
    "The read-origin response must carry the actual reopened window and current ACK."

private def boundaryAndDenial : IO Unit := do
  let received ← load ((← base).append (.receive (← packet 100 400 17)))
  let early ← load ((← load (received.append (.advanceClock 598))).append (.dispatchAck true))
  let some attempt := early.steps.getLast? | throw (IO.userError "The early dispatch is missing.")
  ensure (attempt.result.decision == .reject (.ack .early) && attempt.result.output.isNone)
    "A dispatcher before its due time must retain the pending response."
  fails early.assure
  let due ← load (received.append (.advanceClock 599))
  let denied ← load (due.append (.dispatchAck false))
  ensure ((← denied.reaction).credit == 1) "Local denial must retain actual cause credit."
  fails denied.assure
  let emitted ← load (denied.append (.dispatchAck true))
  let value ← load emitted.assure
  auditIssuer value 3
  auditCompletions value
  let output ← load (TCP.ApplicationTrace.findOutput emitted.steps 6)
  ensure (output.val.step.before.now == 599 && output.val.output.packet.segment.acknowledgment == TCP.Seq.ofNat 500)
    "An actual output after 499 milliseconds must meet the strict ACK bound."
  let late ← load (received.append (.advanceClock 600))
  let some jump := late.steps.getLast? | throw (IO.userError "The forbidden clock jump is missing.")
  ensure (jump.result.decision == .ackUnsupported .deadline) "The clock jump must stop the selected timed scope."
  fails late.assure

private def oldDuplicate : IO Unit := do
  let data ← packet 100 400 17
  let received ← load ((← base).append (.receive data))
  let duplicate ← load (received.append (.receive data))
  let pending ← duplicate.reaction
  ensure (duplicate.current.core.received.length == 400 && pending.credit == 2 && pending.due == some 100)
    "A wholly old duplicate must request an immediate ACK without a second byte delivery."
  let emitted ← load (duplicate.append (.dispatchAck true))
  let value ← load emitted.assure
  auditIssuer value 3
  auditIssuer value 4
  auditCompletions value

def run : IO Unit := do
  piggyback
  boundaryAndDenial
  oldDuplicate
  IO.println "Checked TCP ACK trace tests passed."

end NetlibTest.TCPAckTrace

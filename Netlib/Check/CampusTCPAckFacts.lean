import Netlib.Check.CampusTCPFacts
import Netlib.Protocol.TCP.AckTrace

/-!
# Local ACK generation on the actual campus replay

Each endpoint keeps its own clock and checked startup offer.
Receive causes retain the existing gateway delivery evidence.
Local output does not imply later delivery through a gateway.
-/

namespace Netlib.Check.CampusTCPAckFacts

open Protocol
namespace M
export Check.CampusTCPModel (Actor Cursor Report)
end M
namespace A
export TCP.ApplicationTrace (Step Event)
end A
namespace R
export TCP.AckTrace (work adapter checkSteps checkSteps_history Assurance Causal)
end R

private theorem step_eq (first second : A.Step) (before : first.before = second.before)
    (event : first.event = second.event) (stamp : first.stamp = second.stamp) : first = second := by
  cases first with
  | mk firstBefore firstEvent firstResult firstStamp firstValid firstComputed =>
    cases second with
    | mk secondBefore secondEvent secondResult secondStamp secondValid secondComputed =>
      dsimp only at before event stamp
      subst secondBefore
      subst secondEvent
      subst secondStamp
      cases firstComputed
      cases secondComputed
      rfl

structure Selected (steps : List A.Step) where
  prior : List A.Step
  step : A.Step
  later : List A.Step
  split : steps = prior ++ step :: later
  accepted : step.result.decision = .accepted .enableAck

def select : (steps : List A.Step) → Except String (Selected steps)
  | [] => .error "The endpoint has no accepted ACK activation."
  | head :: tail => do
    if accepted : head.result.decision = .accepted .enableAck then
      return ⟨[], head, tail, rfl, accepted⟩
    else
      let rest ← select tail
      return ⟨head :: rest.prior, rest.step, rest.later, by simp only [rest.split, List.cons_append], rest.accepted⟩

def beforeTransport (steps : List A.Step) : Bool :=
  steps.all fun step => match step.event with | .send .. | .receive .. => false | _ => true

structure Activation (report : M.Report input events) (actor : M.Actor) (steps : List A.Step) where
  selected : Selected steps
  event : selected.step.event = .enableAck
  disabled : selected.step.before.ackReaction = none
  early : beforeTransport selected.prior = true
  joint : CampusTCPFacts.At report selected.step.stamp
  actual : joint.step.event = .enableAck actor
  applied : joint.step.result.application = some (actor, selected.step)
  initialized : selected.step.result.state.ackReaction = some (TCP.AckReaction.initial
    selected.step.before.core.receiveNext selected.step.before.core.capacity selected.step.before.localReceiveMSS.limit)

def activation (report : M.Report input events) (actor : M.Actor) (steps : List A.Step) :
    Except String (Activation report actor steps) := do
  let selected ← select steps
  match event : selected.step.event with
  | .enableAck =>
    if disabled : selected.step.before.ackReaction = none then
      if early : beforeTransport selected.prior = true then
        let joint ← CampusTCPFacts.findStep report selected.step.stamp
        match actual : joint.step.event, applied : joint.step.result.application with
        | .enableAck actualActor, some (appliedActor, appliedStep) =>
          if actorEq : actualActor = actor then
            if appliedActorEq : appliedActor = actor then
              if before : appliedStep.before = selected.step.before then
                match appliedEvent : appliedStep.event with
                | .enableAck =>
                  if stamp : appliedStep.stamp = selected.step.stamp then
                    have same := step_eq appliedStep selected.step before (appliedEvent.trans event.symm) stamp
                    have accepted : (TCP.Endpoint.enableAck selected.step.before).decision = .accepted .enableAck := by
                      simpa only [selected.step.computed, event, TCP.ApplicationTrace.evaluate] using selected.accepted
                    have initialized := (TCP.Endpoint.enableAck_state _ accepted).1
                    return ⟨selected, event, disabled, early, joint, by simpa only [actorEq] using actual,
                      by simpa only [appliedActorEq, same] using applied,
                      by simpa only [selected.step.computed, event, TCP.ApplicationTrace.evaluate] using initialized⟩
                  else throw "The ACK activation has a different joint stamp."
                | _ => throw "The joint operation is not the selected ACK activation."
              else throw "The ACK activation has a different joint state."
            else throw "The applied ACK activation names a different endpoint."
          else throw "The joint ACK activation names a different endpoint."
        | _, _ => throw "The ACK activation has no actual joint operation."
      else throw "The ACK activation follows a transport operation."
    else throw "The first accepted ACK activation replaced an enabled profile."
  | _ => throw "The accepted ACK activation has a different operation kind."

inductive Mode (report : M.Report input events) (actor : M.Actor) (steps : List A.Step) (final : TCP.Endpoint.State) where
  | disabled (absent : final.ackReaction = none)
  | enabled (present : final.ackReaction.isSome = true) (activation : Activation report actor steps)

structure EndpointEvidence (report : M.Report input events) (actor : M.Actor)
    (seed : TCP.Endpoint.State) (cursor : M.Cursor seed) (offer : TCP.MSS.Offer) where
  started : seed.ackReaction = none
  seedOffer : seed.localReceiveMSS = offer
  finalOffer : cursor.current.localReceiveMSS = offer
  rmss : ∀ reaction, cursor.current.ackReaction = some reaction → reaction.rmss = offer.limit
  mode : Mode report actor cursor.steps cursor.current
  projected : List (TCP.AckTrace.T.CheckedStep R.adapter)
  checked : R.checkSteps cursor.steps = .ok projected
  history : TCP.AckTrace.T.History R.adapter seed projected cursor.current

def endpointEvidence (report : M.Report input events) (actor : M.Actor)
    (seed : TCP.Endpoint.State) (cursor : M.Cursor seed) (offer : TCP.MSS.Offer) :
    Except String (EndpointEvidence report actor seed cursor offer) := do
  if started : seed.ackReaction = none then
    if seedOffer : seed.localReceiveMSS = offer then
      if finalOffer : cursor.current.localReceiveMSS = offer then
        match checked : R.checkSteps cursor.steps with
        | .error reason => throw reason
        | .ok projected =>
          match enabled : cursor.current.ackReaction with
          | none => return ⟨started, seedOffer, finalOffer, (by intro reaction found; rw [enabled] at found; cases found),
              .disabled enabled, projected, checked, R.checkSteps_history cursor.chain projected checked⟩
          | some reaction =>
            if rmss : reaction.rmss = offer.limit then
              let actual ← activation report actor cursor.steps
              return ⟨started, seedOffer, finalOffer, by
                intro next found
                have same := Option.some.inj (enabled.symm.trans found)
                simpa only [← same] using rmss,
                .enabled (by rw [enabled]; rfl) actual, projected, checked,
                R.checkSteps_history cursor.chain projected checked⟩
            else throw "The ACK RMSS differs from the endpoint's checked startup offer."
      else throw "The endpoint changed its own checked receive-MSS offer."
    else throw "The endpoint seed differs from its own checked startup offer."
  else throw "The checked startup already contains an ACK profile."

def EndpointEvidence.timing (value : EndpointEvidence report actor seed cursor offer)
    (enabled : cursor.current.ackReaction.isSome = true) (closed : (R.work cursor.current).pending = []) :
    R.Assurance seed cursor.steps cursor.current :=
  ⟨cursor.chain, cursor.ordered, value.started, enabled, value.projected, value.checked, value.history, closed⟩

structure Evidence (report : M.Report input events) where
  application : CampusTCPFacts.Assurance report
  client : EndpointEvidence report .client application.complete.certificate.activeSeed application.endpoints.client
    (TCP.Handshake.receiveOffer input.active)
  server : EndpointEvidence report .server application.complete.certificate.passiveSeed application.endpoints.server
    (TCP.Handshake.receiveOffer input.passive)

def evidence (report : M.Report input events) : Except String (Evidence report) := do
  let application ← CampusTCPFacts.assure report
  let client ← endpointEvidence report .client _ application.endpoints.client (TCP.Handshake.receiveOffer input.active)
  let server ← endpointEvidence report .server _ application.endpoints.server (TCP.Handshake.receiveOffer input.passive)
  return ⟨application, client, server⟩

structure Assurance (report : M.Report input events) extends Evidence report where
  clientClosed : (R.work application.endpoints.client.current).pending = []
  serverClosed : (R.work application.endpoints.server.current).pending = []

def assure (value : Evidence report) : Except String (Assurance report) := do
  if clientClosed : (R.work value.application.endpoints.client.current).pending = [] then
    if serverClosed : (R.work value.application.endpoints.server.current).pending = [] then
      return ⟨value, clientClosed, serverClosed⟩
    else throw "The server has unresolved ACK causes."
  else throw "The client has unresolved ACK causes."

theorem receive_cause_delivery (history : CampusTCPFacts.Receives report peer actor steps)
    (step : A.Step) (member : step ∈ steps) (packet : TCP.EstablishedReceive.Input)
    (received : step.event = .receive packet) :
    Nonempty (CampusTCPFacts.ApplicationDelivery report peer actor step) :=
  history.application_delivery step member packet received

structure CampusCausal (report : M.Report input events) (peer : List A.Step) (actor : M.Actor)
    (steps : List A.Step) (completion : Netlib.Theory.TimedReaction.Discharge Unit TCP.AckReaction.Demand TCP.AckReaction.Acknowledgment)
    (cause : Netlib.Theory.TimedReaction.Cause Unit TCP.AckReaction.Demand) where
  causal : R.Causal steps completion cause
  source : (∃ packet, causal.issuer.event = .receive packet ∧
      Nonempty (CampusTCPFacts.ApplicationDelivery report peer actor causal.issuer)) ∨
    (∃ count, causal.issuer.event = .read count ∧ cause.demand.kind = .window)

theorem campus_causal (history : CampusTCPFacts.Receives report peer actor steps)
    (causal : R.Causal steps completion cause) : Nonempty (CampusCausal report peer actor steps completion cause) := by
  refine ⟨⟨causal, ?_⟩⟩
  rcases TCP.AckTrace.request_source causal.issuer cause.demand causal.delay causal.request with received | read
  · obtain ⟨packet, event, _, _⟩ := received
    exact .inl ⟨packet, event, receive_cause_delivery history causal.issuer causal.issuerMember packet event⟩
  · exact .inr read

theorem Assurance.client_causal (value : Assurance report)
    (enabled : value.application.endpoints.client.current.ackReaction.isSome = true)
    (completion : Netlib.Theory.TimedReaction.Discharge Unit TCP.AckReaction.Demand TCP.AckReaction.Acknowledgment)
    (completed : completion ∈ (R.work value.application.endpoints.client.current).completed)
    (cause : Netlib.Theory.TimedReaction.Cause Unit TCP.AckReaction.Demand) (member : cause ∈ completion.causes) :
    Nonempty (CampusCausal report value.application.endpoints.server.steps .client
      value.application.endpoints.client.steps completion cause) := by
  obtain ⟨causal⟩ := (value.client.timing enabled value.clientClosed).causal completion completed cause member
  exact campus_causal value.application.clientReceives causal

theorem Assurance.server_causal (value : Assurance report)
    (enabled : value.application.endpoints.server.current.ackReaction.isSome = true)
    (completion : Netlib.Theory.TimedReaction.Discharge Unit TCP.AckReaction.Demand TCP.AckReaction.Acknowledgment)
    (completed : completion ∈ (R.work value.application.endpoints.server.current).completed)
    (cause : Netlib.Theory.TimedReaction.Cause Unit TCP.AckReaction.Demand) (member : cause ∈ completion.causes) :
    Nonempty (CampusCausal report value.application.endpoints.client.steps .server
      value.application.endpoints.server.steps completion cause) := by
  obtain ⟨causal⟩ := (value.server.timing enabled value.serverClosed).causal completion completed cause member
  exact campus_causal value.application.serverReceives causal

theorem Assurance.client_issued_response (value : Assurance report)
    (enabled : value.application.endpoints.client.current.ackReaction.isSome = true)
    (issuer : A.Step) (member : issuer ∈ value.application.endpoints.client.steps)
    (demand : TCP.AckReaction.Demand) (delay : Nat)
    (requested : TCP.AckTrace.request issuer.before issuer.event issuer.result = some (demand, delay)) :
    let cause := Netlib.Theory.TimedReaction.fresh (R.work issuer.before) issuer.before.now demand delay
    ∃ completion ∈ (R.work value.application.endpoints.client.current).completed,
      cause ∈ completion.causes ∧ Nonempty (CampusCausal report value.application.endpoints.server.steps
        .client value.application.endpoints.client.steps completion cause) := by
  obtain ⟨completion, completed, covered, causal⟩ :=
    (value.client.timing enabled value.clientClosed).issued_response issuer member demand delay requested
  obtain ⟨causal⟩ := causal
  exact ⟨completion, completed, covered, campus_causal value.application.clientReceives causal⟩

theorem Assurance.server_issued_response (value : Assurance report)
    (enabled : value.application.endpoints.server.current.ackReaction.isSome = true)
    (issuer : A.Step) (member : issuer ∈ value.application.endpoints.server.steps)
    (demand : TCP.AckReaction.Demand) (delay : Nat)
    (requested : TCP.AckTrace.request issuer.before issuer.event issuer.result = some (demand, delay)) :
    let cause := Netlib.Theory.TimedReaction.fresh (R.work issuer.before) issuer.before.now demand delay
    ∃ completion ∈ (R.work value.application.endpoints.server.current).completed,
      cause ∈ completion.causes ∧ Nonempty (CampusCausal report value.application.endpoints.client.steps
        .server value.application.endpoints.server.steps completion cause) := by
  obtain ⟨completion, completed, covered, causal⟩ :=
    (value.server.timing enabled value.serverClosed).issued_response issuer member demand delay requested
  obtain ⟨causal⟩ := causal
  exact ⟨completion, completed, covered, campus_causal value.application.serverReceives causal⟩

theorem Assurance.application_prefix (value : Assurance report) :
    value.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.written ∧
      value.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.written :=
  value.application.application_prefix

end Netlib.Check.CampusTCPAckFacts

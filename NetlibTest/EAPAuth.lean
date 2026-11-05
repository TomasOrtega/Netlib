import Netlib.Protocol.EAPAuth

namespace NetlibTest.EAPAuth

open Netlib.Protocol.EAPAuth

private def context : Context := ⟨"client@example.test", 13⟩
private def anonymous : List UInt8 := [97, 110, 111, 110, 121, 109, 111, 117, 115]
private def evidence (round : Nat := 1) : Evidence :=
  ⟨round, context.subject, 13, true, some "external certificate and method verification"⟩

private def fragments : List Event := [
  .start,
  .server (.request 1 1 []), .peer (.response 1 1 anonymous),
  .server (.request 2 13 [0x20]), .peer (.response 2 13 [0xc0, 0, 0, 1, 0, 0x16]),
  .server (.request 2 13 [0x20]), .peer (.response 2 13 [0xc0, 0, 0, 1, 0, 0x16]),
  .server (.request 3 13 [0]), .peer (.response 2 13 [0xc0, 0, 0, 1, 0, 0x16]),
  .peer (.response 3 13 [0x40, 0x16]),
  .server (.request 4 13 [0xc0, 0, 0, 2, 0, 0x16]), .peer (.response 4 13 [0]),
  .server (.request 5 13 [0x40, 0x16]), .peer (.response 5 13 [0]),
  .server (.request 6 13 [0, 0x16]), .peer (.response 6 13 [0, 0x16]),
  .server (.request 7 13 [0, 0x17]), .peer (.response 7 13 [0])]

private def awaiting : State := {
  round := 1
  latestRequest := some ⟨7, 13, [0, 0x17]⟩
  latestResponse := some ⟨7, 13, [0]⟩
  outerIdentity := some anonymous }
private def succeeded : State := step context awaiting (.server (.success 7))
private def authenticated : State := step context succeeded (.method (evidence 1))

example : awaiting.round = 1 ∧ awaiting.authorized = false ∧ awaiting.outerIdentity = some anonymous := by decide
example : succeeded.authorized = false := by decide
example : authenticated.authorized = true := by decide
example : (step context awaiting (.method (evidence 1))).authorized = false := by decide
example : (step context (step context awaiting (.method (evidence 1))) (.server (.success 7))).authorized = true := by decide

example : (step context awaiting (.server (.success 6))) = awaiting := by rfl
example : (step context awaiting (.peer (.success 7))) = awaiting := by rfl
example : step context awaiting (.peer (.response 7 1 anonymous)) = awaiting := by rfl
example : step context authenticated (.server (.request 7 13 [0, 0x17])) = authenticated := by rfl
example : step context authenticated (.peer (.response 7 13 [0])) = authenticated := by rfl
example : step context authenticated (.server (.success 7)) = authenticated := by rfl
example : step context authenticated (.server (.request 7 13 [0x20])) = authenticated := by rfl

example : (step context authenticated (.server (.request 8 13 [0x20]))).round = 2 := by decide
example : (step context authenticated (.server (.request 8 13 [0x20]))).authorized = false := by decide
example : (step context authenticated (.server (.failure 7))).round = 2 := by decide
example : step context authenticated (.server (.failure 6)) = authenticated := by rfl

private def identityOnly : State := run context State.initial [
  .start, .server (.request 1 1 []), .peer (.response 1 1 anonymous),
  .method (evidence 1), .server (.success 1)]

example : identityOnly.authorized = false := by decide
example : (run ⟨"anonymous@example.test", 1⟩ State.initial [
    .start, .server (.request 1 1 []), .peer (.response 1 1 anonymous),
    .method ⟨1, "anonymous@example.test", 1, true, none⟩, .server (.success 1)]).authorized = false := by decide

example : authenticated.Safe context :=
  step_safe context succeeded (.method (evidence 1))
    (step_safe context awaiting (.server (.success 7)) (by intro impossible; cases impossible))

example : (run context State.initial fragments).Safe context := run_safe context _ fragments (initial_safe context)

example (state : State) (safe : state.Safe context) (authorized : state.authorized = true) :
    ∃ verified, state.evidence = some verified ∧ verified.ValidFor context state.round :=
  authorized_evidence context state safe authorized

example (state : State) (verified : Evidence) (old : verified.round = state.round) :
    (step context state.reset (.method verified)).authorized = false := old_evidence_after_reset context state verified old

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  ensure (Netlib.Protocol.EAPAuth.run context State.initial fragments == awaiting)
    "Fragmented method exchanges and retransmissions must retain the final correlated response."
  ensure (!awaiting.authorized && awaiting.round == 1 && awaiting.outerIdentity == some anonymous)
    "Opaque TLS fragments and an anonymous outer identity must not authorize a principal."
  ensure (!succeeded.authorized && authenticated.authorized && authenticated.outerIdentity == some anonymous)
    "Matched EAP Success requires independent current method evidence for the expected subject."
  let early := step context awaiting (.method (evidence 1))
  ensure (!early.authorized && (step context early (.server (.success 7))).authorized)
    "Trusted completion evidence may precede the matching terminal packet."
  for wrong in [
    { evidence 1 with round := 0 }, { evidence 1 with subject := "anonymous@example.test" },
    { evidence 1 with method := 21 }
  ] do
    ensure (!(step context succeeded (.method wrong)).authorized)
      "Wrong round, subject, or selected method must not satisfy the evidence guard."
  ensure (!identityOnly.authorized && !(step context State.initial (.server (.success 1))).authorized)
    "Outer Identity and a canned Success must not establish authentication."
  let pending := step context State.initial (.server (.request 9 13 [0x20]))
  ensure (step context pending (.peer (.response 8 13 [0])) == pending &&
    step context pending (.peer (.response 9 1 anonymous)) == pending &&
    step context pending (.server (.response 9 13 [0])) == pending)
    "Wrong response identifier, type, or role must not advance the exchange."
  for duplicate in [
    Event.server (.request 7 13 [0, 0x17]), .peer (.response 7 13 [0]),
    .server (.success 7), .method (evidence 1)
  ] do
    ensure (step context authenticated duplicate == authenticated)
      "Harmless retransmissions must preserve the authorized round and its evidence."
  let changed := step context authenticated (.server (.request 8 13 [0x20]))
  ensure (!changed.authorized && changed.round == 2 && changed.evidence.isNone && changed.outerIdentity.isNone)
    "A new conversation after Success must clear the prior local authorization."
  let next := Netlib.Protocol.EAPAuth.run context changed [
    .peer (.response 8 13 [0]), .server (.success 8), .method (evidence 1)]
  ensure (!next.authorized && next.round == 2 && (step context next (.method (evidence 2))).authorized)
    "Stale accepted evidence must not authorize a later completed round."
  for reset in [Event.begin, .restart, .start, .logoff, .disconnect] do
    let cleared := step context authenticated reset
    ensure (!cleared.authorized && cleared.round == 2 && cleared.latestRequest.isNone &&
      cleared.latestResponse.isNone && cleared.success.isNone && cleared.evidence.isNone)
      "Each local reset must clear authorization, evidence, and transaction correlation."
    ensure (!(step context cleared (.method (evidence 1))).authorized &&
      !(step context cleared (.server (.success 7))).authorized)
      "Old evidence and terminal packets must not reopen a reset conversation."
  let failed := step context authenticated (.server (.failure 7))
  ensure (!failed.authorized && failed.round == 2 &&
    !(step context failed (.method (evidence 1))).authorized)
    "A matching Failure must close the local round and reject stale evidence."
  let rejected := step context authenticated (.method { evidence 1 with accepted := false })
  ensure (!rejected.authorized && rejected.round == 2 && rejected.evidence.isNone &&
    !(step context rejected (.method (evidence 1))).authorized)
    "A trusted negative result must fail closed before a stale positive result arrives."
  for method in [0, 1, 2, 3, 254, 255] do
    let selected : Context := ⟨context.subject, method⟩
    let attempt := Netlib.Protocol.EAPAuth.run selected State.initial [
      .server (.request 1 method []), .peer (.response 1 method []),
      .method ⟨0, context.subject, method, true, none⟩, .server (.success 1)]
    ensure (!attempt.authorized) "Control and expanded types must not become selected basic authentication methods."
  IO.println "EAP authentication guard tests passed."

end NetlibTest.EAPAuth

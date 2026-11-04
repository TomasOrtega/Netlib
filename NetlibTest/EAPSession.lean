import Netlib.Protocol.EAPSession

namespace NetlibTest.EAPSession

open Netlib.Protocol
open Netlib.Protocol.EAPSession

private def context : Context := ⟨"verified-client", "application-server", "token-authority"⟩
private def scope : Scope := ⟨"orders", "read"⟩
private def anonymous : List UInt8 := [97, 110, 111, 110, 121, 109, 111, 117, 115]
private def token : Credential := ⟨context.issuer, context.consumer, context.producer, [scope], 100, true⟩
private def verified (round : Nat := 1) : EAPAuth.Evidence := ⟨round, context.consumer, 13, true, some "trusted method result"⟩
private def authentication : List EAPSession.Event := [
  .authentication .start,
  .authentication (.server (.request 1 1 [])), .authentication (.peer (.response 1 1 anonymous)),
  .authentication (.server (.request 2 13 [0x20])), .authentication (.peer (.response 2 13 [0])),
  .authentication (.server (.success 2)), .authentication (.method (verified 1))]
private def admittedEvents : List EAPSession.Event := authentication ++
  [.application (.install token), .application (.advance 5), .application (.request scope)]
private def good : State := Netlib.Protocol.EAPSession.run context State.initial admittedEvents

example : good.auth.authorized = true ∧ good.session.admitted = some scope := by decide
example : good.Safe context := run_safe context _ admittedEvents (initial_safe context)

example (initial : State) (events : List EAPSession.Event) (safe : initial.Safe context)
    (admitted : (Netlib.Protocol.EAPSession.run context initial events).session.admitted = some scope) :
    Session.Valid context (Netlib.Protocol.EAPSession.run context initial events).session scope ∧
      EAPAuth.State.Ready (authContext context) (Netlib.Protocol.EAPSession.run context initial events).auth :=
  admitted_valid context initial events scope safe admitted

example (state : State) (event : ApplicationEvent) :
    (step context state (.application event)).auth = state.auth := rfl

example (state : State) (event : EAPAuth.Event)
    (unchanged : EAPAuth.step (authContext context) state.auth event = state.auth) :
    step context state (.authentication event) = state := by
  simp [step, synchronize, unchanged]

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let raw := Netlib.Protocol.EAPSession.run context State.initial [
    .application (.install token), .authentication (.server (.success 2)), .application (.request scope)]
  ensure (!raw.auth.authorized && !raw.session.authenticated && raw.session.admitted.isNone && raw.session.credential == some token)
    "Raw EAP Success must not activate a valid installed credential."
  let prepared := Netlib.Protocol.EAPSession.run context State.initial [.authentication .start, .application (.install token)]
  let authorized := Netlib.Protocol.EAPSession.run context prepared (authentication.drop 1)
  ensure (authorized.auth.authorized && authorized.session.authenticated &&
    authorized.session.credential.isNone && authorized.session.admitted.isNone)
    "The new EAP authorization must clear a credential installed before authentication completed."
  let noToken := step context authorized (.application (.request scope))
  ensure noToken.session.admitted.isNone "Authorization alone must not satisfy the credential guard."
  ensure (good.auth.authorized && good.session.authenticated && good.session.admitted == some scope &&
    good.session.permits context scope && good.auth.outerIdentity == some anonymous)
    "A fresh credential after accepted method completion must permit the expected subject's application request."
  for duplicate in [
    EAPAuth.Event.server (.request 2 13 [0x20]), .peer (.response 2 13 [0]),
    .server (.success 2), .method (verified 1)
  ] do
    let after := step context good (.authentication duplicate)
    ensure (after.auth == good.auth && after.session == good.session)
      "Harmless EAP retransmissions must preserve the current credential and recorded admission."
  for reset in [EAPAuth.Event.logoff, .disconnect, .restart, .start] do
    let after := step context good (.authentication reset)
    let denied := step context after (.application (.request scope))
    ensure (!after.auth.authorized && !after.session.authenticated && after.auth.round == 2 &&
      after.session.credential.isNone && after.session.admitted.isNone && denied.session.admitted.isNone)
      "A local EAP reset must clear application authentication and its credential."
    let stale := step context after (.authentication (.method (verified 1)))
    ensure (!stale.auth.authorized && !stale.session.authenticated && stale.session.credential.isNone)
      "Stale method evidence must not reopen the application session."
  let renewed := step context good (.authentication (.server (.request 3 13 [0x20])) )
  ensure (!renewed.auth.authorized && renewed.auth.round == 2 && renewed.session.credential.isNone)
    "A new post-success conversation must clear the earlier session."
  let failed := step context good (.authentication (.method { verified 1 with accepted := false }))
  let stale := step context failed (.authentication (.method (verified 1)))
  ensure (!failed.auth.authorized && failed.auth.round == 2 && failed.session.credential.isNone &&
    !stale.auth.authorized && !stale.session.authenticated)
    "A trusted negative result must close the session before stale positive evidence arrives."
  let closed := step context good .close
  ensure (!closed.auth.authorized && !closed.session.authenticated && closed.auth.round == 2 &&
    closed.session.credential.isNone && closed.session.admitted.isNone)
    "Combined close must disconnect EAP and clear application access."
  let expired := Netlib.Protocol.EAPSession.run context good [.application (.advance 100), .application (.request scope)]
  ensure (expired.auth.authorized && expired.session.admitted.isNone)
    "Credential expiration must deny the application independently of EAP authorization."
  let revoked := step context good (.application .revoke)
  ensure (revoked.auth.authorized && revoked.session.credential.isNone && revoked.session.admitted.isNone)
    "Credential revocation must preserve its separate application scope."
  let mut current := State.initial
  for event in admittedEvents ++ [.authentication .logoff, .authentication (.method (verified 1)),
    .application (.install token), .application (.request scope), .close] do
    current := step context current event
    ensure (current.session.authenticated == current.auth.authorized)
      "Every interleaved transition must retain authentication coupling."
  IO.println "EAP session admission tests passed."

end NetlibTest.EAPSession

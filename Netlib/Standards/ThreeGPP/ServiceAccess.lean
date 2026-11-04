import Netlib.Import.Json
import Netlib.Protocol.Session
import Netlib.Standards.Basic

/-!
# Direct NF service access

This profile checks admitted requests in a direct NF-instance trace.
It covers selected token guards from TS 33.501 clause 13.4.1.1.2.
Identity and token integrity results are supplied evidence.
It does not implement TLS, token signatures, or the complete 5G specification.
-/

namespace Netlib.FiveG

open Protocol Standards

def documentUrl : String :=
  "https://www.etsi.org/deliver/etsi_ts/133500_133599/133501/19.05.00_60/ts_133501v190500p.pdf"

def source : Source :=
  ⟨"3GPP TS 33.501", "19.5.0 Release 19", "13.4.1.1.2", documentUrl⟩

def requirement (id statement : String) : Standards.Requirement where
  id
  source
  statement
  applicability := "Admitted direct NF-instance requests with token authorization."
  assumptions := [
    "The trace records every service admission.",
    "Identity results match both authenticated TLS peers.",
    "Integrity results come from a trusted token validator.",
    "The clock and configured issuer identities are correct.",
    "Tokens have no slice, NF-set, service-set, or CCA restrictions."
  ]

inductive TraceEvent where
  | authenticate (success : Bool)
  | token (credential : Credential)
  | tick (now : Nat)
  | request (scope : Scope) (accepted : Bool)
  | close
  deriving Repr, BEq, DecidableEq

def TraceEvent.event : TraceEvent → Protocol.Event
  | .authenticate success => .authenticate success
  | .token credential => .install credential
  | .tick now => .advance now
  | .request scope _ => .request scope
  | .close => .close

structure Trace where
  context : Context
  events : List TraceEvent
  deriving Repr

structure Admission where
  index : Nat
  state : Session
  scope : Scope
  accepted : Bool
  deriving Repr

private def collect (context : Context) (state : Session) (index : Nat) :
    List TraceEvent → List Admission
  | [] => []
  | event :: events =>
    let later := collect context (Session.step context state event.event) (index + 1) events
    match event with
    | .request scope accepted => ⟨index, state, scope, accepted⟩ :: later
    | _ => later

def admissions (trace : Trace) : List Admission :=
  collect trace.context .initial 1 trace.events

def safeAdmissions (context : Context) (attempts : List Admission) : Bool :=
  attempts.all (fun attempt => !attempt.accepted ||
    Session.permits context attempt.state attempt.scope)

theorem safeAdmissions_iff (context : Context) (attempts : List Admission) :
    safeAdmissions context attempts = true ↔
      ∀ attempt ∈ attempts, attempt.accepted = true →
        Session.Valid context attempt.state attempt.scope := by
  simp only [safeAdmissions, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro safe attempt member accepted
    rcases safe attempt member with denied | permitted
    · simp_all
    · exact (Session.permits_iff _ _ _).mp permitted
  · intro safe attempt member
    cases accepted : attempt.accepted with
    | false => exact .inl rfl
    | true => exact .inr ((Session.permits_iff _ _ _).mpr (safe attempt member accepted))

private def status (present passed : Bool) : Status :=
  if !present then .missingEvidence else if passed then .satisfied else .violated

private theorem passed_of_status (present passed : Bool)
    (accepted : status present passed = .satisfied ∨ status present passed = .notApplicable) :
    passed = true := by
  cases present <;> cases passed <;> simp_all [status]

private def evidence (context : Context) (attempt : Admission) : String :=
  s!"Event {attempt.index}, time {attempt.state.now}: " ++
  s!"{attempt.scope.resource}/{attempt.scope.operation}, admitted={attempt.accepted}, " ++
  s!"guard={Session.permits context attempt.state attempt.scope}."

def admissionFinding (trace : Trace) : Finding :=
  let attempts := admissions trace
  { requirement := requirement "5G-ADMISSION" "Every admitted request passes all selected token guards."
    status := status (!attempts.isEmpty) (safeAdmissions trace.context attempts)
    evidence := attempts.map (evidence trace.context) }

private def tokenTest (attempt : Admission) (test : Credential → Bool) : Bool :=
  ((attempt.state.credential).map test).getD false

private def finding (trace : Trace) (id statement : String)
    (guard : Admission → Bool) : Finding :=
  let attempts := admissions trace
  { requirement := requirement id statement
    status := status (!attempts.isEmpty)
      (attempts.all (fun attempt => !attempt.accepted || guard attempt))
    evidence := attempts.map (fun attempt =>
      s!"Event {attempt.index}: admitted={attempt.accepted}, selected guard={guard attempt}.") }

def check (trace : Trace) : Report where
  profile := "5G direct NF-instance token admission profile"
  findings := admissionFinding trace :: [
    finding trace "5G-MUTUAL-AUTH" "Both peers pass the identity check before service admission."
      (fun attempt => attempt.state.authenticated),
    finding trace "5G-TOKEN" "An admitted request has an access token."
      (fun attempt => attempt.state.credential.isSome),
    finding trace "5G-ISSUER" "The token issuer matches the configured authorization server."
      (fun attempt => tokenTest attempt (fun token => decide (token.issuer = trace.context.issuer))),
    finding trace "5G-INTEGRITY" "The token passes the supplied integrity check."
      (fun attempt => tokenTest attempt (·.integrity)),
    finding trace "5G-SUBJECT" "The token subject matches the authenticated consumer."
      (fun attempt => tokenTest attempt (fun token => decide (token.subject = trace.context.consumer))),
    finding trace "5G-AUDIENCE" "The token audience matches the selected producer instance."
      (fun attempt => tokenTest attempt (fun token => decide (token.audience = trace.context.producer))),
    finding trace "5G-SCOPE" "The token scope includes the requested resource and operation."
      (fun attempt => tokenTest attempt (fun token => decide (attempt.scope ∈ token.scopes))),
    finding trace "5G-EXPIRATION" "An admitted request uses a token before its expiration time."
      (fun attempt => tokenTest attempt (fun token => decide (attempt.state.now < token.expiresAt)))
  ]

/-- A passing profile cannot contain an unsafe observed admission. -/
theorem check_compliant_safe (trace : Trace) (passed : (check trace).compliant = true) :
    ∀ attempt ∈ admissions trace, attempt.accepted = true →
      Session.Valid trace.context attempt.state attempt.scope := by
  have head := Report.compliant_status (check trace) passed (admissionFinding trace)
    (by simp [check])
  have safe : safeAdmissions trace.context (admissions trace) = true := by
    apply passed_of_status (!((admissions trace).isEmpty)) _
    exact head
  exact (safeAdmissions_iff _ _).mp safe

/-- Coverage records the evidence that this selected profile does not provide. -/
def coverage : Report where
  profile := "5G profile evidence boundaries"
  findings := [
    { requirement := requirement "5G-CRYPTO-EVIDENCE" "Establish that the integrity verifier is correct."
      status := .missingEvidence
      evidence := ["The trace supplies validator results. Netlib does not validate token signatures."] },
    { requirement := requirement "5G-IDENTITY-EVIDENCE" "Establish the relation between trace identities and TLS peer identities."
      status := .missingEvidence
      evidence := ["The trace supplies identity results. Netlib does not inspect TLS certificates."] },
    { requirement := requirement "5G-OPTIONAL-CLAIMS" "Check optional slice, NF-set, service-set, and CCA restrictions."
      status := .unsupported
      evidence := ["These claim forms are outside this direct NF-instance profile."] }
  ]

private def ensure (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def fields (value : Lean.Json) (names : List String) : Except String Unit := do
  let object ← value.getObj?
  for (name, _) in object.toList do
    ensure (names.contains name) s!"Unknown JSON field: {name}."
  for name in names do
    let _ ← value.getObjVal? name

private def string (value : Lean.Json) (name : String) : Except String String := do
  let result ← (← value.getObjVal? name).getStr?
  ensure (!result.isEmpty && result.toList.all
    (fun ch => ch.isAlphanum || ch == '_' || ch == '-' || ch == '.'))
    s!"Use a nonempty identifier for {name}."
  return result

private def boolean (value : Lean.Json) (name : String) : Except String Bool := do
  (← value.getObjVal? name).getBool?

private def natural (value : Lean.Json) (name : String) : Except String Nat := do
  (← value.getObjVal? name).getNat?

private def scopeFromJson (value : Lean.Json) : Except String Scope := do
  fields value ["resource", "operation"]
  return ⟨← string value "resource", ← string value "operation"⟩

private def credentialFromJson (value : Lean.Json) : Except String Credential := do
  fields value ["issuer", "subject", "audience", "scopes", "expiresAt", "integrity"]
  let scopes ← (← value.getObjVal? "scopes").getArr?
  let scopes ← scopes.toList.mapM scopeFromJson
  ensure (!scopes.isEmpty) "A token must declare its scope."
  return ⟨← string value "issuer", ← string value "subject", ← string value "audience",
    scopes, ← natural value "expiresAt", ← boolean value "integrity"⟩

private def eventFromJson (value : Lean.Json) : Except String TraceEvent := do
  let kind ← string value "type"
  match kind with
  | "authenticate" =>
    fields value ["type", "mutual"]
    return .authenticate (← boolean value "mutual")
  | "token" =>
    fields value ["type", "credential"]
    return .token (← credentialFromJson (← value.getObjVal? "credential"))
  | "tick" =>
    fields value ["type", "now"]
    return .tick (← natural value "now")
  | "request" =>
    fields value ["type", "resource", "operation", "accepted"]
    return .request ⟨← string value "resource", ← string value "operation"⟩
      (← boolean value "accepted")
  | "close" =>
    fields value ["type"]
    return .close
  | _ => throw s!"Unsupported 5G trace event: {kind}."

def fromJson (value : Lean.Json) : Except String Trace := do
  fields value ["schema", "mode", "consumer", "producer", "issuer", "events"]
  ensure ((← natural value "schema") == 1) "Use trace schema 1."
  let mode ← (← value.getObjVal? "mode").getStr?
  ensure (mode == "direct-nf-instance") "Use the direct-nf-instance profile."
  let context := Context.mk (← string value "consumer") (← string value "producer")
    (← string value "issuer")
  let events ← (← value.getObjVal? "events").getArr?
  let events ← events.toList.mapM eventFromJson
  ensure (!events.isEmpty) "Supply a nonempty trace."
  ensure (events.any (fun event => match event with | .request .. => true | _ => false))
    "Supply at least one observed service request."
  let mut now := 0
  for event in events do
    if let .tick time := event then
      ensure (now ≤ time) "Trace time must not move backward."
      now := time
  return ⟨context, events⟩

def parse (text : String) : Except String Trace := do
  fromJson (← Netlib.Import.Json.parse text)

def run (text : String) : Except String Report := do
  return check (← parse text)

def render := Standards.Report.render
def renderJson := Standards.Report.renderJson

end Netlib.FiveG

import Netlib.Compile.SessionFirewall
import Netlib.Check.StatefulRefinement

namespace NetlibTest.SessionFirewall

open Netlib Packet Protocol Compile.SessionFirewall

private def context : Context := ⟨"alice", "reports-application", "campus-authority"⟩
private def readScope : Scope := ⟨"reports", "read"⟩
private def adminScope : Scope := ⟨"reports", "admin"⟩

private def web : Match := {
  source := some ⟨3221225986, 32⟩
  destination := some ⟨3325256714, 32⟩
  protocol := some Packet.Protocol.tcp
  destinationPorts := some (PortRange.single 443) }

private def admin : Match := { web with destinationPorts := some (PortRange.single 8443) }

private def requirements : List Intent := [⟨"REPORTS-READ", readScope, web⟩, ⟨"REPORTS-ADMIN", adminScope, admin⟩]
private def webHeader : Header := ⟨3221225986, 3325256714, Packet.Protocol.tcp, 50000, 443⟩
private def adminHeader : Header := { webHeader with destinationPort := 8443 }
private def states : List StatefulACL.CTState := [.new, .established, .related, .invalid, .untracked]

private def authenticated : EAPSession.State := EAPSession.run context EAPSession.State.initial [
  .authentication .begin,
  .authentication (.server (.request 7 13 [32])),
  .authentication (.peer (.response 7 13 [0])),
  .authentication (.server (.success 7)),
  .authentication (.method ⟨1, "alice", 13, true, some "SYNTHETIC method result"⟩)]

private def token : Credential := ⟨"campus-authority", "alice", "reports-application", [readScope], 100, true⟩
private def active : EAPSession.State := EAPSession.step context authenticated (.application (.install token))

example (compiled : Certified context state requirements) (safe : state.Safe context) (header : Header)
    (allowed : compiled.snapshot.permits header = true) :
    ∃ requirement ∈ requirements, requirement.test.Holds header ∧
      Session.Valid context state.session requirement.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext context) state.auth :=
  compiled.permitted_valid safe header allowed

example (compiled : Certified context state requirements) (requirement : Intent) (member : requirement ∈ requirements)
    (denied : state.session.permits context requirement.scope = false) (header : Header)
    (matched : requirement.test.Holds header) : compiled.snapshot.permits header = false :=
  compiled.denied_requirement requirement member denied header matched

example (compiled : Certified context state requirements) (ctstate : StatefulACL.CTState) (header : Header) :
    compiled.statefulSnapshot.permits ctstate header = compiled.snapshot.permits header :=
  compiled.statefulSnapshot_permits ctstate header

example (compiled : Certified context state requirements) (fallback : Action) (ctstate : StatefulACL.CTState)
    (header : Header) : StatefulACL.Policy.evaluate fallback compiled.statefulSnapshot.compile ctstate header =
      compiled.snapshot.evaluate header := compiled.statefulSnapshot_evaluate fallback ctstate header

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def build (state : EAPSession.State) (requirements : List Intent) (budget : Nat := 100000) :
    IO (Certified context state requirements) :=
  match compile context state requirements budget with
  | .ok compiled => pure compiled
  | .error error => throw (IO.userError error.describe)

private def parse (json : Lean.Json) : IO Import.NftablesStateful.Snapshot :=
  match Import.NftablesStateful.Snapshot.parse json.pretty with
  | .ok snapshot => pure snapshot
  | .error error => throw (IO.userError error)

private def checkRoundtrip (compiled : Certified context state requirements) : IO Unit := do
  let parsed ← parse compiled.toJson
  ensure (parsed.hook == "forward" && parsed.priority == compiled.statefulSnapshot.priority &&
      compiled.statefulSnapshot.hook == "forward" && compiled.statefulSnapshot.priority == 0 &&
      compiled.statefulSnapshot.rules.all (fun rule => rule.states.isNone))
    "Session policy must retain its forward context without a conntrack-state exception."
  ensure (Check.StatefulRefinement.check parsed compiled.statefulSnapshot &&
      Check.StatefulRefinement.check compiled.statefulSnapshot parsed)
    "JSON parsing and the stateful conversion must agree for every state and header."

private def deniedTests : IO Unit := do
  let unauthenticatedToken := EAPSession.step context EAPSession.State.initial (.application (.install token))
  let postLogoff := EAPSession.step context active (.authentication .logoff)
  let postClose := EAPSession.step context active .close
  let expired := EAPSession.step context active (.application (.advance 100))
  let revoked := EAPSession.step context active (.application .revoke)
  for state in [EAPSession.State.initial, unauthenticatedToken, authenticated, postLogoff, postClose, expired, revoked] do
    let compiled ← build state requirements
    ensure (compiled.requirementIds == ["REPORTS-READ", "REPORTS-ADMIN"] && compiled.snapshot.rules.isEmpty)
      "Denied current scopes must preserve requirement IDs while emitting no permit rule."
    for ctstate in states do
      ensure (!compiled.statefulSnapshot.permits ctstate webHeader &&
          !compiled.statefulSnapshot.permits ctstate adminHeader &&
          !compiled.statefulSnapshot.compile.allows ctstate webHeader)
        "Missing authorization, credentials, expiry, Logoff, close, and revoke deny even cached established packets."
    checkRoundtrip compiled
  ensure (authenticated.auth.authorized && authenticated.session.authenticated && authenticated.session.credential.isNone)
    "The SYNTHETIC EAP result must authorize without inventing an application credential."
  ensure (!postLogoff.auth.authorized && postLogoff.session.credential.isNone &&
      revoked.auth.authorized && revoked.session.credential.isNone && expired.session.now == 100)
    "Logoff, credential revocation, and exact expiry must retain their distinct state transitions."

private def permittedTests : IO Unit := do
  let compiled ← build active requirements
  ensure (compiled.snapshot.permits webHeader && !compiled.snapshot.permits adminHeader &&
      compiled.snapshot.rules.map (·.sourceID) == ["REPORTS-READ"])
    "A current scoped credential must permit only its selected packet class."
  for ctstate in states do
    ensure (compiled.statefulSnapshot.permits ctstate webHeader &&
        !compiled.statefulSnapshot.permits ctstate adminHeader)
      "Every conntrack classification must use the same current scope decision."
  for header in [
      { webHeader with source := 3221225987 }, { webHeader with destination := 3325256715 },
      { webHeader with protocol := Packet.Protocol.udp }, { webHeader with destinationPort := 80 }] do
    ensure (!compiled.snapshot.permits header) "Unspecified packet classes must remain denied."
  let beforeExpiry := EAPSession.step context active (.application (.advance 99))
  let current ← build beforeExpiry requirements
  ensure (current.snapshot.permits webHeader) "A credential remains current strictly before expiry."
  let both := EAPSession.step context authenticated
    (.application (.install { token with scopes := [readScope, adminScope] }))
  let compiledBoth ← build both requirements
  ensure (compiledBoth.snapshot.permits webHeader && compiledBoth.snapshot.permits adminHeader)
    "Independent valid scopes may enable separate classes in one current policy."
  checkRoundtrip compiled
  checkRoundtrip compiledBoth

private def errorTests : IO Unit := do
  let overlapping : List Intent := [⟨"READ", readScope, web⟩, ⟨"ADMIN", adminScope, web⟩]
  match compile context active overlapping with
  | .error (.intent (.conflict evidence)) =>
    ensure (evidence.permitted.id == "READ" && evidence.forbidden.id == "ADMIN" &&
        web.accepts evidence.header)
      "An exact overlap conflict must retain both scope requirement IDs and a matching packet."
  | .error error => throw (IO.userError s!"Expected an overlap conflict: {error.describe}")
  | .ok _ => throw (IO.userError "Differently authorized overlapping classes must not acquire priority.")
  let denied ← build EAPSession.State.initial overlapping
  ensure (!denied.snapshot.permits webHeader) "Two overlapping prohibitions remain consistent."
  let sameScope ← build active [⟨"READ-ONE", readScope, web⟩, ⟨"READ-TWO", readScope, web⟩]
  ensure (sameScope.snapshot.permits webHeader) "Overlapping permits for the same current scope are consistent."
  match compile context active requirements 0 with
  | .error (.intent (.exhausted required 0)) =>
    ensure (0 < required) "The cell budget error must expose the required work."
  | _ => throw (IO.userError "Session policy compilation must preserve partition budget exhaustion.")
  match compile context active [] with
  | .error (.intent (.invalid .emptyPolicy)) => pure ()
  | _ => throw (IO.userError "An empty requirement list must preserve the compiler's explicit input error.")
  match compile context active [⟨"DUPLICATE", readScope, web⟩, ⟨"DUPLICATE", adminScope, admin⟩] with
  | .error (.intent (.invalid (.duplicateId "DUPLICATE"))) => pure ()
  | _ => throw (IO.userError "Duplicate session requirement IDs must be rejected.")
  match compile context active [⟨"BAD-PORT", readScope, { destinationPorts := some (PortRange.single 443) }⟩] with
  | .error (.unsupported "BAD-PORT") => pure ()
  | _ => throw (IO.userError "Unsupported native matches must not be weakened during session compilation.")

def run : IO Unit := do
  deniedTests
  permittedTests
  errorTests
  IO.println "Current-session firewall compiler tests passed."

end NetlibTest.SessionFirewall

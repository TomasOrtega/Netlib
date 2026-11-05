import Netlib.Standards.Composition

namespace NetlibTest.StandardsComposition

open Netlib
open Netlib.Standards
open Netlib.Standards.Composition

inductive Fact where
  | applicable
  | selected
  | authenticated
  | encrypted
  deriving Repr, DecidableEq

private def source (document version clause : String) : Source :=
  ⟨document, version, clause, "urn:netlib:composition-fixture"⟩

private def clause (document version id : String) (condition : Formula Fact) : Clause Fact where
  requirement := ⟨id, source document version id, "The fixture condition must hold.", "The fixture is in scope.", []⟩
  condition := some condition

private def requireEncryption : Profile Fact :=
  ⟨"Encryption", [clause "Encryption fixture" "1" "ENCRYPT" (.atom .encrypted)]⟩

private def forbidEncryption : Profile Fact :=
  ⟨"Legacy transport", [clause "Legacy fixture" "1" "CLEAR" (.neg (.atom .encrypted))]⟩

private def guarded : Clause Fact :=
  { clause "Optional feature fixture" "1" "OPTIONAL" (.atom .encrypted) with
    applicability := .atom .applicable
    feature := .atom .selected }

private def optionalProfile : Profile Fact := ⟨"Optional encryption", [guarded]⟩

private def interpretation (applies selected encrypted : Bool) : Fact → Bool
  | .applicable => applies
  | .selected => selected
  | .authenticated => true
  | .encrypted => encrypted

example : (guarded.evaluate (interpretation false true false)).status = .notApplicable := by decide
example : (guarded.evaluate (interpretation true false false)).status = .notApplicable := by decide
example : (guarded.evaluate (interpretation true true false)).status = .violated := by decide
example : (guarded.evaluate (interpretation true true true)).status = .satisfied := by decide

example : (Profile.compose requireEncryption forbidEncryption).Meaning (interpretation true true true) ↔
    requireEncryption.Meaning (interpretation true true true) ∧
      forbidEncryption.Meaning (interpretation true true true) := Profile.compose_meaning _ _ _

private def oldVersion : Profile Fact :=
  ⟨"Access profile v1", [clause "Access fixture" "1" "ACCESS" (.atom .authenticated)]⟩

private def newVersion : Profile Fact :=
  ⟨"Access profile v2", [clause "Access fixture" "2" "ACCESS"
    (.conj (.atom .authenticated) (.atom .encrypted))]⟩

theorem version_strengthens : Refines [] newVersion oldVersion := by
  intro valuation _ safe
  intro old member
  have oldSame : old = clause "Access fixture" "1" "ACCESS" (.atom .authenticated) := by
    simpa [oldVersion] using member
  subst old
  have newSafe := safe (clause "Access fixture" "2" "ACCESS"
    (.conj (.atom .authenticated) (.atom .encrypted))) (by simp [newVersion])
  have both : valuation .authenticated = true ∧ valuation .encrypted = true := by
    simpa [Clause.Meaning, clause, Formula.Holds] using newSafe
  simpa [Clause.Meaning, clause, Formula.Holds] using both.1

theorem old_does_not_strengthen : ¬Refines [] oldVersion newVersion := by
  intro refines
  let valuation := interpretation true true false
  have oldSafe : oldVersion.Meaning valuation := by
    intro condition member
    have same : condition = clause "Access fixture" "1" "ACCESS" (.atom .authenticated) := by
      simpa [oldVersion] using member
    subst condition
    simp [Clause.Meaning, clause, Formula.Holds, valuation, interpretation]
  have newSafe := refines valuation (by simp [Reasoning.Models]) oldSafe
  have newClause := newSafe (clause "Access fixture" "2" "ACCESS"
    (.conj (.atom .authenticated) (.atom .encrypted))) (by simp [newVersion])
  simp [Clause.Meaning, clause, Formula.Holds, valuation, interpretation] at newClause

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.message)

private def compatibilityTests : IO Unit := do
  let first ← unwrap (checkCompatibility [] [requireEncryption])
  let second ← unwrap (checkCompatibility [] [forbidEncryption])
  ensure (first.isCompatible && second.isCompatible) "Each individual profile must be satisfiable."
  let combined ← unwrap (checkCompatibility [] [requireEncryption, forbidEncryption])
  ensure (!combined.isCompatible) "The composed profiles must conflict."
  ensure (combined.witness?.isNone) "A conflict must have no witness."
  ensure (combined.sources == requirements [requireEncryption, forbidEncryption])
    "The conflict must retain every original source record in order."
  ensure (first.sources == requireEncryption.requirements) "A witness must retain its source records."
  match first.witness? with
  | none => throw (IO.userError "The compatible profile must supply a witness.")
  | some valuation =>
    ensure (valuation .encrypted) "The witness must satisfy the encryption requirement."
    ensure ((first.evidence.map Report.findings).flatten.all (fun finding => finding.status.passes))
      "Witness evidence must satisfy every selected clause."
    ensure (((first.evidence.map Report.findings).flatten.map Finding.requirement) == first.sources)
      "Witness findings must preserve source metadata."
  let optional ← unwrap (checkCompatibility [.neg (.atom .selected)] [optionalProfile, forbidEncryption])
  ensure optional.isCompatible "A disabled optional feature must impose no encryption condition."
  let outside ← unwrap (checkCompatibility [.neg (.atom .applicable)] [optionalProfile, forbidEncryption])
  ensure outside.isCompatible "An inapplicable clause must impose no encryption condition."
  let active ← unwrap (checkCompatibility [.atom .selected, .atom .applicable]
    [optionalProfile, forbidEncryption])
  ensure (!active.isCompatible) "The selected applicable feature must conflict with clear transport."

private def refinementTests : IO Unit := do
  let stronger ← unwrap (checkRefinement [] newVersion oldVersion)
  ensure stronger.isRefinement "Version 2 must strengthen version 1."
  ensure (stronger.sources == newVersion.requirements ++ oldVersion.requirements)
    "The refinement must retain both source versions."
  ensure ((stronger.sources.map (·.source.version)) == ["2", "1"])
    "Identical clause IDs must not merge different versions."
  let weaker ← unwrap (checkRefinement [] oldVersion newVersion)
  ensure (!weaker.isRefinement) "Version 1 must not imply version 2."
  match weaker.witness? with
  | none => throw (IO.userError "A failed refinement must return a counterexample.")
  | some valuation =>
    ensure (valuation .authenticated && !valuation .encrypted)
      "The counterexample must permit authentication without encryption."
    ensure ((weaker.evidence.map Report.findings).flatten.any (fun finding => finding.status == .violated))
      "The counterexample must identify a failed version 2 clause."
    ensure (((weaker.evidence.map Report.findings).flatten.map Finding.requirement) == weaker.sources)
      "Counterexample findings must preserve both versions."

private def errorTests : IO Unit := do
  let unavailable : Clause Fact := { guarded with condition := none }
  let unsupportedProfile : Profile Fact := ⟨"Unsupported", [unavailable]⟩
  match checkCompatibility [] [unsupportedProfile] with
  | .ok _ => throw (IO.userError "An unsupported clause must not produce a compatibility result.")
  | .error error =>
    ensure (error.kind == .unsupported) "Unsupported input must retain its error kind."
    ensure (error.requirements == [unavailable.requirement]) "The error must retain the unsupported source."
  match checkRefinement [] unsupportedProfile oldVersion with
  | .ok _ => throw (IO.userError "An unsupported clause must not produce a refinement result.")
  | .error error => ensure (error.kind == .unsupported) "Refinement must report unsupported clauses."
  match checkCompatibility [] [requireEncryption] 0 with
  | .ok _ => throw (IO.userError "An exhausted search must not produce a compatibility result.")
  | .error error =>
    ensure (error.kind == .resource) "The search must preserve its resource error."
    ensure (error.requirements == requireEncryption.requirements) "The resource error must retain its sources."
  match checkRefinement [] newVersion oldVersion 0 with
  | .ok _ => throw (IO.userError "An exhausted search must not produce a refinement result.")
  | .error error =>
    ensure (error.kind == .resource) "Refinement must preserve its resource error."
    ensure (error.requirements == newVersion.requirements ++ oldVersion.requirements)
      "The refinement error must retain both versions."
  ensure ((unavailable.evaluate (interpretation true true true)).status == .unsupported)
    "An active unsupported clause must remain unsupported."

def run : IO Unit := do
  compatibilityTests
  refinementTests
  errorTests
  IO.println "Standards composition tests passed."

end NetlibTest.StandardsComposition

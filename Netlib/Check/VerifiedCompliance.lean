import Netlib.Check.Verification

namespace Netlib.VerifiedCompliance

private def auditFinding (config : Config) (finding : Compliance.Finding) : Except String Unit :=
  match Verification.evaluate config finding.observation with
  | .error message => .error message
  | .ok certified =>
    if finding.value = certified.value then .ok ()
    else .error s!"internal error: certified observation disagrees with report: {finding.observation.render}"

private theorem auditFinding_sound (config : Config) (finding : Compliance.Finding)
    (success : auditFinding config finding = .ok ()) :
    finding.value = true ↔ Observation.Denotes (Verification.selection config)
      (Verification.model config) finding.observation := by
  cases checked : Verification.evaluate config finding.observation with
  | error message => simp [auditFinding, checked] at success
  | ok certified =>
    by_cases agree : finding.value = certified.value
    · rw [agree]
      exact certified.correct
    · simp [auditFinding, checked, agree] at success

private def auditFindings (config : Config) : List Compliance.Finding → Except String Unit
  | [] => .ok ()
  | finding :: findings =>
    match auditFinding config finding with
    | .error message => .error message
    | .ok _ => auditFindings config findings

private theorem auditFindings_sound (config : Config) (findings : List Compliance.Finding)
    (success : auditFindings config findings = .ok ()) :
    ∀ finding ∈ findings, finding.value = true ↔
      Observation.Denotes (Verification.selection config) (Verification.model config)
        finding.observation := by
  induction findings with
  | nil => simp
  | cons finding findings ih =>
    cases head : auditFinding config finding with
    | error message => simp [auditFindings, head] at success
    | ok unitValue =>
      have tail : auditFindings config findings = .ok () := by
        simpa [auditFindings, head] using success
      intro other member
      rcases List.mem_cons.mp member with rfl | member
      · cases unitValue
        exact auditFinding_sound config _ head
      · exact ih tail other member


private structure CertifiedResults (config : Config) (requirements : List Requirement) where
  results : List (Requirement × Bool)
  covered : results.map Prod.fst = requirements
  correct : ∀ requirement value, (requirement, value) ∈ results →
    (value = true ↔ Verification.formulaMeaning config requirement.formula)

private def certifyRequirements (config : Config) :
    (requirements : List Requirement) → Except String (CertifiedResults config requirements)
  | [] => .ok ⟨[], rfl, by simp⟩
  | requirement :: requirements => do
    let head ← Verification.evaluateFormula config requirement.formula
    let tail ← certifyRequirements config requirements
    return {
      results := (requirement, head.value) :: tail.results
      covered := by simp only [List.map_cons, tail.covered]
      correct := by
        intro other value member
        rcases List.mem_cons.mp member with same | member
        · cases same
          exact head.correct
        · exact tail.correct other value member
    }

private structure CertifiedReport (config : Config) (requirements : List Requirement) where
  report : Compliance.Report
  findingsCorrect : ∀ finding ∈ report.findings, finding.value = true ↔
    Observation.Denotes (Verification.selection config) (Verification.model config) finding.observation
  resultsCovered : report.results.map Prod.fst = requirements
  resultsCorrect : ∀ requirement value, (requirement, value) ∈ report.results →
    (value = true ↔ Verification.formulaMeaning config requirement.formula)

private def certifiedCheck (config : Config) (requirements : List Requirement) :
    Except String (CertifiedReport config requirements) :=
  match Compliance.check config requirements with
  | .error message => .error message
  | .ok report =>
    match audited : auditFindings config report.findings with
    | .error message => .error message
    | .ok () =>
      match certifyRequirements config requirements with
      | .error message => .error message
      | .ok certified => .ok {
        report := ⟨report.findings, certified.results⟩
        findingsCorrect := auditFindings_sound config report.findings audited
        resultsCovered := certified.covered
        resultsCorrect := certified.correct
      }

/-- Audited findings accompany certified truth values for every original requirement. -/
def check (config : Config) (requirements : List Requirement) : Except String Compliance.Report :=
  match certifiedCheck config requirements with
  | .error message => .error message
  | .ok certified => .ok certified.report

/-- Every observation in a successful report has its full formal network meaning. -/
theorem check_findings_correct (config : Config) (requirements : List Requirement)
    (report : Compliance.Report) (success : check config requirements = .ok report) :
    ∀ finding ∈ report.findings, finding.value = true ↔
      Observation.Denotes (Verification.selection config) (Verification.model config)
        finding.observation := by
  cases checked : certifiedCheck config requirements with
  | error message => simp [check, checked] at success
  | ok certified =>
    have same : certified.report = report := by simpa [check, checked] using success
    rw [← same]
    exact certified.findingsCorrect

/-- The certified result list covers the original requirements in their original order. -/
theorem check_results_covered (config : Config) (requirements : List Requirement)
    (report : Compliance.Report) (success : check config requirements = .ok report) :
    report.results.map Prod.fst = requirements := by
  cases checked : certifiedCheck config requirements with
  | error message => simp [check, checked] at success
  | ok certified =>
    have same : certified.report = report := by simpa [check, checked] using success
    rw [← same]
    exact certified.resultsCovered

/-- Every returned requirement status is equivalent to its formal network meaning. -/
theorem check_results_correct (config : Config) (requirements : List Requirement)
    (report : Compliance.Report) (success : check config requirements = .ok report) :
    ∀ requirement value, (requirement, value) ∈ report.results →
      (value = true ↔ Verification.formulaMeaning config requirement.formula) := by
  cases checked : certifiedCheck config requirements with
  | error message => simp [check, checked] at success
  | ok certified =>
    have same : certified.report = report := by simpa [check, checked] using success
    rw [← same]
    exact certified.resultsCorrect

/-- A successful report passes exactly when all original requirements hold in the model. -/
theorem check_compliant_iff (config : Config) (requirements : List Requirement)
    (report : Compliance.Report) (success : check config requirements = .ok report) :
    report.compliant = true ↔
      ∀ requirement ∈ requirements, Verification.formulaMeaning config requirement.formula := by
  have covered := check_results_covered config requirements report success
  have correct := check_results_correct config requirements report success
  constructor
  · intro compliant requirement member
    rw [← covered] at member
    obtain ⟨⟨other, value⟩, resultMember, same⟩ := List.mem_map.mp member
    cases same
    exact (correct other value resultMember).mp
      (List.all_eq_true.mp compliant (other, value) resultMember)
  · intro all
    apply List.all_eq_true.mpr
    intro result member
    apply (correct result.1 result.2 member).mpr
    apply all result.1
    rw [← covered]
    exact List.mem_map.mpr ⟨result, member, rfl⟩

end Netlib.VerifiedCompliance

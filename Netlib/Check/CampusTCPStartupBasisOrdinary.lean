import Netlib.Check.CampusTCPStartupBasis
import Netlib.Check.CampusTCPGapProgressStart

/-! The strict ordinary source refines the common startup certificate. -/

namespace Netlib.Check.CampusTCPStartupBasis

open CampusTCPModel
open CampusTCPRound (Cut)

variable {input : Input} {complete : H.Completed input.active input.passive} {cut : Cut input complete}

def Basis.ofOrdinary (ordinary : CampusTCPGapProgressStart.StartupBasis cut) : Basis cut.report complete := {
  events := ordinary.events
  report := ordinary.report
  supported := ordinary.supported
  finished := ordinary.finished
  endpoints := Applications.initial complete
  connection := ordinary.connection
  origin := .ordinary ordinary.ordinary ordinary.history ordinary.clean
  retained := ordinary.retained
  entry := ordinary.entry
  session := ordinary.session
  aligned := .ofOrdinary ordinary.aligned
  phase := ordinary.phase }

end Netlib.Check.CampusTCPStartupBasis

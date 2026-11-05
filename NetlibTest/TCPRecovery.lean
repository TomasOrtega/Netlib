import Netlib.Protocol.TCP.Recovery

namespace NetlibTest.TCPRecovery

open Netlib.Protocol.TCP

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except Recovery.Stop α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError s!"Unexpected recovery stop: {repr reason}.")

private def stopped (result : Except Recovery.Stop α) (reason : Recovery.Stop) : IO Unit :=
  match result with
  | .error actual => ensure (actual == reason) "The recovery stop must retain its reason."
  | .ok _ => throw (IO.userError "A recovery operation passed its selected boundary.")

private def estimatorCases : IO Unit := do
  let first := RTO.first 250
  ensure (first.srtt == 250 && first.variance == 125 && RTO.exact first == 750 && RTO.interval first == 1000)
    "The first RTT sample must initialize the exact estimate and retain the one-second floor."
  let second := RTO.update first 500
  ensure (second.srtt == (1125 : Rat) / 4 && second.variance == (625 : Rat) / 4)
    "Variance must use the old SRTT before the later SRTT update."
  let fractional := RTO.update (RTO.first 1001) 2002
  ensure (fractional.srtt == (9009 : Rat) / 8 && fractional.variance == (5005 : Rat) / 8 &&
      RTO.exact fractional == (29029 : Rat) / 8 && RTO.interval fractional == 3629)
    "The selected RTO must round the exact fractional expression up to milliseconds."
  ensure (RTO.interval (RTO.first 1001) == 3003 && RTO.interval (RTO.first 0) == 1000)
    "Integral samples and a zero-millisecond sample must retain the selected floor."

private def timerCases : IO Unit := do
  let initial := Recovery.initial 800
  ensure (decide initial.Valid && initial.deadline.isNone && Recovery.flight initial == 0)
    "Startup must create an idle timer without transmitted bytes."
  stopped (Recovery.timeout initial) .idle
  let at100 ← load (Recovery.advance initial 100)
  let first := Recovery.sent at100 400
  let at200 ← load (Recovery.advance first 200)
  let second := Recovery.sent at200 400
  ensure (second.deadline == some 1100 && Recovery.flight second == 800 &&
      !decide (Recovery.SendReady second 1))
    "A later new send must keep the existing timer and the unique one-MSS flight bound."
  stopped (Recovery.advance second 199) .backwardClock
  let early ← load (Recovery.advance second 1099)
  stopped (Recovery.timeout early) .early
  let at300 ← load (Recovery.advance second 300)
  let clipped ← load (Recovery.acknowledge at300 200)
  ensure (Recovery.flight clipped == 600 && clipped.deadline == some 1300 &&
      clipped.outstanding.head?.map (·.start) == some 200 &&
      clipped.outstanding.head?.map (·.count) == some 200 && clipped.estimator.isNone)
    "A clipped ACK must clip the actual range, restart the timer, and retain its timing origin."
  let unchanged ← load (Recovery.acknowledge clipped 0)
  ensure (unchanged == clipped) "An unchanged ACK must not restart the timer."
  stopped (Recovery.acknowledge clipped 601) .ledger
  let at400 ← load (Recovery.advance clipped 400)
  let retired ← load (Recovery.acknowledge at400 200)
  ensure (retired.estimator == some (RTO.first 300) && retired.rto == 1000 &&
      retired.lastSample == some ⟨0, 100, 400⟩ && Recovery.flight retired == 400)
    "The RTT sample must come from the stored original send and the actual ACK clock."
  let cleared ← load (Recovery.acknowledge retired 400)
  ensure (cleared.deadline.isNone && Recovery.flight cleared == 0 && cleared.outstanding.isEmpty)
    "A cumulative ACK of all unique data must stop the timer."

private def retryCases : IO Unit := do
  let first := Recovery.sent (Recovery.initial 800) 800
  let due ← load (Recovery.advance first 1000)
  let (count, retried) ← load (Recovery.timeout due)
  ensure (count == 800 && Recovery.flight retried == 800 && retried.frontier == 800 &&
      retried.nextId == 1 && retried.rto == 2000 && retried.deadline == some 3000 &&
      retried.ssthresh == 1600 && retried.cwnd == 800 && retried.timeoutCount == 1)
    "A timer attempt must keep unique bytes and origin IDs while it doubles RTO and reduces congestion state."
  let beforeSecond ← load (Recovery.advance retried 2999)
  stopped (Recovery.timeout beforeSecond) .early
  let secondDue ← load (Recovery.advance retried 3000)
  let (_, twice) ← load (Recovery.timeout secondDue)
  ensure (twice.ssthresh == retried.ssthresh && twice.rto == 4000 && twice.deadline == some 7000 &&
      twice.timeoutCount == 2 && twice.outstanding.head?.map (·.retried) == some true)
    "A repeated timeout must keep the original threshold and retain retransmission ambiguity."
  let limited ← load (Recovery.advance twice 7000)
  stopped (Recovery.timeout limited) .failureHandling
  let clipped ← load (Recovery.acknowledge twice 400)
  ensure (clipped.outstanding.head?.map (·.id) == some 0 &&
      clipped.outstanding.head?.map (·.retried) == some true && clipped.estimator.isNone)
    "A clipped ACK must not remove the retry history of the remaining bytes."
  let complete ← load (Recovery.acknowledge clipped 400)
  ensure (complete.estimator.isNone && complete.rto == 4000 && complete.deadline.isNone &&
      complete.timeoutCount == 0)
    "Karn must exclude a retried original even after its last bytes are acknowledged."
  let fresh := Recovery.sent complete 800
  let acknowledgedAt ← load (Recovery.advance fresh 3250)
  let sampled ← load (Recovery.acknowledge acknowledgedAt 800)
  ensure (sampled.lastSample == some ⟨1, 3000, 3250⟩ &&
      sampled.estimator == some (RTO.first 250) && sampled.rto == 1000)
    "A later original can replace backed-off RTO only through its actual unambiguous sample."

private def duplicateCases : IO Unit := do
  let first := Recovery.sent (Recovery.initial 1200) 1200
  let one ← load (Recovery.duplicate first)
  let two ← load (Recovery.duplicate one)
  ensure (one.deadline == first.deadline && two.deadline == first.deadline && two.duplicateAcks == 2)
    "Qualifying duplicate ACKs must not restart the retransmission timer."
  stopped (Recovery.duplicate two) .fastRecovery
  let advanced ← load (Recovery.acknowledge two 1)
  ensure (advanced.duplicateAcks == 0 && Recovery.flight advanced == 1199)
    "ACK advancement must reset the qualifying duplicate count."

def run : IO Unit := do
  estimatorCases
  timerCases
  retryCases
  duplicateCases
  IO.println "Bounded TCP recovery timer tests passed."

end NetlibTest.TCPRecovery

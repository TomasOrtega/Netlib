import Netlib.Protocol.TCP.MSS

namespace NetlibTest.TCPMSS

open Netlib.Protocol TCP

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except MSS.Error α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason.message)

private def error (actual : Except MSS.Error α) (expected : MSS.Error) : IO Unit :=
  match actual with
  | .error reason => ensure (reason == expected) "The MSS failure must retain its selected reason."
  | .ok _ => throw (IO.userError "The unsupported MSS input was accepted.")

private def parsed (bytes : List UInt8) (expected : Nat) : IO Unit := do
  let offer ← load (MSS.readStartup bytes)
  ensure (offer.limit == expected) "The MSS must come from the actual option bytes."

private def optionCases : IO Unit := do
  parsed [] 536
  parsed [0, 0, 0, 0] 536
  parsed [1, 1, 1, 1] 536
  parsed [2, 4, 0, 1] 1
  parsed [2, 4, 2, 23] 535
  parsed [2, 4, 2, 24] 536
  let explicitDefault ← load (MSS.read [2, 4, 2, 24])
  ensure (explicitDefault != .absent && explicitDefault.limit == 536)
    "An explicit MSS of 536 must remain different from an absent option."
  parsed [2, 4, 5, 180] 1460
  parsed [2, 4, 255, 255] 65535
  parsed [1, 1, 2, 4, 5, 180, 0, 0] 1460
  parsed [1, 2, 4, 5, 180] 1460
  error (MSS.readStartup [2, 4, 0, 0]) .zero
  error (MSS.readStartup [2, 4, 5, 180, 2, 4, 5, 180]) .duplicate
  error (MSS.readStartup [2, 4, 0, 0, 2, 4, 5, 180]) .duplicate
  error (MSS.readStartup [2, 3, 5, 180]) .framing
  error (MSS.readStartup [2, 4, 5]) .framing
  error (MSS.readStartup [0, 2, 4, 0]) .framing
  error (MSS.readStartup [30, 1, 0, 0]) .framing
  error (MSS.readStartup [30, 8, 0, 0]) .framing
  let unknown ← load (MSS.read [30, 4, 0, 0])
  ensure (unknown == .absent) "MSS extraction must keep unrelated option semantics separate."
  error (MSS.readStartup [30, 4, 0, 0]) .otherOptions
  error (MSS.readStartup [3, 3, 7, 0]) .otherOptions
  let selected ← load (MSS.read [30, 4, 0, 0, 2, 4, 5, 180])
  ensure (selected.limit == 1460) "Unrelated framed options must not hide the MSS."
  error (MSS.readStartup [30, 4, 0, 0, 2, 4, 5, 180]) .otherOptions

private def encodingCases : IO Unit := do
  for number in [1, 2, 127, 128, 255, 256, 257, 535, 536, 1460, 4096, 65495, 65535] do
    let value ← load (MSS.Value.ofNat number)
    let bytes := MSS.encode value
    let selected := MSS.selectStartup bytes (by rw [MSS.readStartup_encode]; rfl)
    let _ := selected.property
    ensure (bytes.length == 4 && bytes.length % 4 == 0 && Options.valid bytes &&
        Options.maximumSegmentSizes bytes == [value.word] && selected.val == .present value)
      "Canonical MSS encoding must retain its positive value and aligned framing."
  error (MSS.Value.ofNat 0) .zero
  error (MSS.Value.ofNat 65536) .valueRange
  error (MSS.Value.ofNat 1000000) .valueRange

private def budgetCases : IO Unit := do
  let large ← load (MSS.Value.ofNat 1460)
  let small ← load (MSS.Value.ofNat 100)
  let one ← load (MSS.Value.ofNat 1)
  ensure (MSS.effective .absent 1500 0 0 == 536 &&
      MSS.effective (.present large) 1500 0 0 == 1460 &&
      MSS.effective (.present large) 1500 0 4 == 1456 &&
      MSS.effective (.present large) 1500 4 12 == 1444)
    "Only actual packet option overhead must reduce the effective send budget."
  ensure (MSS.effective (.present small) 1500 0 12 == 88 &&
      MSS.effective (.present large) 100 4 12 == 44)
    "The peer and local minima must precede subtraction of actual option overhead."
  ensure (MSS.effective (.present one) 1500 0 0 == 1 &&
      MSS.effective (.present one) 1500 0 1 == 0 &&
      MSS.effective (.present large) 40 0 0 == 0 &&
      MSS.effective (.present large) 39 0 0 == 0)
    "Exhausted header space must not create an artificial positive data allowance."
  for number in [1, 4, 100, 536, 1460, 65535] do
    let value ← load (MSS.Value.ofNat number)
    let peer := MSS.Offer.present value
    for limit in [40, 41, 44, 576, 1500, 65535] do
      for ipOptions in [0, 4, 40] do
        for tcpOptions in [0, 4, 12, 40] do
          let budget := MSS.effective peer limit ipOptions tcpOptions
          let rfc := min (number + 20) (limit - 20) - (20 + tcpOptions) - ipOptions
          ensure (budget == rfc && budget ≤ number)
            "The effective budget must satisfy the RFC formula and peer bound."
          if budget > 0 then
            ensure (40 + ipOptions + tcpOptions + budget ≤ limit &&
                ipOptions + tcpOptions + budget ≤ number)
              "A positive send budget must retain every actual header byte."

private def advertisementCases : IO Unit := do
  let value ← load (MSS.Value.ofNat 1460)
  let advertisement ← load (MSS.Advertisement.make 1500 value)
  let peer ← load (MSS.readStartup advertisement.options)
  ensure (advertisement.receiveLimit == 1500 && peer.limit == 1460 &&
      MSS.effective peer 600 0 0 == 560)
    "Receive advertisement and the local IP send limit must remain separate evidence."
  let defaultValue ← load (MSS.Value.ofNat 536)
  let full ← load (MSS.Advertisement.make 576 defaultValue)
  ensure (full.value.word.val == 536) "The minimum IPv4 receive limit permits the default MSS."
  let one ← load (MSS.Value.ofNat 1)
  let _ ← load (MSS.Advertisement.make 576 one)
  error (MSS.Advertisement.make 575 one) .receiveLimit
  error (MSS.Advertisement.make 65536 one) .receiveLimit
  let tooLarge ← load (MSS.Value.ofNat 537)
  error (MSS.Advertisement.make 576 tooLarge) .advertisementBound
  let maximum ← load (MSS.Value.ofNat 65495)
  let _ ← load (MSS.Advertisement.make 65535 maximum)
  let overflowing ← load (MSS.Value.ofNat 65535)
  error (MSS.Advertisement.make 65535 overflowing) .advertisementBound

def run : IO Unit := do
  optionCases
  encodingCases
  budgetCases
  advertisementCases
  IO.println "Directional TCP MSS tests passed."

end NetlibTest.TCPMSS

import Netlib.Standards.ThreeGPP.ServiceAccess
open Netlib Netlib.Protocol
private def ctx : Context := ⟨"consumer", "producer", "nrf"⟩
private def scope : Scope := ⟨"service", "read"⟩
private def credential : Credential := ⟨"nrf", "consumer", "producer", [scope], 10, true⟩
private def check (events : List FiveG.TraceEvent) : Bool :=
  (FiveG.check ⟨ctx, events⟩).compliant
example : check [.authenticate true, .token credential, .request scope true,
    .request scope true] = true := by decide
example : check [.authenticate true, .token credential, .tick 10,
    .request scope true] = false := by decide
example : check [.authenticate true, .token credential, .tick 10,
    .request scope false] = true := by decide
example : check [.authenticate true, .token credential, .authenticate true,
    .request scope true] = false := by decide
example : check [.authenticate true, .token credential, .close,
    .token credential, .request scope true] = false := by decide
example : check [.authenticate true, .token credential, .tick 10, .tick 1,
    .request scope true] = false := by decide
example : check [.request scope false] = true := by decide
example : check [.authenticate true, .token { credential with subject := "other" },
    .request scope true] = false := by decide
example : check [.authenticate true, .token { credential with audience := "other" },
    .request scope true] = false := by decide
example : check [.authenticate true, .token credential, .tick 10,
    .token {credential with expiresAt := 20}, .request scope true] = true := by decide

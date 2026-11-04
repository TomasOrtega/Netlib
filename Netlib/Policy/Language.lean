import Netlib.Model.Config
import Netlib.Core.Logic

namespace Netlib

/-- All and some reachability differ for selectors containing several devices. -/
inductive Observation where
  | reach (source target : Selector) (service : String) (universal : Bool)
  | mediated (source target gateways : Selector) (service : String)
  deriving Repr, BEq, DecidableEq

namespace Observation

def render : Observation → String
  | .reach s t service all =>
    s!"{if all then "all" else "some"} {s.render} -> {t.render} for {service}"
  | .mediated s t g service => s!"{s.render} -> {t.render} through {g.render} for {service}"

def selectors : Observation → List Selector
  | .reach s t _ _ => [s, t]
  | .mediated s t g _ => [s, t, g]

end Observation

structure Requirement where
  id : String
  line : Nat
  text : String
  formula : Formula Observation
  deriving Repr

namespace Language

private def service (s : String) : Except String String :=
  if !s.isEmpty && s != "*" && s.toList.all
      (fun ch => ch.isAlphanum || ch == '_' || ch == '-' || ch == '.') then .ok s
  else .error "use one named traffic class; wildcard queries are not supported"

private def clause (tokens : List String) : Except String (Formula Observation) := do
  match tokens with
  | [s, "must", "reach", t, "for", traffic] =>
    return .atom (.reach (← Selector.parse s) (← Selector.parse t) (← service traffic) true)
  | [s, "must", "be", "isolated", "from", t, "for", traffic] =>
    return .neg (.atom (.reach (← Selector.parse s) (← Selector.parse t) (← service traffic) false))
  | [s, "must", "traverse", g, "before", t, "for", traffic] =>
    return .atom (.mediated (← Selector.parse s) (← Selector.parse t)
      (← Selector.parse g) (← service traffic))
  | _ => .error "unsupported sentence; expected reach, be isolated from, or traverse ... before"

private def formula (tokens : List String) : Except String (Formula Observation) := do
  match tokens with
  | "if" :: rest =>
    let left := rest.takeWhile (· != "then")
    let right := (rest.dropWhile (· != "then")).drop 1
    if right.isEmpty || right.contains "then" then
      throw "conditional must contain exactly one then"
    return .impl (← clause left) (← clause right)
  | _ => clause tokens

private def parseLine (number : Nat) (line : String) : Except String Requirement := do
  let line := line.trimAscii.toString
  let (id, body) ← match line.splitOn ": " with
    | [id, body] => pure (id, body)
    | _ => .error "expected ID: sentence."
  if id.isEmpty || !(id.toList.all (fun ch => ch.isAlphanum || ch == '_' || ch == '-')) then
    throw "invalid requirement ID"
  if !body.endsWith "." then throw "sentence must end with a period"
  let tokens := (body.dropEnd 1).toString.splitOn " " |>.filter (!·.isEmpty)
  return ⟨id, number, body, ← formula tokens⟩

def parse (text : String) : Except String (List Requirement) := do
  let mut result := []
  let mut lineNumber := 0
  for line in text.splitOn "\n" do
    lineNumber := lineNumber + 1
    let stripped := line.trimAscii.toString
    if stripped.isEmpty || stripped.startsWith "#" then continue
    let req ← (parseLine lineNumber stripped).mapError (s!"line {lineNumber}: " ++ ·)
    if result.any (fun r : Requirement => r.id == req.id) then
      throw s!"line {lineNumber}: duplicate requirement ID: {req.id}"
    result := result ++ [req]
  if result.isEmpty then throw "requirement document is empty"
  return result

/-- These laws assume every selector denotes at least one device. -/
def laws (observations : List Observation) : List (Formula Observation) :=
  (observations.flatMap fun observation => match observation with
    | .reach s t service _ =>
      let all := Formula.atom (Observation.reach s t service true)
      let some := Formula.atom (Observation.reach s t service false)
      let forward := Formula.impl all some
      match s, t with
      | .node _, .node _ => [forward, .impl some all]
      | _, _ => [forward]
    | .mediated s t g service =>
      [.impl (.neg (.atom (.reach s t service false))) (.atom (.mediated s t g service))]).eraseDups

end Language
end Netlib

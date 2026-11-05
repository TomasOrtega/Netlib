import Lean

namespace Netlib.Import.Json

private inductive Frame where
  | object (keys : List String) (expectsKey : Bool)
  | array

private def literal : List Char → List Char → Bool → Except String (String × List Char)
  | [], _, _ => .error "Unterminated JSON string."
  | char :: rest, reversed, escaped =>
    if escaped then literal rest (char :: reversed) false
    else if char = '\\' then literal rest (char :: reversed) true
    else if char = '"' then .ok (String.ofList ((char :: reversed).reverse), rest)
    else literal rest (char :: reversed) false

private def uniqueKeys : Nat → List Char → List Frame → Except String Unit
  | _, [], _ => .ok ()
  | 0, _ :: _, _ => .error "JSON key scan exhausted its input bound."
  | fuel + 1, char :: rest, frames => do
    match char with
    | '"' =>
      let (token, remaining) ← literal rest ['"'] false
      let frames ← match frames with
        | .object keys true :: parents => do
          let key ← (← Lean.Json.parse token).getStr?
          if keys.contains key then throw s!"Duplicate JSON object key: {key}."
          pure (.object (key :: keys) false :: parents)
        | _ => pure frames
      uniqueKeys fuel remaining frames
    | '{' => uniqueKeys fuel rest (.object [] true :: frames)
    | '[' => uniqueKeys fuel rest (.array :: frames)
    | '}' | ']' => uniqueKeys fuel rest frames.tail
    | ',' =>
      let frames := match frames with
        | .object keys _ :: parents => .object keys true :: parents
        | _ => frames
      uniqueKeys fuel rest frames
    | _ => uniqueKeys fuel rest frames

/-- Validate syntax before checking decoded object keys at every nesting level. -/
def parse (text : String) : Except String Lean.Json := do
  let value ← Lean.Json.parse text
  let chars := text.toList
  uniqueKeys chars.length chars []
  return value

end Netlib.Import.Json

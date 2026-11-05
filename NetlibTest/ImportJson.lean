import Netlib.Import.Json
import Netlib.Model.Config
import Netlib.Model.DataPlane
import Netlib.Standards.ThreeGPP.ServiceAccess
import Netlib.Standards.IEEE80211.Deployment

namespace NetlibTest.ImportJson

private def accept (text : String) : IO Unit := do
  match Netlib.Import.Json.parse text with
  | .ok _ => pure ()
  | .error message => throw (IO.userError s!"Valid JSON failed: {message}")

private def reject (text : String) : IO Unit := do
  match Netlib.Import.Json.parse text with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "Ambiguous or invalid JSON was accepted.")

private def rejectsResult (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "A configuration accepted duplicate JSON keys.")

private def duplicate (text key : String) : String :=
  text.replace ("\"" ++ key ++ "\":") ("\"" ++ key ++ "\":null,\"" ++ key ++ "\":")

def run : IO Unit := do
  reject "{\"a\":1,\"a\":2}"
  reject "{\"a\":1,\"\\u0061\":2}"
  reject "{\"😀\":1,\"\\uD83D\\uDE00\":2}"
  reject "{\"a\\nb\":1,\"a\\u000Ab\":2}"
  reject "{\"outer\":[{\"a\":1,\"a\":2}]}"
  accept "{\"a\":1,\"outer\":{\"a\":2}}"
  accept "[{\"a\":1},{\"a\":2}]"
  accept "{\"a\":\"{\\\"a\\\":1,\\\"a\\\":2}\",\"b\":\"[],:{}\"}"
  accept "{\"a\\\"b\":1,\"a\\\\b\":2}"
  accept "{\"a\":[],\"b\":{},\"c\":[false,null,1.25e2,\"text\"]}"
  accept "true"
  accept "\"text\""
  for text in ["", "{", "[1,]", "{\"a\":1,}", "{\"a\":1} {}", "{a:1}"] do reject text
  rejectsResult (Netlib.Config.parse (duplicate (← IO.FS.readFile "examples/secure.json") "links"))
  rejectsResult (Netlib.DataPlane.Config.parse
    (duplicate (← IO.FS.readFile "examples/dataplane/secure.json") "schema"))
  rejectsResult (Netlib.DataPlane.Config.parseTrafficSelection
    (duplicate (← IO.FS.readFile "examples/traffic/https.json") "protocol"))
  rejectsResult (Netlib.FiveG.parse
    (duplicate (← IO.FS.readFile "examples/5g/secure.json") "schema"))
  rejectsResult (Netlib.Wifi.checkDeployment (← IO.FS.readFile "examples/wifi/secure.conf")
    (duplicate (← IO.FS.readFile "examples/wifi/deployment.json") "schema"))
  IO.println "Strict JSON import tests passed."

end NetlibTest.ImportJson

import VersoManual
import Manual

open Verso.Genre Manual

def manualConfig : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1

def main := manualMain (%doc Manual) (config := manualConfig)

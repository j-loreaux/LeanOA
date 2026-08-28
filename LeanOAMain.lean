import VersoManual
import VersoBlueprint.PreviewManifest
import LeanOABlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc LeanOABlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
    (config := { htmlDepth := 1 })

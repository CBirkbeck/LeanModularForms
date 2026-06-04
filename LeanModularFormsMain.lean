import VersoManual
import VersoBlueprint.PreviewManifest
import LeanModularForms.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc LeanModularForms.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)

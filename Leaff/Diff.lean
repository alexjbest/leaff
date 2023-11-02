import Lean
import Std.Data.RBMap.Basic
import Leaff.Deriving.Optics



open Lean in
/--
A type representing single differences between two environments, limited
to changes that a user might wish to see.
-/
inductive Diff : Type
  | added (name : Name)
  | removed (name : Name)
  | modified (name : Name)
  | renamed (oldName newName : Name)
  | proofChanged (name : Name)
  | typeChanged (name : Name)
  | docChanged (name : Name)
  | docAdded (name : Name)
  | docRemoved (name : Name)
  | attributeAdded (attrName name : Name)
  | attributeRemoved (attrName name : Name)
  | attributeChanged (attrName name : Name)
  | directImportAdded (module importName : Name)
  | transitiveImportAdded (module importName : Name)
  | directImportRemoved (module importName : Name)
  | transitiveImportRemoved (module importName : Name)

set_option trace.derive_optics true
derive_optics Diff
#eval Diff.isAttributeAdded (.attributeAdded `a `a)

namespace Diff
open Std

open ToFormat in
def summarize (diffs : List Diff) : Format := format <|
  Array.run (#[] : Array Format)

end Diff

open Lean Environment

namespace Lean.Environment
def diff (old new : Environment) : Array Diff :=
  let oldnames := old.constants.toList.map Prod.fst
  let newnames := new.constants.toList.map Prod.fst
  oldnames.diff newnames

end Lean.Environment

def diffImports (imports₁ imports₂ : List Import) : IO (Array Diff) := do
  let opts := Options.empty
  let trustLevel := 1
  withImportModules imports₁ opts trustLevel (fun env₁ => withImportModules imports₂ opts trustLevel (fun env₂ => do
    return env₁.diff env₂))

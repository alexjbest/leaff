import Lean
import Std.Data.RBMap.Basic
import Leaff.Deriving.Optics
import Leaff.Hash
import Leaff.HashSet


/-!
# Leaff (Lean Diff) core

## Main types
- `Diff` the type of a single human understandable difference between two environments

-/

open Lean in
/--
A type representing single differences between two environments, limited
to changes that a user might wish to see.
-/
inductive Diff : Type
  | added (name : Name)
  | removed (name : Name)
  | renamed (oldName newName : Name) (namespaceOnly : Bool)
  | movedToModule (name : Name) -- maybe args here
  | movedWithinModule (name : Name)
  | proofChanged (name : Name)
  | typeChanged (name : Name)
  | extensionEntriesModified (ext : Name)
  | docChanged (name : Name) -- TODO how does module/opther doc fit in here
  | docAdded (name : Name)
  | docRemoved (name : Name)
  | moduleRenamed (oldName newName : Name)
  | attributeAdded (attrName name : Name)
  | attributeRemoved (attrName name : Name)
  | attributeChanged (attrName name : Name)
  | directImportAdded (module importName : Name) -- these might be pointless
  | directImportRemoved (module importName : Name)
  | transitiveImportAdded (module importName : Name)
  | transitiveImportRemoved (module importName : Name)
deriving DecidableEq, Repr


-- TODO maybe an "optic" for isBlah that returns all args of blah
-- set_option trace.derive_optics true
derive_optics Diff



namespace Diff
open Std
-- TODO can we make the output richer,
-- colours
-- links / messagedata in the infoview maybe extracted as links somehow
-- group by filename
-- should group also by most important first, moves aren't interesting normally!
open ToFormat in
def summarize (diffs : List Diff) (includeInternals := false) : Format := Id.run do
  if diffs = [] then return "No differences found."
  let mut out : Format := ("Found differences:" : Format).append .line
  for d in diffs do
    if d.isAdded   && (includeInternals || !(name! d).isInternal) then out := out.append <| format s!"added {name! d}\n" -- awkward that we can't use dot notation with nested
    if d.isRemoved && (includeInternals || !(name! d).isInternal) then out := out.append <| format s!"removed {name! d}\n"
    if d.isRenamed && (includeInternals || !(oldName! d).isInternal) then out := out.append <| format s!"renamed {oldName! d} → {newName! d}\n"
    if d.isDocAdded   then out := out.append <| format s!"doc added to {name! d}\n"
    if d.isDocRemoved then out := out.append <| format s!"doc removed from {name! d}\n"
    if d.isDocChanged then out := out.append <| format s!"doc modified for {name! d}\n"
    if d.isExtensionEntriesModified then out := out.append <| format s!"extension entry modified for {ext! d}\n"
    -- dbg_trace (repr d)
  out := out.append (format s!"{diffs.length} differences, some not shown")
  pure out

end Diff

open Lean Environment

namespace Lean.Environment

open Std

def importDiffs (old new : Environment) : List Diff := Id.run do
  let mut out : List Diff := []
  -- dbg_trace new.header.moduleNames
  -- dbg_trace new.header.moduleData[2]!.imports
  -- everything should be in map₁ as we loaded from file?
  pure out


/-- Copied from `whatsnew` by @gebner-/
def diffExtension (old new : Environment)
    (ext : PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState) :
    (Option Diff) := unsafe
  let oldSt := ext.toEnvExtension.getState old
  let newSt := ext.toEnvExtension.getState new
  -- if ptrAddrUnsafe oldSt == ptrAddrUnsafe newSt then return none
  -- dbg_trace oldSt.importedEntries
  -- dbg_trace ext.statsFn oldSt.state
  -- dbg_trace ext.statsFn newSt.state
  let oldEntries := ext.exportEntriesFn oldSt.state
  let newEntries := ext.exportEntriesFn newSt.state
  if newEntries.size = oldEntries.size then none else
  some <| .extensionEntriesModified ext.name
  -- m!"-- {ext.name} extension: {(newEntries.size - oldEntries.size : Int)} new entries"

def extDiffs (old new : Environment) : IO (List Diff) := do
  let mut out : List Diff := []
  for ext in ← persistentEnvExtensionsRef.get do
    -- dbg_trace ext.name
    if let some diff := diffExtension old new ext then
      out := diff :: out
  -- let oldexts := RBSet.ofList (old.extensions Prod.fst) Name.cmp
  -- let newexts := RBSet.ofList (new.constants.map₁.toList.map Prod.fst) Name.cmp
  pure out

def diffHash (c : ConstantInfo) : UInt64 := mixHash c.name.hash <| mixHash c.type.hash c.value!.hash

def constantDiffs (old new : Environment) : List Diff := Id.run do
  let mut out : List Diff := []
  -- dbg_trace new.header.moduleNames
  -- dbg_trace new.header.moduleData[2]!.imports
  -- everything should be in map₁ as we loaded from file?
  -- TODO should we use rbmap or hashmap?
  -- let oldhashes := (HashMap.fold (fun old name const =>
  --   let ha := (diffHash const)
  --   old.insert ha <| (old.findD ha #[]).push name) (mkRBMap UInt64 (Array Name) Ord.compare) old.constants.map₁)
  let oldhashes := (HashMap.fold (fun old name const =>
    if const.hasValue && ¬ name.isInternal then old.insert name else old) (@HashSet.empty Name _ ⟨fun n => diffHash <| old.constants.map₁.find! n⟩) old.constants.map₁)
  let newhashes := (HashMap.fold (fun old name const =>
    if const.hasValue && ¬ name.isInternal then old.insert name else old) (@HashSet.empty Name _ ⟨fun n => diffHash <| new.constants.map₁.find! n⟩) new.constants.map₁)
  -- TODO can we fold over smaller
  -- TODO init with right size
  -- out := out ++ (newnames.sdiff oldnames).toList.map .added
  -- out := out ++ (oldnames.sdiff newnames).toList.map .removed
  -- dbg_trace out.length
  dbg_trace (HashSet.sdiff oldhashes newhashes).toList
  for (di, removed) in (HashSet.sdiff oldhashes newhashes).toList do
    if removed then out := .removed di :: out
    if !removed then out := .added di :: out
  pure out

-- TODO some sort of minimization pass might be needed?
-- TODO make this not IO and pass exts in
def diff (old new : Environment) : IO (List Diff) := do
  -- logHashCollisions old
  -- logHashCollisions new
  pure <|
    constantDiffs old new ++
    importDiffs old new ++
    (← extDiffs old new)

end Lean.Environment

unsafe
def diffImports (imports₁ imports₂ : Array Import) : IO Unit := do
  let opts := Options.empty
  let trustLevel := 1
  withImportModules imports₁ opts trustLevel (fun env₁ => withImportModules imports₂ opts trustLevel (fun env₂ => do
    IO.println <| Diff.summarize (← (env₁.diff env₂))))

unsafe
def summarizeDiffImports (imports₁ imports₂ : Array Import) : IO Unit :=
  diffImports imports₁ imports₂

#eval summarizeDiffImports #[`Std.Lean.Float] #[`Std.Data.Fin.Init.Lemmas]
-- #eval summarizeDiffImports #[`Mathlib] #[`Std.Data.Fin.Init.Lemmas]

#eval summarizeDiffImports #[`test.TestA] #[`test.TestB]

-- hash collision
-- #check Lean.reservedMacroScope
-- #check UInt64.size

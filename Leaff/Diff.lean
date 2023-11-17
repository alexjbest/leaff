import Lean
import Std.Data.RBMap.Basic
import Leaff.Deriving.Optics
import Leaff.Hash
import Leaff.HashSet


/-!
# Leaff (Lean Diff) core

## Main types
- `Trait` hashable functions of `ConstantInfo`'s used to determine whether two constants are different
- `Diff` the type of a single human understandable difference between two environments

-/
open Lean
/--
Traits are functions from `ConstantInfo` to some type `α` that when changed,
results in some meaningful difference between two constants.
For instance the type, name, value of a constant, or whether it is an axiom,
theorem, or definition. -/
structure Trait :=
  α : Type
  val : ConstantInfo → α
  id : Name
  [ins : Hashable α]

instance : BEq Trait where
   beq a b := a.id == b.id
instance {t : Trait} : Hashable t.α := t.ins

def Trait.mk' (α : Type) [Hashable α] (val : ConstantInfo → α) (name : Name := by exact decl_name%) : Trait := ⟨α, val, name⟩
namespace Trait
def type : Trait := Trait.mk' Expr ConstantInfo.type
def value : Trait := Trait.mk' Expr ConstantInfo.value!

def name : Trait := Trait.mk' Name ConstantInfo.name
def species : Trait := Trait.mk' String fun
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def relevantTraits : List Trait := [name, type, value, species]
def hashExcept (t : Trait) : ConstantInfo → UInt64 :=
  (relevantTraits.filter (· != t)).foldl (fun h t c => mixHash (hash (t.val c)) (h c)) (fun _ => 7) -- TODO 0 or 7...

-- section testing
-- def aaaa := 1
-- def aaab := 1
-- #eval show MetaM Unit from do
--   let e ← getEnv
--   let n ← e.find? ``aaaa
--   dbg_trace (hashExcept name n)
--   let n ← e.find? ``aaab
--   dbg_trace (hashExcept name n)
-- end testing

end Trait

open Lean
/--
A type representing single differences between two environments, limited
to changes that a user might wish to see.
-/
inductive Diff : Type
  | added (name : Name)
  | removed (name : Name)
  | renamed (oldName newName : Name) (namespaceOnly : Bool)
  | movedToModule (name oldModuleName newModuleName : Name) -- maybe args here
  | movedWithinModule (name moduleName : Name)
  | proofChanged (name : Name) (isProofRelevant : Bool) -- TODO maybe value changed also for defs
  | typeChanged (name : Name)
  | speciesChanged (name : Name) (fro to : String)
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

-- TODO changed def to lemma or vice versa
-- TODO distinguish between proof changed and value changed


-- TODO maybe variant "optic"s for isBlah that returns all args of blah not just a bool
-- set_option trace.derive_optics true
derive_optics Diff

namespace Diff
/-- priority for displaying diffs, lower numbers are more important and should come first in the output -/
def prio : Diff → Nat
  | .added _ => 1
  | .removed _ => 1
  | .renamed _ _ _ => 2 -- TODO namespace lower
  | .movedToModule _ _ _ => 2
  | .movedWithinModule _ _ => 3
  | .proofChanged _ _ => 2 -- TODO higher if proof relevant
  | .typeChanged _ => 1
  | .speciesChanged _ _ _ => 1
  | .extensionEntriesModified _ => 1
  | .docChanged _ => 2
  | .docAdded _ => 2
  | .docRemoved _ => 1
  | .moduleRenamed _ _ => 1
  | .attributeAdded _ _ => 1
  | .attributeRemoved _ _ => 1
  | .attributeChanged _ _ => 2
  | .directImportAdded _ _ => 1
  | .directImportRemoved _ _ => 2
  | .transitiveImportAdded _ _ => 3
  | .transitiveImportRemoved _ _ => 3

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
    -- TODO this should be a match
    -- TODO should build a big list of types and priorities and then sort by lex on prio then type
    -- TODO rethink whether internals should be ignored here or in the differ logic
    if d.isAdded   && (includeInternals || !(name! d).isInternal) then out := out.append <| format s!"added {name! d}\n" -- awkward that we can't use dot notation with nested
    if d.isRemoved && (includeInternals || !(name! d).isInternal) then out := out.append <| format s!"removed {name! d}\n"
    -- TDOO namespaceonly
    if d.isRenamed && (includeInternals || !(oldName! d).isInternal) then out := out.append <| format s!"renamed {oldName! d} → {newName! d}\n"
    if d.isMovedToModule && (includeInternals || !(name! d).isInternal) then out := out.append <| format s!"moved {name! d} to {newModuleName! d}\n"
    if d.isMovedWithinModule && (includeInternals || !(name! d).isInternal) then out := out.append <| format s!"moved {name! d} within module {moduleName! d}\n"
    if d.isProofChanged && (includeInternals || !(name! d).isInternal) then out := out.append <| format s!"proof changed for {name! d}\n"
    if d.isTypeChanged && (includeInternals || !(name! d).isInternal) then out := out.append <| format s!"type changed for {name! d}\n"
    if d.isSpeciesChanged && (includeInternals || !(name! d).isInternal) then out := out.append <| format s!"{name! d} changed from {fro! d} to {to! d}\n"
    if d.isExtensionEntriesModified then out := out.append <| format s!"extension entry modified for {ext! d}\n"
    if d.isDocChanged then out := out.append <| format s!"doc modified for {name! d}\n"
    if d.isDocAdded   then out := out.append <| format s!"doc added to {name! d}\n"
    if d.isDocRemoved then out := out.append <| format s!"doc removed from {name! d}\n"
    if d.isModuleRenamed then out := out.append <| format s!"module renamed {oldName! d} → {newName! d}\n"
    if d.isAttributeAdded then out := out.append <| format s!"attribute {attrName! d} added to {name! d}\n"
    if d.isAttributeRemoved then out := out.append <| format s!"attribute {attrName! d} removed from {name! d}\n"
    if d.isAttributeChanged then out := out.append <| format s!"attribute {attrName! d} changed for {name! d}\n"
    if d.isDirectImportAdded then out := out.append <| format s!"direct import {importName! d} added to {module! d}\n"
    if d.isDirectImportRemoved then out := out.append <| format s!"direct import {importName! d} removed from {module! d}\n"
    if d.isTransitiveImportAdded then out := out.append <| format s!"transitive import {importName! d} added to {module! d}\n"
    if d.isTransitiveImportRemoved then out := out.append <| format s!"transitive import {importName! d} removed from {module! d}\n"
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

open Trait


-- TODO make this the hash of all relevantTraits, but
def diffHash (c : ConstantInfo) : UInt64 := mixHash (hash <| species.val c) <| mixHash c.name.hash <| mixHash c.type.hash c.value!.hash

def constantDiffs (old new : Environment) : List Diff := Id.run do
  let mut out : List Diff := []
  -- dbg_trace new.header.moduleNames
  -- dbg_trace new.header.moduleData[2]!.imports
  -- everything should be in map₁ as we loaded from file?
  -- TODO should we use rbmap or hashmap?
  -- let oldhashes := (HashMap.fold (fun old name const =>
  --   let ha := (diffHash const)
  -- let (all, ex) := (HashMap.fold (fun (all, ex) name const =>
  --   if const.hasValue && ¬ name.isInternal then (all + 1, ex + 1) else (all + 1, ex)) (0,0) old.constants.map₁)
  -- dbg_trace (all, ex)
  --   old.insert ha <| (old.findD ha #[]).push name) (mkRBMap UInt64 (Array Name) Ord.compare) old.constants.map₁)
  let sz := max (new.constants.map₁.size / 5) (old.constants.map₁.size / 5)

  let oldhashes := (HashMap.fold (fun old name const =>
    if const.hasValue && ¬ name.isInternal then old.insert name else old) (@mkHashSet Name _ ⟨fun n => diffHash <| old.constants.map₁.find! n⟩ sz) old.constants.map₁)
  let newhashes := (HashMap.fold (fun old name const =>
    if const.hasValue && ¬ name.isInternal then old.insert name else old) (@mkHashSet Name _ ⟨fun n => diffHash <| new.constants.map₁.find! n⟩ sz) new.constants.map₁)
  -- TODO can we fold over smaller
  -- TODO init with right size
  -- out := out ++ (newnames.sdiff oldnames).toList.map .added
  -- out := out ++ (oldnames.sdiff newnames).toList.map .removed
  -- dbg_trace out.length
  -- dbg_trace (HashSet.sdiff oldhashes newhashes).toList
  let diff := (HashSet.sdiff oldhashes newhashes).toList
  let befores := diff.filterMap (fun (di, bef) => if bef then some (old.constants.map₁.find! di) else none)
  let afters := diff.filterMap (fun (di, bef) => if bef then none else some (new.constants.map₁.find! di))
  -- dbg_trace dm.map (fun (c, rem) => (c.name, rem))
  -- TODO could use hashset here
  let mut explained := []
  for t in relevantTraits do
    let f := t.hashExcept
    for b in befores do
      if (b.name, true) ∈ explained then continue
      for a in afters do
        if (a.name, false) ∈ explained then continue
        if f a == f b ∧ t == name then
          out := .renamed b.name a.name false :: out
          explained := (a.name, true) :: (b.name, false) :: explained
          continue
        if f a == f b ∧ t == value then
          out := .proofChanged a.name false :: out -- TODO check if proof relevant
          explained := (a.name, true) :: (b.name, false) :: explained
          continue
        if f a == f b ∧ t == type then
          out := .typeChanged a.name :: out
          explained := (a.name, true) :: (b.name, false) :: explained
          continue
        if f a == f b ∧ t == species then
          out := .speciesChanged a.name (species.val b) (species.val a) :: out
          explained := (a.name, true) :: (b.name, false) :: explained
        -- dbg_trace "asd"
        -- dbg_trace mat.map ConstantInfo.name
  for a in afters do
    if !(a.name, false) ∈ explained then out := .added a.name :: out
  for b in befores do
    if !(b.name, true) ∈ explained then out := .removed b.name :: out
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

#eval summarizeDiffImports #[`Std.Classes.RatCast] #[`Std.Data.Rat]
-- #eval summarizeDiffImports #[`Mathlib] #[`Std.Data.Fin.Init.Lemmas]


#eval summarizeDiffImports #[`test.TestA] #[`test.TestB]

-- hash collision
-- #check Lean.reservedMacroScope
-- #check UInt64.size

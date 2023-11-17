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

-- TODO add module trait, needs env
-- TODO add universe vars trait? possibly already covered by type

def relevantTraits : List Trait := [name, type, value, species]
-- TODO maybe find some way to make absence of some traits imply others
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


/--
Copied from mathlib:
Lean 4 makes declarations which are technically not internal
(that is, head string does not start with `_`) but which sometimes should
be treated as such. For example, the `to_additive` attribute needs to
transform `proof_1` constants generated by `Lean.Meta.mkAuxDefinitionFor`.
This might be better fixed in core, but until then, this method can act
as a polyfill. This method only looks at the name to decide whether it is probably internal.
Note: this declaration also occurs as `shouldIgnore` in the Lean 4 file `test/lean/run/printDecls`.
-/
def Lean.Name.isInternal' (declName : Name) : Bool :=
  declName.isInternal ||
  match declName with
  | .str _ s => "match_".isPrefixOf s || "proof_".isPrefixOf s
  | _        => true

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
/-- Priority for displaying diffs, lower numbers are more important and should come first in the output.
These should all be distinct as it is what we use to group diffs also -/
def prio : Diff → Nat
  | .added _ => 11
  | .removed _ => 12
  | .renamed _ _ _ => 21 -- TODO namespace lower
  | .movedToModule _ _ _ => 22
  | .movedWithinModule _ _ => 31
  | .proofChanged _ _ => 23 -- TODO higher if proof relevant
  | .typeChanged _ => 13
  | .speciesChanged _ _ _ => 14
  | .extensionEntriesModified _ => 15
  | .docChanged _ => 24
  | .docAdded _ => 25
  | .docRemoved _ => 16
  | .moduleRenamed _ _ => 17
  | .attributeAdded _ _ => 18
  | .attributeRemoved _ _ => 19
  | .attributeChanged _ _ => 26
  | .directImportAdded _ _ => 19
  | .directImportRemoved _ _ => 27
  | .transitiveImportAdded _ _ => 33
  | .transitiveImportRemoved _ _ => 34

open Std
-- TODO can we make the output richer,
-- colours
-- links / messagedata in the infoview maybe extracted as links somehow
-- group by filename
-- should group also by most important first, moves aren't interesting normally!
open ToFormat in
def summarize (diffs : List Diff) : Format := Id.run do
  if diffs = [] then return "No differences found."
  let mut out : Format := ("Found differences:" : Format).append .line
  let mut diffs := diffs.toArray
  diffs := diffs.qsort (fun a b => a.prio < b.prio)
  for d in diffs do
    -- TODO this should be a match
    -- TODO should build a big list of types and priorities and then sort by lex on prio then type
    if d.isAdded then out := out.append <| format s!"added {name! d}\n" -- awkward that we can't use dot notation with nested
    if d.isRemoved then out := out.append <| format s!"removed {name! d}\n"
    -- TDOO namespaceonly
    if d.isRenamed then out := out.append <| format s!"renamed {oldName! d} → {newName! d}\n"
    if d.isMovedToModule then out := out.append <| format s!"moved {name! d} to {newModuleName! d}\n"
    if d.isMovedWithinModule then out := out.append <| format s!"moved {name! d} within module {moduleName! d}\n"
    if d.isProofChanged then out := out.append <| format s!"proof changed for {name! d}\n"
    if d.isTypeChanged then out := out.append <| format s!"type changed for {name! d}\n"
    if d.isSpeciesChanged then out := out.append <| format s!"{name! d} changed from {fro! d} to {to! d}\n"
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
  out := out.append (format s!"{diffs.size} differences, some not shown")
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
  -- dbg_trace new.header.moduleNames
  -- dbg_trace new.header.moduleData[2]!.imports
  -- TODO should we use rbmap or hashmap?
  -- let oldhashes := (HashMap.fold (fun old name const =>
  --   let ha := (diffHash const)
  -- let (all, ex) := (HashMap.fold (fun (all, ex) name const =>
  --   if const.hasValue && ¬ name.isInternal then (all + 1, ex + 1) else (all + 1, ex)) (0,0) old.constants.map₁)
  -- dbg_trace (all, ex)
  --   old.insert ha <| (old.findD ha #[]).push name) (mkRBMap UInt64 (Array Name) Ord.compare) old.constants.map₁)
  -- TODO recompute this for mathlib!
  -- sz is roughly how many non-internal decls we expect, empirically around 1/5th of total
  let sz := max (new.constants.map₁.size / 5) (old.constants.map₁.size / 5)

  -- first we make a hashmap of all decls, hashing with `diffHash`, this should cut the space of "interesting" decls down drastically
  -- TODO reconsider internals, how useful are they
  -- note everything should be in map₁ as we loaded from file
  let oldhashes := (HashMap.fold (fun old name const =>
    if const.hasValue && ¬ name.isInternal' then old.insert name else old) (@mkHashSet Name _ ⟨fun n => diffHash <| old.constants.map₁.find! n⟩ sz) old.constants.map₁)
  dbg_trace "hashes1 made"
  let newhashes := (HashMap.fold (fun old name const =>
    if const.hasValue && ¬ name.isInternal' then old.insert name else old) (@mkHashSet Name _ ⟨fun n => diffHash <| new.constants.map₁.find! n⟩ sz) new.constants.map₁)
  dbg_trace "hashes2 made"
  -- out := out ++ (newnames.sdiff oldnames).toList.map .added
  -- out := out ++ (oldnames.sdiff newnames).toList.map .removed
  -- dbg_trace out.length
  -- dbg_trace (HashSet.sdiff oldhashes newhashes).toList
  let diff := (HashSet.sdiff oldhashes newhashes).toArray
  dbg_trace "diffs made"
  let befores := diff.filterMap (fun (di, bef) => if bef then some (old.constants.map₁.find! di) else none)
  let afters := diff.filterMap (fun (di, bef) => if bef then none else some (new.constants.map₁.find! di))
  -- dbg_trace befores.map ConstantInfo.name
  -- dbg_trace afters.map ConstantInfo.name
  dbg_trace afters.size
  -- -- dbg_trace dm.map (fun (c, rem) => (c.name, rem))
  -- TODO could use hashset here for explained
  let mut out : List Diff := []
  let mut explained := []
  for t in relevantTraits do
    let f := t.hashExcept
    let mut hs : HashMap UInt64 (Name × Bool) := HashMap.empty
    let mut co := true
    for b in befores do
      (hs, co) := hs.insert' (f b) (b.name, true)
      if co then dbg_trace s!"collision, all bets are off {b.name}"
    for a in afters do
      if hs.contains (f a) then
        let (bn, _) := hs.find! (f a)
        let b := old.constants.map₁.find! bn
        if t == name then
          out := .renamed bn a.name false :: out
          explained := (a.name, true) :: (bn, false) :: explained
          continue
        if t == value then
          out := .proofChanged a.name false :: out -- TODO check if proof relevant
          explained := (a.name, true) :: (bn, false) :: explained
          continue
        if t == type then
          out := .typeChanged a.name :: out
          explained := (a.name, true) :: (bn, false) :: explained
          continue
        if t == species then
          out := .speciesChanged a.name (species.val b) (species.val a) :: out
          explained := (a.name, true) :: (bn, false) :: explained
  dbg_trace "comps"
  for a in afters do
    if !(a.name, false) ∈ explained then out := .added a.name :: out
  for b in befores do
    if !(b.name, true) ∈ explained then out := .removed b.name :: out
  pure out

-- TODO some sort of minimization pass might be needed?
-- TODO make this not IO and pass exts in
def diff (old new : Environment) : IO (List Diff) := do
  pure <|
    constantDiffs old new ++
    importDiffs old new ++
    (← extDiffs old new)

end Lean.Environment

-- TODO need some logic for checking lean versions
-- TODO rename to old new
unsafe
def summarizeDiffImports (imports₁ imports₂ : Array Import) (sp₁ sp₂ : SearchPath) : IO Unit := timeit "total" <| do
  let sp ← searchPathRef.get
  searchPathRef.set (sp₁ ++ sp) -- TODO prepend or replace?
  IO.println (← searchPathRef.get)
  let opts := Options.empty
  let trustLevel := 1024 -- TODO actually think about this value
  withImportModules imports₁ opts trustLevel fun env₁ => do
    -- TODO could be really clever here instead of passing search paths around and try and swap the envs in place
    -- to reduce the need for multiple checkouts
    searchPathRef.set (sp₂ ++ sp)
    withImportModules imports₂ opts trustLevel fun env₂ => do
      IO.println <| Diff.summarize (← env₁.diff env₂)

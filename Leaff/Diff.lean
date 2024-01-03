import Lean
import Leaff.Deriving.Optics
import Leaff.Hash
import Leaff.HashSet
import Std.Lean.HashMap


/-!
# Leaff (Lean Diff) core

## Main types
- `Trait` hashable functions of `ConstantInfo`'s and environments used to determine whether two constants are different
- `Diff` the type of a single human understandable difference between two environments


## Design
We consider diffs coming from 3 different sources
- Constants (defs, lemmas, axioms, etc)
- Environment extensions (attributes, docstrings, etc)
- Imports

## TODO
- is there a way to include defeq checking in this?
  for example if a type changes but in a defeq way

-/
open Lean

/--
Traits are functions from `ConstantInfo` to some hashable type `α` that when changed,
results in some meaningful difference between two constants.
For instance the type, name, value of a constant, or whether it is an axiom,
theorem, or definition. -/
structure Trait :=
  α : Type
  val : ConstantInfo → Environment → α
  id : Name
  [ins : Hashable α]
  [ts : ToString α] -- for debugging

instance : BEq Trait where
  beq a b := a.id == b.id
instance : Repr Trait where
  reprPrec a := reprPrec a.id
instance {t : Trait} : Hashable t.α := t.ins
instance {t : Trait} : ToString t.α := t.ts

def Trait.mk' (α : Type) [Hashable α] [ToString α] (val : ConstantInfo → Environment → α) (name : Name := by exact decl_name%) :
  Trait := ⟨α, val, name⟩
namespace Trait
def type : Trait := Trait.mk' Expr (fun c _ => c.type)
def value : Trait := Trait.mk' Expr (fun c _ => c.value!)

def name : Trait := Trait.mk' Name (fun c _ => c.name)
def species : Trait := Trait.mk' Nat fun c _ => (fun
  | .axiomInfo _ => 1 -- "axiom"
  | .defnInfo _ => 2 -- "def"
  | .thmInfo _ => 3 -- "thm"
  | .opaqueInfo _ => 4 -- "opaque"
  | .quotInfo _ => 5 -- "quot"
  | .inductInfo _ => 6 -- "induct"
  | .ctorInfo _ => 7 -- "ctor"
  | .recInfo _ => 8 /-"rec"-/)
  c -- TODO is there a better way to do this

def speciesDescription : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def module : Trait := Trait.mk' Name (fun c e => e.header.moduleNames[(e.getModuleIdxFor? c.name).get!.toNat]!)

-- TODO add universe vars trait? possibly already covered by type
-- TODO maybe def safety as a trait?

def relevantTraits : List Trait := [name, type, value, species, module]
-- TODO maybe find some way to make absence of some traits imply others

@[specialize 1]
def hashExcept (t : Trait) : ConstantInfo → Environment → UInt64 :=
  (relevantTraits.filter (· != t)).foldl (fun h t c e => mixHash (hash (t.val c e)) (h c e)) (fun _ _ => 7) -- TODO 0 or 7...

@[specialize 1]
def hashExceptMany (t : List Trait) : ConstantInfo → Environment → UInt64 :=
  (relevantTraits.filter (!t.contains ·)).foldl (fun h t c e => mixHash (hash (t.val c e)) (h c e)) (fun _ _ => 7) -- TODO 0 or 7...

-- #eval List.sublists [1,2,3]
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
-- TODO maybe isBlackListed from mathlib instead? or something else that removes mk.inj and sizeOf_spec

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
  | proofChanged (name : Name) (isProofRelevant : Bool) -- TODO maybe value changed also for defs
  | typeChanged (name : Name)
  | speciesChanged (name : Name) (fro to : String) -- species is axiom, def, thm, opaque, quot, induct, ctor, rec
  | movedWithinModule (name : Name)
  | extensionEntriesModified (ext : Name) -- TODO maybe delete?
  | docChanged (name : Name) -- TODO how does module/other doc fit in here
  | docAdded (name : Name)
  | docRemoved (name : Name)
  | moduleAdded (name : Name)
  | moduleRemoved (name : Name)
  | moduleRenamed (oldName newName : Name)
  | attributeAdded (attrName name : Name)
  | attributeRemoved (attrName name : Name)
  | attributeChanged (attrName name : Name)
  | directImportAdded (module importName : Name) -- these might be pointless
  | directImportRemoved (module importName : Name)
  | transitiveImportAdded (module importName : Name)
  | transitiveImportRemoved (module importName : Name)
deriving DecidableEq, Repr

-- what combinations? all pairs?
-- renamed and proof modified
-- renamed and moved to module


-- TODO maybe variant "optic"s for isBlah that returns all args of blah not just a bool
-- set_option trace.derive_optics true
derive_optics Diff

namespace Diff
/-- Priority for displaying diffs, lower numbers are more important and should come first in the output.
These should all be distinct as it is what we use to group diffs also -/
def prio : Diff → Nat
  | .added _ => 80
  | .removed _ => 90
  | .renamed _ _ false => 200
  | .renamed _ _ true => 210
  | .movedToModule _ _ _ => 220
  | .movedWithinModule _ => 310
  | .proofChanged _ true => 110 -- if the declaration is proof relevant (i.e. a def) then it is more important
  | .proofChanged _ _ => 250
  | .typeChanged _ => 100
  | .speciesChanged _ _ _ => 140
  | .extensionEntriesModified _ => 150
  | .docChanged _ => 240
  | .docAdded _ => 230
  | .docRemoved _ => 160
  | .moduleAdded _ => 105
  | .moduleRemoved _ => 107
  | .moduleRenamed _ _ => 170
  | .attributeAdded _ _ => 180
  | .attributeRemoved _ _ => 190
  | .attributeChanged _ _ => 260
  | .directImportAdded _ _ => 195
  | .directImportRemoved _ _ => 270
  | .transitiveImportAdded _ _ => 330
  | .transitiveImportRemoved _ _ => 340
-- TODO maybe order this in src to make it clearer

open Std
-- TODO can we make the output richer,
-- colours (sort of handled by diff format in github)
-- links / messagedata in the infoview maybe extracted as links somehow
-- TODO group by module name using @@module@@
open ToFormat in
def summarize (diffs : List Diff) : Format := Id.run do
  if diffs = [] then return "No differences found."
  let mut out : Format := ("Found differences:" : Format).append .line
  let mut diffs := diffs.toArray
  diffs := diffs.qsort (fun a b => a.prio < b.prio)
  for d in diffs do
    out := out.append <| match d with
      | .added name                                     => format s!"+ added {name}\n"
      | .removed name                                   => format s!"- removed {name}\n"
      | .renamed oldName newName true                   => format s!"! renamed {oldName} → {newName} (changed namespace)\n"
      | .renamed oldName newName false                  => format s!"! renamed {oldName} → {newName}\n"
      | .movedToModule name oldModuleName newModuleName => format s!"! moved {name} from {oldModuleName} to {newModuleName}\n"
      | .movedWithinModule name                         => format s!"! moved {name} within module\n"
      | .proofChanged name true                         => format s!"! value changed for {name}\n"
      | .proofChanged name false                        => format s!"! proof changed for {name}\n"
      | .typeChanged name                               => format s!"! type changed for {name}\n"
      | .speciesChanged name fro to                     => format s!"! {name} changed from {fro} to {to}\n"
      | .extensionEntriesModified ext                   => format s!"! extension entry modified for {ext}\n"
      | .docChanged name                                => format s!"! doc modified for {name}\n"
      | .docAdded name                                  => format s!"+ doc added to {name}\n"
      | .docRemoved name                                => format s!"- doc removed from {name}\n"
      | .moduleAdded name                               => format s!"+ module added {name}\n"
      | .moduleRemoved name                             => format s!"- module removed {name}\n"
      | .moduleRenamed oldName newName                  => format s!"! module renamed {oldName} → {newName}\n"
      | .attributeAdded attrName name                   => format s!"+ attribute {attrName} added to {name}\n"
      | .attributeRemoved attrName name                 => format s!"- attribute {attrName} removed from {name}\n"
      | .attributeChanged attrName name                 => format s!"! attribute {attrName} changed for {name}\n"
      | .directImportAdded module importName            => format s!"+ direct import {importName} added to {module}\n"
      | .directImportRemoved module importName          => format s!"- direct import {importName} removed from {module}\n"
      | .transitiveImportAdded module importName        => format s!"+ transitive import {importName} added to {module}\n"
      | .transitiveImportRemoved module importName      => format s!"- transitive import {importName} removed from {module}\n"
  out := out.append (format s!"{diffs.size} differences")
  pure out

end Diff

open Lean Environment

namespace Lean.Environment

open Std

def importDiffs (old new : Environment) : List Diff := Id.run do
  let mut out : List Diff := []
  let mut impHeierOld : RBMap Name (List Name) Name.quickCmp := mkRBMap _ _ _ -- TODO can we reuse any lake internals here?
  let mut impHeierNew : RBMap Name (List Name) Name.quickCmp := mkRBMap _ _ _ -- TODO can we reuse any lake internals here?
  let mut idx := 0
  for mod in old.header.moduleNames do
    impHeierOld := impHeierOld.insert mod (old.header.moduleData[idx]!.imports.map Import.module).toList -- TODO notation for such updates
    idx := idx + 1
  idx := 0
  for mod in new.header.moduleNames do
    impHeierNew := impHeierNew.insert mod (new.header.moduleData[idx]!.imports.map Import.module).toList -- TODO notation for such updates
    idx := idx + 1

  for mod in new.header.moduleNames.toList.diff old.header.moduleNames.toList do
    out := .moduleAdded mod :: out
  for mod in old.header.moduleNames.toList.diff new.header.moduleNames.toList do
    out := .moduleRemoved mod :: out
  for mod in new.header.moduleNames.toList ∩ old.header.moduleNames.toList do
    for add in (impHeierNew.findD mod []).diff (impHeierOld.findD mod []) do
      out := .directImportAdded mod add :: out
    for rem in (impHeierOld.findD mod []).diff (impHeierNew.findD mod []) do
      out := .directImportRemoved mod rem :: out
  -- dbg_trace new.header.moduleData[2]!.imports
  pure out


namespace MapDeclarationExtension

def getImportedState [Inhabited α] (ext : MapDeclarationExtension α) (env : Environment) : NameMap α :=
RBMap.fromArray (ext.toEnvExtension.getState env).importedEntries.flatten Name.quickCmp
  -- match env.getModuleIdxFor? declName with
  -- | some modIdx =>
  --   match (modIdx).binSearch (declName, default) (fun a b => Name.quickLt a.1 b.1) with
  --   | some e => some e.2
  --   | none   => none
  -- | none => (ext.getState env).find? declName

end MapDeclarationExtension
namespace TagDeclarationExtension

def getImportedState (ext : TagDeclarationExtension) (env : Environment) : NameSet :=
RBTree.fromArray (ext.toEnvExtension.getState env).importedEntries.flatten Name.quickCmp

end TagDeclarationExtension

namespace SimpleScopedEnvExtension

def getImportedState [Inhabited σ] (ext : SimpleScopedEnvExtension α σ) (env : Environment) : σ :=
ext.getState env

end SimpleScopedEnvExtension

-- TODO upstream
instance [BEq α] [Hashable α] : ForIn m (SMap α β) (α × β) where
  forIn t init f := do
    forIn t.map₂ (← forIn t.map₁ init f) f

-- TODO upstream
deriving instance BEq for DeclarationRanges

open private docStringExt in Lean.findDocString?

/-- Take the diff between an old and new state of some environment extension,
at the moment we hardcode the extensions we are interested in, as it is not clear how we can go beyond that. -/
def diffExtension (old new : Environment)
    (ext : PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState)
    (renames : NameMap Name)
    (revRenames : NameMap Name) :
    IO (List Diff) := do
  -- let oldSt := ext.getState old
  -- let newSt := ext.getState new
  -- if ptrAddrUnsafe oldSt == ptrAddrUnsafe newSt then return none
  -- dbg_trace oldSt.importedEntries
  -- dbg_trace ext.statsFn oldSt
  -- dbg_trace ext.statsFn newSt
  -- let oldEntries := ext.exportEntriesFn oldSt
  -- let newEntries := ext.exportEntriesFn newSt
  -- dbg_trace oldEntries.size
  -- dbg_trace newEntries.size
  -- dbg_trace ext.name
  let mut out := []
  -- TODO map exts could be way more efficient, we already have sorted arrays of imported entries
  match ext.name with
  | ``Lean.declRangeExt => if false then do -- TODO turn this into a configurable option
      let os := MapDeclarationExtension.getImportedState declRangeExt old
      let ns := MapDeclarationExtension.getImportedState declRangeExt new
      for (a, b) in ns do
        if !a.isInternalDetail then continue
        if os.find? (revRenames.findD a a) != b then
          out := .movedWithinModule a :: out
  | `Lean.docStringExt => do -- Note this is `` not `, as docStringExt is actually private
      let os := MapDeclarationExtension.getImportedState docStringExt old
      let ns := MapDeclarationExtension.getImportedState docStringExt new
      for (a, doc) in ns do
        if a.isInternalDetail then
          continue
        if ¬ os.contains (revRenames.findD a a) then
          out := .docAdded a :: out
        else
          if os.find! (revRenames.findD a a) != doc then
            out := .docChanged a :: out
      for (a, _b) in os do
        if a.isInternalDetail then
          continue
        if ¬ ns.contains (renames.findD a a) then
          out := .docRemoved (renames.findD a a) :: out
  | ``Lean.protectedExt => do
      let os := TagDeclarationExtension.getImportedState protectedExt old
      let ns := TagDeclarationExtension.getImportedState protectedExt new
      for a in ns do
        if a.isInternalDetail then
          continue
        if ¬ os.contains (revRenames.findD a a) then
          out := .attributeAdded `protected a :: out
      for a in os do
        if a.isInternalDetail then
          continue
        if ¬ ns.contains (renames.findD a a) then
          out := .attributeRemoved `protected (renames.findD a a) :: out
  | ``Lean.noncomputableExt => do
      let os := TagDeclarationExtension.getImportedState noncomputableExt old
      let ns := TagDeclarationExtension.getImportedState noncomputableExt new
      for a in ns do
        if a.isInternalDetail then
          continue
        if ¬ os.contains (revRenames.findD a a) then
          out := .attributeAdded `noncomputable a :: out
      for a in os do
        if a.isInternalDetail then
          continue
        if ¬ ns.contains (renames.findD a a) then
          out := .attributeRemoved `noncomputable (renames.findD a a) :: out
  | ``Lean.Meta.globalInstanceExtension => do -- TODO test this, is this the relevant ext?
      let os := Lean.Meta.globalInstanceExtension.getState old
      let ns := Lean.Meta.globalInstanceExtension.getState new
      for (a, _) in ns do
        if a.isInternalDetail then
          continue
        if ¬ os.contains (revRenames.findD a a) then
          out := .attributeAdded `instance a :: out
      for (a, _) in os do
        if a.isInternalDetail then
          continue
        if ¬ ns.contains (renames.findD a a) then
          out := .attributeRemoved `instance (renames.findD a a) :: out
  -- TODO maybe alias
  -- TODO maybe deprecated
  -- TODO maybe implementedBy
  -- TODO maybe export?
  -- | ``Lean.classExtension => do
  --     dbg_trace "class"
  --     dbg_trace (SimplePersistentEnvExtension.getState classExtension new).outParamMap.toList
      -- for (a, b) in SimplePersistentEnvExtension.getState docStringExt new do
      --   if ¬ (SimplePersistentEnvExtension.getState docStringExt old).contains a then
      --     out := .docAdded a :: out
      --   else
      --     if (SimplePersistentEnvExtension.getState docStringExt old).find! a != b then
      --       out := .docChanged a :: out
      -- for (a, _b) in SimplePersistentEnvExtension.getState docStringExt old do
      --   if ¬ (SimplePersistentEnvExtension.getState docStringExt new).contains a then
      --     out := .docRemoved a :: out
  | ``Lean.classExtension => do
      let os := classExtension.getState old
      let ns := classExtension.getState new
      -- for mod in [0:old.header.moduleData.size] do
        -- (ext.getModuleEntries old mod)
      -- IO.println (ext.getModuleEntries old mod).size
      for (a, _b) in ns.outParamMap do
        if a.isInternalDetail then
          continue
        if ¬ os.outParamMap.contains (revRenames.findD a a) then
          out := .attributeAdded `class a :: out
      for (a, _b) in os.outParamMap do
        if a.isInternalDetail then
          continue
        if ¬ ns.outParamMap.contains (renames.findD a a) then
          out := .attributeRemoved `class (renames.findD a a) :: out
  | _ => pure ()
    -- if newEntries.size ≠ oldEntries.size then
    -- -- m!"-- {ext.name} extension: {(newEntries.size - oldEntries.size : Int)} new entries"
    --   out := .extensionEntriesModified ext.name :: out
  return out

-- Which extensions do we care about?
-- all??
-- class (maybe not)
-- instance
-- declrange (maybe as an option)
-- simp
-- computable markers?
-- coe?
-- reducible?
-- protected
-- namespaces?
-- docString, moduleDoc

def extDiffs (old new : Environment) (renames : NameMap Name) : IO (List Diff) := do
  let mut out : List Diff := []
  let mut revRenames := mkNameMap Name
  for (o, n) in renames do
    revRenames := revRenames.insert n o
  -- dbg_trace "exts"
  -- dbg_trace old.extensions.size
  for ext in ← persistentEnvExtensionsRef.get do
    -- dbg_trace ext.name
    out := (← diffExtension old new ext renames revRenames) ++ out
  -- let oldexts := RBSet.ofList (old.extensions Prod.fst) Name.cmp -- TODO maybe quickCmp
  -- let newexts := RBSet.ofList (new.constants.map₁.toList.map Prod.fst) Name.cmp -- TODO maybe quickCmp
  pure out

open Trait

-- TODO do we want definition safety her

def diffHash (c : ConstantInfo) (e : Environment) : UInt64 :=
relevantTraits.foldl (fun h t => mixHash (hash (t.val c e)) h) 13 -- TODO can we get rid of initial value here?
-- mixHash (hash <| module.val c e) <| mixHash (hash <| species.val c e) <| mixHash (hash <| name.val c e) <| mixHash (type.val c e |>.hash) (value.val c e |>.hash)

/-- the list of trait combinations used below -/
def traitCombinations : List (List Trait):= [[name],[value],[name, value],[type],[type, value],[name, value, module],[type, value, module],[species],[module]]
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
  -- TODO recompute this for mathlib! using current ignores
  -- sz is roughly how many non-internal decls we expect, empirically around 1/5th of total
  let sz := max (new.constants.map₁.size / 5) (old.constants.map₁.size / 5)

  -- first we make a hashmap of all decls, hashing with `diffHash`, this should cut the space of "interesting" decls down drastically
  -- TODO reconsider internals, how useful are they
  -- note everything should be in map₁ as we loaded from file
  let oldhashes := HashMap.fold (fun old name const =>
    if const.hasValue && ¬ name.isInternalDetail then old.insert name else old) (@mkHashSet Name _ ⟨fun n => diffHash (old.constants.map₁.find! n) old⟩ sz) old.constants.map₁
  dbg_trace "hashes1 made"
  let newhashes := HashMap.fold (fun old name const =>
    if const.hasValue && ¬ name.isInternalDetail then old.insert name else old) (@mkHashSet Name _ ⟨fun n => diffHash (new.constants.map₁.find! n) new⟩ sz) new.constants.map₁
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
  let mut explained : HashSet (Name × Bool) := HashSet.empty
  for t in traitCombinations.toArray.qsort (fun a b => a.length < b.length) do -- TODO end user should be able to customize which traits
    let f := hashExceptMany t
    let mut hs : HashMap UInt64 (Name × Bool) := HashMap.empty
    let mut co := true
    -- TODO actually check trait differences when found here!?
    for b in befores do
      let a := hs.findEntry? (f b old)
      if !explained.contains (b.name, true) then
        (hs, co) := hs.insert' (f b old) (b.name, true)
        if co then dbg_trace s!"collision when hashing for {t.map Trait.id}, all bets are off {b.name} {a.get!.2}" -- TODO change to err print
    -- dbg_trace s!"{t.id}"
    -- dbg_trace s!"{hs.toList}"
    for a in afters do
      -- if explained.contains (a.name, false) then
      --   continue
      -- dbg_trace a.name
      -- dbg_trace f a new
      -- [name, type, value, species, module] -- TODO check order
      if let some (bn, _) := hs.find? (f a new) then
        if t == [name] then
          out := .renamed bn a.name false :: out -- TODO namespace only?
          explained := explained.insert (a.name, false) |>.insert (bn, true)
          continue
        if t == [value] then
          out := .proofChanged a.name false :: out -- TODO check if proof relevant
          explained := explained.insert (a.name, false) |>.insert (bn, true)
          continue
        if t == [name, value] then
          out := .renamed bn a.name false :: out -- TODO namespace only?
          out := .proofChanged a.name false :: out -- TODO check if proof relevant
          explained := explained.insert (a.name, false) |>.insert (bn, true)
          continue
        if t == [type] then -- this is very unlikely?
          out := .typeChanged a.name :: out
          explained := explained.insert (a.name, false) |>.insert (bn, true)
          continue
        if t == [type, value] then
          out := .typeChanged a.name :: out
          out := .proofChanged a.name false :: out -- TODO check if proof relevant
          explained := explained.insert (a.name, false) |>.insert (bn, true)
        if t == [name, value, module] then
          out := .renamed bn a.name false :: out -- TODO namespace only?
          out := .proofChanged a.name false :: out -- TODO check if proof relevant
          out := .movedToModule a.name old.allImportedModuleNames[(old.const2ModIdx.find! bn).toNat]!
            new.allImportedModuleNames[(new.const2ModIdx.find! a.name).toNat]! :: out
          explained := explained.insert (a.name, false) |>.insert (bn, true)
          continue
        if t == [type, value, module] then
          out := .typeChanged a.name :: out
          out := .proofChanged a.name false :: out -- TODO check if proof relevant
          out := .movedToModule a.name old.allImportedModuleNames[(old.const2ModIdx.find! bn).toNat]!
            new.allImportedModuleNames[(new.const2ModIdx.find! a.name).toNat]! :: out
          explained := explained.insert (a.name, false) |>.insert (bn, true)
          continue
        if t == [species] then
          out := .speciesChanged a.name (speciesDescription (new.constants.map₁.find! bn)) (speciesDescription a) :: out
          explained := explained.insert (a.name, false) |>.insert (bn, true)
          continue
        if t == [module] then
          out := .movedToModule a.name old.allImportedModuleNames[(old.const2ModIdx.find! a.name).toNat]!
            new.allImportedModuleNames[(new.const2ModIdx.find! a.name).toNat]! :: out
          explained := explained.insert (a.name, false) |>.insert (bn, true)
          continue
  for a in afters do
    if !explained.contains (a.name, false) then out := .added a.name :: out
  for b in befores do
    if !explained.contains (b.name, true) then out := .removed b.name :: out
  pure out

/-- for debugging purposes -/
def _root_.Leaff.printHashes (name : Name) : MetaM Unit := do
  let env ← getEnv
  let c := env.find? name
  match c with
  | none => IO.println "not found"
  | some c => do
  let mut out := ""
  for t in relevantTraits do
    IO.println s!"{t.id} {t.val c env}"
    IO.println s!"{hash (t.val c env)}"
    IO.println s!"{t.hashExcept c env}"
  IO.println out

/-- Some diffs are not interesting given then presence of others, so filter the list to remove them.
For instance if a decl is removed, then so will all of its attributes. -/
def minimizeDiffs (diffs : List Diff) : List Diff := Id.run do
  let mut init := diffs
  for diff in init do
    if let .removed n := diff then
      init := init.filter fun
        | .docRemoved m => m != n
        | .attributeRemoved _ m => m != n
        | _ => true
  pure init

def extractRenames (diffs : List Diff) : NameMap Name := Id.run do
  let mut out := mkNameMap Name
  for diff in diffs do
    match diff with
    | .renamed old new _ => out := out.insert old new
    | _ => pure ()
  pure out

-- TODO some sort of minimization pass might be needed?
-- TODO make this not IO and pass exts in
def diff (old new : Environment) : IO (List Diff) := do
  let cd := constantDiffs old new
  let renames := extractRenames cd
  pure <|
    minimizeDiffs <| cd ++
    importDiffs old new ++
    (← extDiffs old new renames)

end Lean.Environment

-- TODO need some logic for checking lean versions agree otherwise we are in a world of hurt
-- TODO rename to old new
unsafe
def summarizeDiffImports (oldImports newImports : Array Import) (old new : SearchPath) : IO Unit := timeit "total" <| do
  searchPathRef.set old
  let opts := Options.empty
  let trustLevel := 1024 -- TODO actually think about this value
  withImportModules oldImports opts trustLevel fun oldEnv => do
    -- TODO could be really clever here instead of passing search paths around and try and swap the envs in place
    -- to reduce the need for multiple checkouts, but that seems compilicated
    searchPathRef.set new
    withImportModules newImports opts trustLevel fun newEnv => do
      IO.println <| Diff.summarize (← oldEnv.diff newEnv)

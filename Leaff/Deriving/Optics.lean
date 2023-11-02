/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers
-/
import Lean
import Lean.Parser
import Lake
import Std.Data.RBMap
open Lean Elab Command Term Tactic
open Lean.Parser.Term
open Lean.Parser.Command
open Lean.Elab.Deriving

namespace String

/-- Make a human-readable string from the given list which is comma-separated but the final comma is
replaced with `conj`. So if `conj := "and"` we get `"A, B, C and D"`.-/
def andList (conj : String := "and") : List String → String
  | [] => ""
  | [x] => x
  | [x,y] => s!"{x} {conj} {y}"
  | head :: tail => s!"{head}, {andList conj tail}"

end String

namespace Lean.Elab.Deriving.Optics

initialize registerTraceClass `derive_optics

-- [todo] this must already exist?
private def Name.modifyHead (f : String → String) : Name → Name
  | Name.str p s => Name.mkStr p (f s)
  | n => n

private def mkDocComment (s : String) : TSyntax `Lean.Parser.Command.docComment :=
  mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ "-/")]

variable {M} [MonadControlT MetaM M] [MonadLiftT MetaM M] [Monad M] [MonadEnv M] [MonadError M]

private structure IndField :=
  (ctor : Name)
  (name : Name)
  (index : Nat)
  /-- Abstracted on params. Use `type.instantiateRev params` to reinstantiate. -/
  (type : Expr)

/-- Maps a field name to the constructors which include that field name and the type.
It's none if the field exists on constructors but the types are incompatible.-/
abbrev FieldCollections := NameMap (Option (NameMap Nat × Expr))

private def getAllFields (decl : Name) : TermElabM (Array IndField) := do
  let indVal ← getConstInfoInduct decl
  indVal.ctors.foldlM (fun acc ctor => do
    let ctorInfo ← Lean.getConstInfoCtor ctor
    Lean.Meta.forallTelescopeReducing ctorInfo.type fun xs _ => do
      let xsdecls ← liftM $ xs.mapM Lean.Meta.getFVarLocalDecl
      let params := xs[:ctorInfo.numParams].toArray
      let fields := xsdecls[ctorInfo.numParams:].toArray
      let field_idxs : Array (Nat × _) := fields.mapIdx fun i x => (i,x)
      field_idxs.foldlM (fun acc (fieldIdx, field) => do
        let fieldName := field.userName
        if fieldName.isNum then
          return acc
        let type := Expr.abstract field.type params
        return acc.push ⟨ctor, fieldName, fieldIdx, type⟩
      ) acc
  ) #[]

/-- Given inductive datatype `decl`, makes a map from field names to a
map from constructor names to field index and type. -/
private def getFieldCollections
  (decl : Name) : TermElabM FieldCollections := do
  let fields ← getAllFields decl
  return fields.foldl add ∅
  where
    add (n : FieldCollections) (f : IndField) : FieldCollections :=
      match n.find? f.name with
      | some x => x.bind (fun (ctors, t) => if t == f.type && not (ctors.contains f.ctor) then some (ctors.insert f.ctor f.index, t) else none) |> n.insert f.name
      | none => n.insert f.name (some (NameMap.insert ∅ f.ctor f.index, f.type))

private def mkAlt (mkRhs : (fieldVars : Array (TSyntax `term)) → TermElabM (TSyntax `term)) (ctor : Name) : TermElabM ((TSyntax `term) × (TSyntax `term)) := do
  let ctorInfo ← Lean.getConstInfoCtor ctor
  let fieldVars ←
    List.range ctorInfo.numFields
    |>.mapM (fun _ => mkIdent <$> mkFreshUserName `a)
  let fieldVars := fieldVars.toArray
  let lhs ← `($(mkIdent ctorInfo.name):ident $fieldVars:term*)
  let rhs ← mkRhs fieldVars
  return (lhs, rhs)

private def mkAlts (ctors : NameMap Nat) (mkRhs : (ctorName : Name) → (fieldIdx : Nat) → (fieldVars : Array (TSyntax `term)) → TermElabM (TSyntax `term)) : TermElabM ((Array (TSyntax `term)) × (Array (TSyntax `term))) := do
  let cs ← ctors.toList.toArray.mapM (fun (n,i) => mkAlt (mkRhs n i) n)
  return Array.unzip cs

private def ctorNameOrList (ctors : NameMap α) : String :=
  ctors.toList |>.map Prod.fst |>.map (fun | Name.str _ x => s!"`{x}`" | _ => "????") |> String.andList "or"

private def isExhaustive (ctors : NameMap α) (indName : Name) : M Bool := do
  let indVal ← getConstInfoInduct indName
  return indVal.ctors.all (fun a => ctors.contains a)

private structure CtorInfo where
  baseName : Name
  indName : Name
  fieldName : Name
  indType : TSyntax `term
  implicitBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder
  fieldType: TSyntax `term
  ctors : NameMap Nat


private def mkGetOptional (c : CtorInfo) : TermElabM (TSyntax `command) := do
  let {baseName, indName, fieldName, indType, implicitBinders, fieldType, ctors} := c
  if (← isExhaustive ctors indName) then
    throwError "expected non-exhautive ctor list"
  let defname := mkIdent <| baseName ++ Name.modifyHead (· ++ "?") fieldName
  let (lhs, rhs) ← mkAlts ctors (fun _ i fvs => `(some $(fvs[i]!)))
  let docstring := mkDocComment <| s!"If the given `{indName}` is a {ctorNameOrList ctors}; returns the value of the `{fieldName}` field, otherwise returns `none`."
  `(
        $docstring:docComment
        def $defname:ident $implicitBinders:bracketedBinder*
          : $indType → Option $fieldType
          $[| $lhs => $rhs]*
          | _ => none
  )

private def mkGetBang (c : CtorInfo) : TermElabM (TSyntax `command) := do
  let {baseName, indName, fieldName, indType, implicitBinders, fieldType, ctors} := c
  if (← isExhaustive ctors indName) then
    throwError "expected non-exhautive ctor list"
  let defname : Name := baseName ++ Name.modifyHead (· ++ "!") fieldName
  let docstring := mkDocComment <| s!"If the given `{indName}` is a {ctorNameOrList ctors},
    returns the value of the `{fieldName}` field, otherwise panics."
  let (lhs, rhs) ← mkAlts ctors (fun _ i fvs => pure fvs[i]!)
  `(
    $docstring:docComment
    def $(mkIdent defname):ident $implicitBinders:bracketedBinder* [Inhabited $fieldType]
      : $indType → $fieldType
      $[| $lhs => $rhs]*
      | x =>
        let n := $(quote (ctorNameOrList ctors))
        panic! s!"expected constructor {n}"
  )

private def mkGet (c : CtorInfo) : TermElabM (TSyntax `command) := do
  let {baseName, indName, fieldName, indType, implicitBinders, fieldType, ctors} := c
  if not (← isExhaustive ctors indName) then
    throwError "expected exhaustive ctor list"
  let defname : Name := baseName ++ fieldName
  let docstring := mkDocComment <| s!"Returns the value of the `{fieldName}` field."
  let (lhs, rhs) ← mkAlts ctors (fun _ i fvs => pure fvs[i]!)
  `(
    $docstring:docComment
    def $(mkIdent defname):ident $implicitBinders:bracketedBinder* [Inhabited $fieldType]
      : $indType → $fieldType
      $[| $lhs => $rhs]*
  )


private def mkWith (c : CtorInfo) : TermElabM (TSyntax `command) := do
  let {baseName, indName, fieldName, indType, implicitBinders, fieldType, ctors} := c
  let defname : Name := baseName ++ Name.modifyHead (fun n => s!"with{n.capitalize}") fieldName
  let x ← mkIdent <$> mkFreshUserName `x
  let (lhs, rhs) ← mkAlts ctors (fun ctorName i fvs => `($(mkIdent ctorName) $(fvs.modify i (fun _ => x)):term*))
  if ← isExhaustive ctors indName then
    `(
      $(mkDocComment <| s!"Replaces the value of the `{fieldName}` field with the given value."):docComment
      def $(mkIdent defname):ident $implicitBinders:bracketedBinder*
        ($x : $fieldType)
        : $indType → $indType
        $[| $lhs => $rhs]*
    )
  else
    `(
      $(mkDocComment <| s!"If the given `{indName}` is a {ctorNameOrList ctors},
          replaces the value of the `{fieldName}` field with the given value.
          Otherwise acts as the identity function."):docComment
      def $(mkIdent defname):ident $implicitBinders:bracketedBinder*
        ($x : $fieldType)
        : $indType → $indType
        $[| $lhs => $rhs]*
        | y => y
    )

private def mkModify (c : CtorInfo) : TermElabM (TSyntax `command) := do
  let {baseName, indName, fieldName, indType, implicitBinders, fieldType, ctors} := c  let defname : Name := baseName ++ Name.modifyHead (fun n => s!"modify{n.capitalize}") fieldName
  let x ← mkIdent <$> mkFreshUserName `visit
  let (lhs, rhs) ← mkAlts ctors (fun ctorName i fvs => do
    let outFields ← fvs.modifyM i (fun q => `(($x <| $q)))
    `($(mkIdent ctorName) $outFields:term*))
  if ← isExhaustive ctors indName then
    `(
      $(mkDocComment <| s!"Modifies the value of the `{fieldName}` field with the given `visit` function."):docComment
      def $(mkIdent defname):ident $implicitBinders:bracketedBinder*
        ($x :$fieldType → $fieldType )
        : $indType → $indType
        $[| $lhs => $rhs]*
    )
  else
    `(
      $(mkDocComment <| s!"If the given `{indName}` is a {ctorNameOrList ctors};
          modifies the value of the `{fieldName}` field with the given `visit` function."):docComment
      def $(mkIdent defname):ident $implicitBinders:bracketedBinder*
        ($x :$fieldType → $fieldType )
        : $indType → $indType
        $[| $lhs => $rhs]*
        | y => y
    )


private def mkModifyM (c : CtorInfo) : TermElabM (TSyntax `command) := do
  let {baseName, indName, fieldName, indType, implicitBinders, fieldType, ctors} := c  let visit ← mkIdent <$> mkFreshUserName `visit
  let x ← mkIdent <$> mkFreshUserName `x
  let (lhs, rhs) ← mkAlts ctors (fun ctorName i fvs => do
    let outFields := fvs.modify i (fun _ => x)
    `((fun $x => $(mkIdent ctorName) $outFields:term*) <$> $visit $(fvs[i]!)))
  let defname : Name := baseName ++ Name.modifyHead (fun n => s!"modifyM{n.capitalize}") fieldName
  if ← (isExhaustive ctors indName) then
    let docstring := mkDocComment <|  s!"Runs the given `visit` function on the `{fieldName}` field."
    `(
      $docstring:docComment
      def $(mkIdent defname):ident
        {M} [Functor M]
        $implicitBinders:bracketedBinder*
        ($visit : $fieldType → M $fieldType)
        :  $indType → M $indType
        $[| $lhs => $rhs]*
    )
  else
    let docstring := mkDocComment <|  s!"Runs the given `visit` function on the `{fieldName}` field if present.
            Performing the pure op if the given `{indName}` is not a {ctorNameOrList ctors}."
    `(
      $docstring:docComment
      def $(mkIdent defname):ident
        {M} [Pure M] [Functor M]
        $implicitBinders:bracketedBinder*
        ($visit : $fieldType → M $fieldType)
        :  $indType → M $indType
        $[| $lhs => $rhs]*
        | y => pure y
    )

private def opticMakers := [mkGet, mkGetOptional, mkGetBang, mkWith, mkModify, mkModifyM]

open Lean.Parser.Term in
private def mkOpticsCore (indVal : InductiveVal) : TermElabM (Array Syntax.Command) :=
  Lean.Meta.forallTelescopeReducing indVal.type fun params _ => do
    let paramDecls ← liftM $ params.mapM Lean.Meta.getFVarLocalDecl
    let paramStx := paramDecls |>.map (fun x => mkIdent x.userName)
    let indType ← `($(mkIdent indVal.name):ident $paramStx:term*)
    let implicitBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinderF) ←
      paramDecls |>.mapM (fun x => do
        let i := mkIdent x.userName
        `(bracketedBinderF|{ $i:ident }))
    let mut cmds := #[]
    let fcs ← getFieldCollections indVal.name
    for (field, cne?) in fcs do
      if let some (ctors, fieldType) := cne? then
        let isEx := if ← isExhaustive ctors indVal.name then "exhaustive" else "non-exhaustive"
        trace[derive_optics] "Deriving optic functions for {isEx} field {field} with constructors {ctors.toList}. "
        let fieldType ← PrettyPrinter.delab <| fieldType.instantiateRev params
        for mk in opticMakers do
          try
            let cmd ← mk {baseName := indVal.name, indName := indVal.name, fieldName := field, indType, implicitBinders, fieldType, ctors}
            cmds := cmds.push cmd
          catch
            | _err => continue
    let fields ← getAllFields indVal.name
    for field in fields do
      let fieldType ← PrettyPrinter.delab <| field.type.instantiateRev params
      let ctors := mkNameMap Nat |>.insert field.ctor field.index
      for mk in opticMakers do
        try
          let cmd ← mk {baseName := field.ctor, indName := indVal.name, fieldName := field.name, indType, implicitBinders, fieldType, ctors}
          cmds := cmds.push cmd
        catch
          | _err => continue
    for ctor in indVal.ctors do
      let na : Name := (Lake.toUpperCamelCase ctor).appendBefore "is"
      let (lhs, rhs) ← mkAlt (fun _ => `(true)) ctor
      let cmd : TSyntax `command ← `(
        -- TODO doc here
        def $(mkIdent na):ident $implicitBinders:bracketedBinder* : $indType → Bool
          | $lhs => $rhs
          | _ => false
      )
      cmds := cmds.push cmd
    return cmds

private def mkOptics (decl : Name) : CommandElabM Unit := do
  if not (← isInductive decl) then
    throwError "{decl} must be an inductive datatype."
  let indVal ← getConstInfoInduct decl
  if isStructure (← getEnv) indVal.name then
    throwError "{decl} structures have projectors already"
  if indVal.numIndices > 0 then
    -- It should be possible to auto-derive some optics using the method as below
    -- But the result is usually confusing so it's better to not support it and
    -- get the users to make bespoke optics.
    throwError "getters and setters derivation not supported for indexed inductive datatype {decl}."
  if indVal.ctors.length <= 1 then
    throwError "single constructor inductive types should be structures."

  let cmds ← liftTermElabM <| mkOpticsCore indVal
  trace[derive_optics] "Created {cmds.size} definitions."
  for cmd in cmds do
    let pp ← liftCoreM $ PrettyPrinter.ppCommand cmd
    trace[derive_optics] "Creating definition:\n{pp}"
    elabCommand cmd

/-- If `T` is an inductive datatype with more than one constructor, `derive_optics T` will create
a set of helper definitions for unpacking the named fields of constructors of `T`.
Let `𝑐` be a constructor of `T` and let `𝑎` be a named field of `𝑐`. `derive_optics T` will produce
the following definitions:
1. `T.𝑐.𝑎? : T → Option α`
2. `T.𝑐.𝑎! : T → α`
3. `T.𝑐.with𝑎 : α → T → T`
4. `T.𝑐.modify𝑎 : (α → α) → T → T`
5. `T.𝑐.modifyM𝑎 : (α → M α) → T → M T`
Each definition includes a docstring describing its behaviour.
Additionally, it will create a non-`𝑐`-named version (`T.𝑎?`, `T.with𝑎`...) where if the same
field name `𝑎` appears on multiple constructors, it will perform the operation on both.
If `𝑎` exists on every constructor, `T.𝑎?` and `T.𝑎!` will be not be
generated, instead `T.𝑎 : T → α` will be.
You can view the generated definitions using `set_option trace.derive_optics true`.
 -/
elab "derive_optics" decl:ident : command =>
  mkOptics decl.getId

end Lean.Elab.Deriving.Optics

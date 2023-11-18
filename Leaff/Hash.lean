import Lean
open Lean Meta Elab Std

def Lean.ConstantInfo.hash (c : ConstantInfo) : UInt64 := mixHash c.type.hash c.value!.hash

def logHashCollisions (e : Environment) : IO Unit := do
  -- let mut hashes := RBSet.empty
  let hashes : Lean.RBMap UInt64 (Array <| Name × Expr) (compareOfLessAndEq · ·) :=
    e.constants.fold (fun o n c => if c.hasValue && ¬ n.isInternal then o.insert c.hash ((o.findD c.hash #[]).push (n, c.value!)) else o) RBMap.empty
  let i : Nat := e.constants.fold (fun o n c => if c.hasValue && ¬ n.isInternal then o + 1 else o) 0
  dbg_trace (toString i)
  dbg_trace (toString hashes.size)
  for o in hashes do
    if o.2.size > 1 && ¬ (o.2.map Prod.snd).all ((o.2.get! 0).2 == ·) then do
      dbg_trace (toString o.1)
      for e in o.2 do
        dbg_trace (toString e.1)

elab "hashcol" : command => do
  let e ← getEnv
  Command.liftCoreM  <| logHashCollisions e

hashcol

#eval UInt64.size
#eval Lean.reservedMacroScope
#eval (Lean.mkConst `Nat).hash
#eval (Lean.Expr.lit <| .natVal 0).hash
#eval (Lean.Expr.lit <| .natVal (2^64)).hash



#eval hash 0
#eval hash (2^64)
#synth Hashable Nat
#check instHashableNat

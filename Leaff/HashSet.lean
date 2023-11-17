import Lean.Data.HashSet
import Std.Data.List.Basic


namespace Array


-- TODO these are copied from lean core but look wrong if stop is too big imo

/-- See comment at `forInUnsafe` -/
@[inline]
unsafe def foldlM₂Unsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → α → m β) (init : β) (asl asr : Array α) (start := 0) (stop := min asl.size asr.size) : m β :=
  let rec @[specialize] fold (i : USize) (stop : USize) (b : β) : m β := do
    if i == stop then
      pure b
    else
      fold (i+1) stop (← f b (asl.uget i lcProof) (asr.uget i lcProof))
  if start < stop then
    if stop ≤ min asl.size asr.size then
      fold (USize.ofNat start) (USize.ofNat stop) init
    else
      pure init
  else
    pure init

/-- Reference implementation for `foldlM`
this is a custom fold over a pair of arrays, assuming their sizes are multiples of each other
-/
@[implemented_by foldlM₂Unsafe]
-- todo could be generalized
def foldlM₂ {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → α → m β) (init : β) (asl asr : Array α) (start := 0) (stop := min asl.size asr.size) : m β :=
  let fold (stop : Nat) (h : stop ≤ min asl.size asr.size) :=
    let rec loop (i : Nat) (j : Nat) (b : β) : m β := do
      if hlt : j < stop then
        match i with
        | 0    => pure b
        | i'+1 =>
          have : j < asl.size := Nat.lt_of_lt_of_le hlt (Nat.le_min.mp h).1
          have : j < asr.size := Nat.lt_of_lt_of_le hlt (Nat.le_min.mp h).2
          loop i' (j+1) (← f b asl[j] asr[j])
      else
        pure b
    loop (stop - start) start init
  if h : stop ≤ min asl.size asr.size then
    fold stop h
  else
    fold (min asl.size asr.size) (Nat.le_refl _)


@[inline]
def foldl₂ {α : Type u} {β : Type v} (f : β → α → α → β) (init : β) (asl asr : Array α) (start := 0) (stop := min asl.size asr.size) : β :=
  Id.run <| asl.foldlM₂ f init asr start stop
end Array


namespace Lean

@[inline] def HashSetImp.sdiff [BEq α] [Hashable α] (l : HashSetImp α) (r : HashSetImp α) : HashSet (α × Bool) :=
  -- if l.numBuckets !=
  --    r.numBuckets then panic! "hash sets have different size" else -- TODO remove this restriction!
  Array.foldl₂ (fun o ll rl => o.insertMany <| (ll.diff rl).map ((·, true)) ++ (rl.diff ll).map ((·, false))) mkHashSet l.2.1 r.2.1

namespace HashSet

@[inline] def sdiff [BEq α] [Hashable α] (l : @HashSet α _ instl) (r : @HashSet α _ instr) : HashSet (α × Bool) :=
  if l.numBuckets !=
     r.numBuckets then panic! "hash sets have different size" else -- TODO remove this restriction!
  (l.1.sdiff r.1)
  -- (l.1.buckets.1.zipWith r.1.buckets.1 fun ll rl => (ll.diff rl).map ((·, true)) ++ (rl.diff ll).map ((·, false))).foldl (fun o li => o.insertMany li) mkHashSet

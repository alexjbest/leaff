import Lean.Data.HashSet
import Std.Data.List.Basic

namespace Lean
namespace HashSet

@[inline] def sdiff [BEq α] [Hashable α] (l : @HashSet α _ instl) (r : @HashSet α _ instr) : HashSet (α × Bool) :=
  if l.numBuckets !=
     r.numBuckets then panic! "hash sets have different size" else -- TODO remove this restriction!
  (l.1.buckets.1.zipWith r.1.buckets.1 fun ll rl => (ll.diff rl).map ((·, true)) ++ (rl.diff ll).map ((·, false))).foldl (fun o li => o.insertMany li) mkHashSet


#eval (mkHashSet.insertMany [3,4,5,6,7,8,9,0,1,4,6,213,2432,435,435,234,12,2]).numBuckets
#eval (mkHashSet.insertMany [3,21343245,213131,4,5,6,7,8,9,0,1,4,6,213,2432,435,435,234,12,2]).numBuckets
#eval (mkHashSet.insertMany [1]).numBuckets
#eval (mkHashSet.insertMany [3,4,5,6,7,8,9,0,1,4,6,213,2432,435,435,234,12,2,12312,12321] |>.sdiff (mkHashSet.insertMany [1,2,3])).toList
#eval (mkHashSet.insertMany [3,4] |>.sdiff (mkHashSet.insertMany [1,2,3])).toList

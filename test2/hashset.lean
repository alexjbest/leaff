import Leaff.HashSet

open Lean
#eval (mkHashSet.insertMany [3,4,5,6,7,8,9,0,1,4,6,213,2432,435,435,234,12,2]).numBuckets
#eval (mkHashSet.insertMany [3,21343245,213131,4,5,6,7,8,9,0,1,4,6,213,2432,435,435,234,12,2]).numBuckets
#eval (mkHashSet.insertMany [1]).numBuckets
#eval (mkHashSet.insertMany [3,4,5,6,7,8,9,0,1,4,6,213,2432,435,435,234,12,2,12312,12321] |>.sdiff (mkHashSet.insertMany [1,2,3])).toList
#eval (mkHashSet.insertMany [3,4] |>.sdiff (mkHashSet.insertMany [1,2,3])).toList

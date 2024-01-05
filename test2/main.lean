import Leaff.Diff
import Lean

open Lean

def sp : SearchPath :=
["."/".lake" /"build"/"lib","."/".lake" /"packages"/"std"/"build"/"lib","/home/alexanderbest/.elan/toolchains/leanprover--lean4---v4.4.0-rc1/lib/lean"]

#eval summarizeDiffImports #[`Std.Classes.RatCast] #[`Std.Data.Rat] sp sp
-- #eval summarizeDiffImports #[`Mathlib] #[`Mathlib] sp₁ sp₂

#eval summarizeDiffImports #[`test.TestA] #[`test.TestB] sp sp

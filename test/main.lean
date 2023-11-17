import Leaff.Diff

open Lean

def sp₁ : SearchPath := "."/"lake-packages"/"mathlib"/"build"/"lib" :: "."/"lake-packages"/"mathlib"/"lake-packages"/"proofwidgets"/"build"/"lib" :: "."/"lake-packages"/"mathlib"/"lake-packages"/"aesop"/"build"/"lib" ::
    "."/"lake-packages"/"mathlib"/"lake-packages"/"Qq"/"build"/"lib" :: "."/"lake-packages"/"mathlib"/"lake-packages"/"std"/"build"/"lib" :: []
def sp₂ : SearchPath := "."/"lake-packages"/"mathlib2"/"build"/"lib" :: "."/"lake-packages"/"mathlib2"/"lake-packages"/"proofwidgets"/"build"/"lib" :: "."/"lake-packages"/"mathlib2"/"lake-packages"/"aesop"/"build"/"lib" ::
      "."/"lake-packages"/"mathlib2"/"lake-packages"/"Qq"/"build"/"lib" :: "."/"lake-packages"/"mathlib2"/"lake-packages"/"std"/"build"/"lib" :: []

#eval summarizeDiffImports #[`Std.Classes.RatCast] #[`Std.Data.Rat] sp₁ sp₂
#eval summarizeDiffImports #[`Mathlib] #[`Mathlib] sp₁ sp₂
-- #[`Std.Data.Fin.Init.Lemmas]


#eval summarizeDiffImports #[`test.TestA] #[`test.TestB] sp₁ sp₂

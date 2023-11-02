/-!
# Basic Git functionality

ideally this would be an actual `libgit` wrapper
-/


namespace Git


open System (FilePath)


def status : IO Unit := do
  let out ← IO.Process.output {
    cmd := "git"
    args := #["status"]
  }
  IO.print out.stdout
  IO.eprintln out.stderr

#eval status

namespace Worktree
def add : String -> IO Unit := sorry

end Worktree
end Git

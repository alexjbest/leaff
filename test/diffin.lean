import Leaff.Diff

diff in
def fo : Type _ := Type _

diff in
def foo := 1
diff in
theorem foo' : 1 = 1 := rfl

-- note that this finds what changed in `section`, so nothing
diff in
section
def asd := 1
end

diff in
/-- ik heb een docstring -/
def aaa : LE Nat := sorry

diff in
attribute [instance] aaa

theorem foo'' : 1 + 1 = 2 := rfl

-- TODO doesn't work
diff in
attribute [simp] foo''

diff in
#eval show Lean.MetaM Unit from do Lean.addDocString `foo "hello"

diffs in
def a := 2
def b := 4
end diffs

def c := 3

diffs in
def a' := 2
def b' := 4

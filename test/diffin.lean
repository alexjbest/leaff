import Leaff.Diff

diff in
def foo := 1
diff in
theorem foo' : 1 = 1 := rfl

-- note that this finds what changed in `section`, so nothing
diff in
section
def asd := 1
end

-- doesn't work right now
diff in
#eval show Lean.MetaM Unit from do Lean.addDocString `foo "hello"

#check foo

diffs in
def a := 2
def b := 4
end diffs

def c := 3

diffs in
def a' := 2
def b' := 4

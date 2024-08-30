
/-- has a doc -/
def a : Nat := 1

def c : Nat := 1
def bloop : Nat := 1

-- theorem sada : Int := 123


structure blah where
  (a b : Nat)

/-- magic number-/
def hasdoc : Int := 123



class blasdf where
  (a b : Nat)


def floo : blasdf := ⟨1, 2⟩



theorem bloop1 : 3 ≠ 9 := by decide



def defToLemma : 1 = 1 := rfl

set_option pp.all true
#print bloop1
-- #eval Leaff.printHashes ``bloop1

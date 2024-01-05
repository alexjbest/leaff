def a : Nat := 1

def b : Nat := 1

-- value changed
def c : Nat := 2

def sada : Int := 123


class blah where
  (a b : Nat)

/-- not so magic number-/
def hasdoc : Int := 123


class blasdf where
  (a b : Nat)

instance floo : blasdf := ⟨1, 2⟩

theorem bloop2 : 3 ≠ 9 := by decide

theorem defToLemma : 1 = 1 := rfl

-- #eval Leaff.printHashes ``bloop2

import SemigroupBasis.Equational

/-! Exact Prop18.1 basis, all optional H/K/T cases expanded. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18
open SemigroupBasis

def lawPower : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0]⟩⟩
def lawLeft : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def lawRight : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def lawSquare : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩
def law04 : Identity Nat := ⟨⟨0, [1, 1, 2, 0]⟩, ⟨0, [2, 1, 1, 0]⟩⟩
def law05 : Identity Nat := ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [2, 0, 1, 0]⟩⟩
def law06 : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 0, 1, 0]⟩⟩
def law07 : Identity Nat := ⟨⟨0, [1, 0, 2, 1]⟩, ⟨0, [1, 0, 2, 1, 0]⟩⟩
def law08 : Identity Nat := ⟨⟨0, [1, 2, 0, 1]⟩, ⟨0, [1, 2, 0, 1, 0]⟩⟩
def law09 : Identity Nat := ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨0, [1, 2, 0, 3, 1, 0]⟩⟩
def law10 : Identity Nat := ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 0, 2, 0]⟩⟩
def law11 : Identity Nat := ⟨⟨0, [1, 2, 0, 3, 2]⟩, ⟨0, [1, 2, 0, 3, 2, 0]⟩⟩
def law12 : Identity Nat := ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 0, 2, 0]⟩⟩
def law13 : Identity Nat := ⟨⟨0, [1, 2, 3, 0, 4, 2]⟩, ⟨0, [1, 2, 3, 0, 4, 2, 0]⟩⟩
def law14 : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 1, 0, 1]⟩⟩
def law15 : Identity Nat := ⟨⟨0, [1, 0, 2, 1]⟩, ⟨1, [0, 1, 0, 2, 1]⟩⟩
def law16 : Identity Nat := ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 1, 2, 0, 1]⟩⟩
def law17 : Identity Nat := ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 1, 2, 0, 3, 1]⟩⟩
def law18 : Identity Nat := ⟨⟨0, [1, 2, 0, 2]⟩, ⟨2, [0, 1, 2, 0, 2]⟩⟩
def law19 : Identity Nat := ⟨⟨0, [1, 2, 0, 3, 2]⟩, ⟨2, [0, 1, 2, 0, 3, 2]⟩⟩
def law20 : Identity Nat := ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨2, [0, 1, 2, 3, 0, 2]⟩⟩
def law21 : Identity Nat := ⟨⟨0, [1, 2, 3, 0, 4, 2]⟩, ⟨2, [0, 1, 2, 3, 0, 4, 2]⟩⟩

def basis : List (Identity Nat) :=
  [lawPower, lawLeft, lawRight, lawSquare, law04, law05, law06, law07, law08, law09, law10, law11, law12, law13, law14, law15, law16, law17, law18, law19, law20, law21]

theorem basis_length : basis.length = 22 := by decide

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.basis_length

end SemigroupBasis.CoRoots.Order6SporadicSection18

import SemigroupBasis.Equational

/-! Exact ordinary identities from Lee-Zhang Propositions17.1 and17.5.
Optional H/K have their empty cases explicitly expanded. The first pair
has raw13 and does NOT assume x^3=x^2; the second pair has raw10.
The literal laws are matched to the frozen actual-oriented input. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17
open SemigroupBasis

namespace C5C6
def lawLeft : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def lawRight : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def lawSquare : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩
def lawSquareH : Identity Nat := ⟨⟨0, [0, 2, 1, 1]⟩, ⟨1, [1, 2, 0, 0]⟩⟩
def lawCubeSquare : Identity Nat := ⟨⟨0, [0, 0, 1, 1]⟩, ⟨1, [1, 0, 0, 0]⟩⟩
def lawCubeSquareH : Identity Nat := ⟨⟨0, [0, 0, 2, 1, 1]⟩, ⟨1, [1, 2, 0, 0, 0]⟩⟩
def lawCubes : Identity Nat := ⟨⟨0, [0, 0, 1, 1, 1]⟩, ⟨1, [1, 1, 0, 0, 0]⟩⟩
def lawCubesH : Identity Nat := ⟨⟨0, [0, 0, 2, 1, 1, 1]⟩, ⟨1, [1, 1, 2, 0, 0, 0]⟩⟩
def lawSpreadRight : Identity Nat := ⟨⟨0, [0, 0, 1, 2, 2]⟩, ⟨0, [0, 0, 1, 0, 0, 0, 2, 2]⟩⟩
def lawSpreadLeft : Identity Nat := ⟨⟨2, [2, 1, 0, 0, 0]⟩, ⟨2, [2, 0, 0, 0, 1, 0, 0, 0]⟩⟩
def lawSlide : Identity Nat := ⟨⟨2, [2, 0, 0, 1, 3, 3]⟩, ⟨2, [2, 1, 0, 0, 3, 3]⟩⟩
def lawSwapBlocks : Identity Nat := ⟨⟨2, [0, 2, 1, 2]⟩, ⟨2, [1, 2, 0, 2]⟩⟩
def lawSwapSquareBlocks : Identity Nat := ⟨⟨2, [2, 0, 3, 3, 1, 4, 4]⟩, ⟨2, [2, 1, 3, 3, 0, 4, 4]⟩⟩

def basis : List (Identity Nat) :=
  [lawLeft, lawRight, lawSquare, lawSquareH, lawCubeSquare, lawCubeSquareH, lawCubes, lawCubesH, lawSpreadRight, lawSpreadLeft, lawSlide, lawSwapBlocks, lawSwapSquareBlocks]

theorem basis_length : basis.length = 13 := by decide
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.basis_length
end C5C6

namespace C10D1
def lawPower : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0]⟩⟩
def lawLeft : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def lawRight : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def lawPermute : Identity Nat := ⟨⟨0, [0, 1, 1, 2, 2]⟩, ⟨1, [1, 0, 0, 2, 2]⟩⟩
def lawInflate : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩
def lawInflateH : Identity Nat := ⟨⟨0, [0, 2, 1, 1]⟩, ⟨1, [0, 0, 2, 1]⟩⟩
def lawSwap : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩
def lawSwapK : Identity Nat := ⟨⟨0, [1, 0, 3, 1]⟩, ⟨1, [0, 0, 3, 1]⟩⟩
def lawSwapH : Identity Nat := ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩
def lawSwapHK : Identity Nat := ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 2, 0, 3, 1]⟩⟩

def basis : List (Identity Nat) :=
  [lawPower, lawLeft, lawRight, lawPermute, lawInflate, lawInflateH, lawSwap, lawSwapK, lawSwapH, lawSwapHK]

theorem basis_length : basis.length = 10 := by decide
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.basis_length
end C10D1

end SemigroupBasis.CoRoots.Order6SporadicSection17

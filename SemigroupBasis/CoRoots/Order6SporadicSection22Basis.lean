import SemigroupBasis.Equational

/-! Lee-Zhang2015, Section22, Propositions22.1 and22.9, pp94 and98.
E5 and E7 have different bases. Each sans-serif H/K is independently
optional; its empty instance is a separate law, never an empty substitution.
Variables x=0, y=1, h=2, k=3. No completeness claim in this module. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection22
open SemigroupBasis

namespace E5

def lawPower : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0]⟩⟩
def lawLeft : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def lawRight : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def lawMove : Identity Nat := ⟨⟨2, [2, 0, 1, 0]⟩, ⟨2, [2, 1, 0, 0]⟩⟩
def lawSwap : Identity Nat := ⟨⟨2, [2, 0, 0, 1, 1]⟩, ⟨2, [2, 1, 1, 0, 0]⟩⟩

def basis : List (Identity Nat) :=
  [lawPower, lawLeft, lawRight, lawMove, lawSwap]

theorem basis_length : basis.length = 5 := by decide

end E5

namespace E7

def lawPower : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0]⟩⟩
def lawPowerH : Identity Nat := ⟨⟨0, [2, 0, 0]⟩, ⟨0, [2, 0]⟩⟩
def lawDelete : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1]⟩⟩
def lawDeleteK : Identity Nat := ⟨⟨0, [1, 3, 0, 1]⟩, ⟨0, [1, 3, 1]⟩⟩
def lawDeleteH : Identity Nat := ⟨⟨0, [2, 1, 0, 1]⟩, ⟨0, [2, 1, 1]⟩⟩
def lawDeleteHK : Identity Nat := ⟨⟨0, [2, 1, 3, 0, 1]⟩, ⟨0, [2, 1, 3, 1]⟩⟩
def lawReverse : Identity Nat := ⟨⟨0, [1, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def lawReverseK : Identity Nat := ⟨⟨0, [1, 3, 1, 0]⟩, ⟨0, [1, 3, 0]⟩⟩
def lawReverseH : Identity Nat := ⟨⟨0, [2, 1, 1, 0]⟩, ⟨0, [2, 1, 0]⟩⟩
def lawReverseHK : Identity Nat := ⟨⟨0, [2, 1, 3, 1, 0]⟩, ⟨0, [2, 1, 3, 0]⟩⟩

def basis : List (Identity Nat) :=
  [lawPower, lawPowerH, lawDelete, lawDeleteK, lawDeleteH, lawDeleteHK, lawReverse, lawReverseK, lawReverseH, lawReverseHK]

theorem basis_length : basis.length = 10 := by decide

end E7

end SemigroupBasis.CoRoots.Order6SporadicSection22


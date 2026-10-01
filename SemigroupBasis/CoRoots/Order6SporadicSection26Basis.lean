import SemigroupBasis.Equational

/-! Lee-Zhang Proposition 26.1, expanded at every optional H/K boundary.
The nine ordered laws are the unchanged actual-direct S6_13527 raw basis.
Variables x=0,y=1,h=2,k/z=3. No completeness premise is introduced. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection26.F7
open SemigroupBasis

def lawPower : Identity Nat := ⟨⟨0,[0,0]⟩,⟨0,[0]⟩⟩
def lawLeft : Identity Nat := ⟨⟨0,[0,2,0]⟩,⟨0,[2,0]⟩⟩
def lawRight : Identity Nat := ⟨⟨0,[2,0,0]⟩,⟨0,[2,0]⟩⟩
def lawMove00 : Identity Nat := ⟨⟨0,[1,0,1]⟩,⟨0,[0,1,1]⟩⟩
def lawMove01 : Identity Nat := ⟨⟨0,[1,3,0,1]⟩,⟨0,[0,1,3,1]⟩⟩
def lawMove10 : Identity Nat := ⟨⟨0,[2,1,0,1]⟩,⟨0,[0,2,1,1]⟩⟩
def lawMove11 : Identity Nat := ⟨⟨0,[2,1,3,0,1]⟩,⟨0,[0,2,1,3,1]⟩⟩
def lawFold0 : Identity Nat := ⟨⟨0,[1,3,1,0]⟩,⟨0,[1,1,3,0]⟩⟩
def lawFold1 : Identity Nat := ⟨⟨0,[2,1,3,1,0]⟩,⟨0,[2,1,1,3,0]⟩⟩

def basis : List (Identity Nat) :=
  [lawPower,lawLeft,lawRight,lawMove00,lawMove01,lawMove10,lawMove11,lawFold0,lawFold1]

theorem basis_length : basis.length = 9 := by decide

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.basis_length
end SemigroupBasis.CoRoots.Order6SporadicSection26.F7

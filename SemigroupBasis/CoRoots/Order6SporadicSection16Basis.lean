import SemigroupBasis.Equational

/-!
Lee and Zhang, *Finite basis problem for semigroups of order six* (2015),
Proposition 16.1, p.49, DOI 10.1112/S1461157014000412.

The six displayed schemes expand to ten ordinary semigroup identities.
Section 2.1 permits each sans-serif H and K to be absent independently;
the empty-context cases below are axioms, not empty-word substitutions.
Variables are x=0, y=1, z=2, h=3, k=4.
This module states the exact basis. It does not assert completeness.
-/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis

def lawPower : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0]⟩⟩
def lawLeft : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def lawRight : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def lawCollect : Identity Nat := ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [0, 1, 2, 2]⟩⟩
def lawAnchor : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
def lawAnchorH : Identity Nat := ⟨⟨0, [0, 3, 1, 1]⟩, ⟨0, [3, 1, 1, 0]⟩⟩
def lawSwap : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
def lawSwapK : Identity Nat := ⟨⟨0, [1, 4, 0, 1]⟩, ⟨0, [1, 4, 1, 0]⟩⟩
def lawSwapH : Identity Nat := ⟨⟨0, [3, 1, 0, 1]⟩, ⟨0, [3, 1, 1, 0]⟩⟩
def lawSwapHK : Identity Nat := ⟨⟨0, [3, 1, 4, 0, 1]⟩, ⟨0, [3, 1, 4, 1, 0]⟩⟩

def basis : List (Identity Nat) :=
  [lawPower, lawLeft, lawRight, lawCollect, lawAnchor, lawAnchorH,
   lawSwap, lawSwapK, lawSwapH, lawSwapHK]

theorem basis_length : basis.length = 10 := by decide

end SemigroupBasis.CoRoots.Order6SporadicSection16

import SemigroupBasis.CoRoots.Order6SporadicSection27F10Uniqueness

/-! Exact frozen raw18, with named bidirectional variable-renaming bridges.
The raw payload was reversed from its historical i94 orientation to the
literal DIRECT F10 / S6_13560 table. This module changes neither law words
nor orientation. SHA256 fe1ca4aee3aa36fbc35cd0a65eabeec041732eea5cb9b30e7bbbe971af02eb51. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection27.F10
open SemigroupBasis

namespace Displayed
def law00 : Identity Nat := ⟨⟨0,[0,0]⟩,⟨0,[0]⟩⟩
def law01 : Identity Nat := ⟨⟨0,[1,0,0]⟩,⟨0,[1,0]⟩⟩
def law02 : Identity Nat := ⟨⟨0,[1,0,1]⟩,⟨0,[1,1,0]⟩⟩
def law03 : Identity Nat := ⟨⟨0,[1,2,0,1]⟩,⟨0,[1,2,1,0]⟩⟩
def law04 : Identity Nat := ⟨⟨0,[1,2,0,2]⟩,⟨0,[1,2,2,0]⟩⟩
def law05 : Identity Nat := ⟨⟨0,[1,2,3,0,2]⟩,⟨0,[1,2,3,2,0]⟩⟩
def law06 : Identity Nat := ⟨⟨0,[1,1,0]⟩,⟨0,[1,0]⟩⟩
def law07 : Identity Nat := ⟨⟨0,[1,2,1,0]⟩,⟨0,[1,2,0]⟩⟩
def law08 : Identity Nat := ⟨⟨0,[1,2,2,0]⟩,⟨0,[1,2,0]⟩⟩
def law09 : Identity Nat := ⟨⟨0,[1,2,3,2,0]⟩,⟨0,[1,2,3,0]⟩⟩
def law10 : Identity Nat := ⟨⟨0,[1,0,1]⟩,⟨0,[1,0,0]⟩⟩
def law11 : Identity Nat := ⟨⟨0,[1,0,2,1]⟩,⟨0,[1,0,2,0]⟩⟩
def law12 : Identity Nat := ⟨⟨0,[1,2,0,1]⟩,⟨0,[1,2,0,0]⟩⟩
def law13 : Identity Nat := ⟨⟨0,[1,2,0,3,1]⟩,⟨0,[1,2,0,3,0]⟩⟩
def law14 : Identity Nat := ⟨⟨0,[1,2,0,2]⟩,⟨0,[1,2,0,0]⟩⟩
def law15 : Identity Nat := ⟨⟨0,[1,2,0,3,2]⟩,⟨0,[1,2,0,3,0]⟩⟩
def law16 : Identity Nat := ⟨⟨0,[1,2,3,0,2]⟩,⟨0,[1,2,3,0,0]⟩⟩
def law17 : Identity Nat := ⟨⟨0,[1,2,3,0,4,2]⟩,⟨0,[1,2,3,0,4,0]⟩⟩

def basis : List (Identity Nat) :=
  [law00,law01,law02,law03,law04,law05,law06,law07,law08,law09,law10,law11,law12,law13,law14,law15,law16,law17]
theorem basis_length : basis.length = 18 := by decide
end Displayed

private def renameFive (a b c d e : Nat) : Nat → Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | n + 5 => n + 5

private theorem renamedLaw {sigma : List (Identity Nat)} (law : Identity Nat)
    (member : law ∈ sigma) (rename : Nat → Nat) :
    Derives sigma (law.lhs.bind (fun x => Word.singleton (rename x)))
      (law.rhs.bind (fun x => Word.singleton (rename x))) :=
  Derives.subst (Derives.fromBasis (e := law) member) (fun x => Word.singleton (rename x))

theorem paperBasis_to_displayedBasis (law : Identity Nat) (member : law ∈ basis) :
    Derives Displayed.basis law.lhs law.rhs := by
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact renamedLaw Displayed.law00 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law01 (by decide) (renameFive 0 2 2 3 4)
  · exact renamedLaw Displayed.law02 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law03 (by decide) (renameFive 0 1 3 3 4)
  · exact renamedLaw Displayed.law04 (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw Displayed.law05 (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw Displayed.law06 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law07 (by decide) (renameFive 0 1 3 3 4)
  · exact renamedLaw Displayed.law08 (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw Displayed.law09 (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw Displayed.law10 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law11 (by decide) (renameFive 0 1 4 3 4)
  · exact renamedLaw Displayed.law12 (by decide) (renameFive 0 1 3 3 4)
  · exact renamedLaw Displayed.law13 (by decide) (renameFive 0 1 3 4 4)
  · exact renamedLaw Displayed.law14 (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw Displayed.law15 (by decide) (renameFive 0 2 1 4 4)
  · exact renamedLaw Displayed.law16 (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw Displayed.law17 (by decide) (renameFive 0 2 1 3 4)

theorem displayedBasis_to_paperBasis (law : Identity Nat) (member : law ∈ Displayed.basis) :
    Derives basis law.lhs law.rhs := by
  simp only [Displayed.basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact renamedLaw lawA_empty (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawA_H (by decide) (renameFive 0 1 1 3 4)
  · exact renamedLaw lawB_empty (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawB_K (by decide) (renameFive 0 1 2 2 4)
  · exact renamedLaw lawB_H (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw lawB_HK (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw lawC_empty (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawC_K (by decide) (renameFive 0 1 2 2 4)
  · exact renamedLaw lawC_H (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw lawC_HK (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw lawD_empty (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawD_T (by decide) (renameFive 0 1 2 3 2)
  · exact renamedLaw lawD_K (by decide) (renameFive 0 1 2 2 4)
  · exact renamedLaw lawD_KT (by decide) (renameFive 0 1 2 2 3)
  · exact renamedLaw lawD_H (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw lawD_HT (by decide) (renameFive 0 2 1 3 3)
  · exact renamedLaw lawD_HK (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw lawD_HKT (by decide) (renameFive 0 2 1 3 4)

theorem displayed_models : Models table.semigroup Displayed.basis := by
  intro law member
  exact (displayedBasis_to_paperBasis law member).sound models

namespace S6_13560

theorem representative_basis : BasisFor table.semigroup Displayed.basis :=
  BasisFor.replace paper_basis displayed_models paperBasis_to_displayedBasis

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis Displayed.basis) :=
  representative_basis.oppositeReversed

end S6_13560
end SemigroupBasis.CoRoots.Order6SporadicSection27.F10

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.Displayed.basis_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.paperBasis_to_displayedBasis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.displayedBasis_to_paperBasis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.displayed_models
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.S6_13560.representative_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.S6_13560.opposite_basis

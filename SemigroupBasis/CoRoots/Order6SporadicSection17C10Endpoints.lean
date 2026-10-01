import SemigroupBasis.CoRoots.Order6SporadicSection17C10WholeConverse

/-! Exact unchanged raw10 and named bidirectional variable-renaming bridges.
Historical i94 opposite orientation was reversed to the literal direct
C10/D1 tables before this encoding. Neither words nor orientations change.
Raw10 SHA 30cdfb9e38b0b89e398017200e05ff1b634135a1fe667be2a2e7a5b69e353f78. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
open SemigroupBasis

namespace Displayed
def law00 : Identity Nat := ⟨⟨0,[0,0]⟩,⟨0,[0]⟩⟩
def law01 : Identity Nat := ⟨⟨0,[0,1,0]⟩,⟨0,[1,0]⟩⟩
def law02 : Identity Nat := ⟨⟨0,[1,0,0]⟩,⟨0,[1,0]⟩⟩
def law03 : Identity Nat := ⟨⟨0,[0,1,1,2,2]⟩,⟨1,[1,0,0,2,2]⟩⟩
def law04 : Identity Nat := ⟨⟨0,[0,1,1]⟩,⟨1,[0,0,1]⟩⟩
def law05 : Identity Nat := ⟨⟨0,[0,1,2,2]⟩,⟨2,[0,0,1,2]⟩⟩
def law06 : Identity Nat := ⟨⟨0,[1,0,1]⟩,⟨1,[0,0,1]⟩⟩
def law07 : Identity Nat := ⟨⟨0,[1,0,2,1]⟩,⟨1,[0,0,2,1]⟩⟩
def law08 : Identity Nat := ⟨⟨0,[1,2,0,1]⟩,⟨1,[0,2,0,1]⟩⟩
def law09 : Identity Nat := ⟨⟨0,[1,2,0,3,1]⟩,⟨1,[0,2,0,3,1]⟩⟩

def basis : List (Identity Nat) :=
  [law00,law01,law02,law03,law04,law05,law06,law07,law08,law09]
theorem basis_length : basis.length = 10 := by decide
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
  simp only [basis,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact renamedLaw Displayed.law00 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law01 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law02 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law03 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law04 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law05 (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw Displayed.law06 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law07 (by decide) (renameFive 0 1 3 3 4)
  · exact renamedLaw Displayed.law08 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law09 (by decide) (renameFive 0 1 2 3 4)

theorem displayedBasis_to_paperBasis (law : Identity Nat) (member : law ∈ Displayed.basis) :
    Derives basis law.lhs law.rhs := by
  simp only [Displayed.basis,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact renamedLaw lawPower (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawLeft (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawRight (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawPermute (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawInflate (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawInflateH (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw lawSwap (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawSwapK (by decide) (renameFive 0 1 2 2 4)
  · exact renamedLaw lawSwapH (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawSwapHK (by decide) (renameFive 0 1 2 3 4)

theorem displayed_models (which : Bool) : Models (Semantics.table which).semigroup Displayed.basis := by
  intro law member
  exact (displayedBasis_to_paperBasis law member).sound (Semantics.models which)

namespace S6_7987

theorem representative_basis : BasisFor table.semigroup Displayed.basis :=
  BasisFor.replace (paper_basis false) (displayed_models false) paperBasis_to_displayedBasis

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis Displayed.basis) :=
  representative_basis.oppositeReversed

end S6_7987

namespace S6_7991

theorem representative_basis : BasisFor table.semigroup Displayed.basis :=
  BasisFor.replace (paper_basis true) (displayed_models true) paperBasis_to_displayedBasis

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis Displayed.basis) :=
  representative_basis.oppositeReversed

end S6_7991

end SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Displayed.basis_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.paperBasis_to_displayedBasis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.displayedBasis_to_paperBasis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.displayed_models
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.S6_7987.representative_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.S6_7987.opposite_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.S6_7991.representative_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.S6_7991.opposite_basis

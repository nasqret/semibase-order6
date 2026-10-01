import SemigroupBasis.CoRoots.Order6SporadicSection26AlphaUniqueness

/-! Both unconditional S6_13527 endpoints. The frozen actual-direct raw9 is
encoded by first-occurrence variable numbering in each whole identity.
Explicit mutual derivability bridges that encoding to the paper's fixed
x/y/h/z numbering; the displayed laws themselves are unchanged. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection26.F7
open SemigroupBasis

namespace Displayed
def law00 : Identity Nat := ⟨⟨0,[0,0]⟩,⟨0,[0]⟩⟩
def law01 : Identity Nat := ⟨⟨0,[0,1,0]⟩,⟨0,[1,0]⟩⟩
def law02 : Identity Nat := ⟨⟨0,[1,0,0]⟩,⟨0,[1,0]⟩⟩
def law03 : Identity Nat := ⟨⟨0,[1,0,1]⟩,⟨0,[0,1,1]⟩⟩
def law04 : Identity Nat := ⟨⟨0,[1,2,0,1]⟩,⟨0,[0,1,2,1]⟩⟩
def law05 : Identity Nat := ⟨⟨0,[1,2,0,2]⟩,⟨0,[0,1,2,2]⟩⟩
def law06 : Identity Nat := ⟨⟨0,[1,2,3,0,2]⟩,⟨0,[0,1,2,3,2]⟩⟩
def law07 : Identity Nat := ⟨⟨0,[1,2,1,0]⟩,⟨0,[1,1,2,0]⟩⟩
def law08 : Identity Nat := ⟨⟨0,[1,2,3,2,0]⟩,⟨0,[1,2,2,3,0]⟩⟩

def basis : List (Identity Nat) :=
  [law00,law01,law02,law03,law04,law05,law06,law07,law08]

theorem basis_length : basis.length = 9 := by decide
end Displayed

private def swap12 : Nat → Nat
  | 1 => 2
  | 2 => 1
  | n => n

private def swap23 : Nat → Nat
  | 2 => 3
  | 3 => 2
  | n => n

private theorem renamedLaw {sigma : List (Identity Nat)} (law : Identity Nat)
    (member : law ∈ sigma) (rename : Nat → Nat) :
    Derives sigma (law.lhs.bind (fun x => Word.singleton (rename x)))
      (law.rhs.bind (fun x => Word.singleton (rename x))) :=
  Derives.subst (Derives.fromBasis (e := law) member) (fun x => Word.singleton (rename x))

theorem paperBasis_to_displayedBasis (law : Identity Nat) (member : law ∈ basis) :
    Derives Displayed.basis law.lhs law.rhs := by
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact renamedLaw Displayed.law00 (by decide) id
  · exact renamedLaw Displayed.law01 (by decide) swap12
  · exact renamedLaw Displayed.law02 (by decide) swap12
  · exact renamedLaw Displayed.law03 (by decide) id
  · exact renamedLaw Displayed.law04 (by decide) swap23
  · exact renamedLaw Displayed.law05 (by decide) swap12
  · exact renamedLaw Displayed.law06 (by decide) swap12
  · exact renamedLaw Displayed.law07 (by decide) swap23
  · exact renamedLaw Displayed.law08 (by decide) swap12

theorem displayedBasis_to_paperBasis (law : Identity Nat) (member : law ∈ Displayed.basis) :
    Derives basis law.lhs law.rhs := by
  simp only [Displayed.basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact renamedLaw lawPower (by decide) id
  · exact renamedLaw lawLeft (by decide) swap12
  · exact renamedLaw lawRight (by decide) swap12
  · exact renamedLaw lawMove00 (by decide) id
  · exact renamedLaw lawMove01 (by decide) swap23
  · exact renamedLaw lawMove10 (by decide) swap12
  · exact renamedLaw lawMove11 (by decide) swap12
  · exact renamedLaw lawFold0 (by decide) swap23
  · exact renamedLaw lawFold1 (by decide) swap12

theorem paper_basis : BasisFor table.semigroup basis := ⟨models, canonical_complete⟩

theorem displayed_models : Models table.semigroup Displayed.basis := by
  intro law member
  exact (displayedBasis_to_paperBasis law member).sound models

namespace S6_13527

theorem representative_basis : BasisFor table.semigroup Displayed.basis :=
  BasisFor.replace paper_basis displayed_models paperBasis_to_displayedBasis

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis Displayed.basis) :=
  representative_basis.oppositeReversed

end S6_13527

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.Displayed.basis_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.paperBasis_to_displayedBasis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.displayedBasis_to_paperBasis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.paper_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.displayed_models
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.S6_13527.representative_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.S6_13527.opposite_basis
end SemigroupBasis.CoRoots.Order6SporadicSection26.F7

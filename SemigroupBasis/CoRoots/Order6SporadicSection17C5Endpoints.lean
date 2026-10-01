import SemigroupBasis.CoRoots.Order6SporadicSection17C5AlphaSemanticComparison
import SemigroupBasis.Opposite

/-! Unconditional C5/C6 endpoints for the exact unchanged ordered raw13.
Displayed variables are numbered in first-occurrence order. Named inverse
singleton-renaming bridges connect that frozen display to the paper encoding.
Raw13 SHA4f6b7c1db87cd5ada6c6bdd90f5a1770791d30736f8472312f30ee25c6c993b3. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem complete (which : Bool) (identity : Identity Nat)
    (valid : identity.SatisfiedBy (Semantics.table which).semigroup) :
    Derives basis identity.lhs identity.rhs := by
  rcases identity with ⟨⟨leftHead,leftTail⟩,⟨rightHead,rightTail⟩⟩
  exact S5_107.ListDerives.toWord
    (Semantics.SameEval.derives (Semantics.sameEval_valid which _ valid))

theorem paper_basis (which : Bool) : BasisFor (Semantics.table which).semigroup basis :=
  ⟨Semantics.models which,complete which⟩

namespace Displayed

def law00 : Identity Nat := ⟨⟨0,[0,1,0]⟩,⟨0,[1,0]⟩⟩
def law01 : Identity Nat := ⟨⟨0,[1,0,0]⟩,⟨0,[1,0]⟩⟩
def law02 : Identity Nat := ⟨⟨0,[0,1,1]⟩,⟨1,[1,0,0]⟩⟩
def law03 : Identity Nat := ⟨⟨0,[0,1,2,2]⟩,⟨2,[2,1,0,0]⟩⟩
def law04 : Identity Nat := ⟨⟨0,[0,0,1,1]⟩,⟨1,[1,0,0,0]⟩⟩
def law05 : Identity Nat := ⟨⟨0,[0,0,1,2,2]⟩,⟨2,[2,1,0,0,0]⟩⟩
def law06 : Identity Nat := ⟨⟨0,[0,0,1,1,1]⟩,⟨1,[1,1,0,0,0]⟩⟩
def law07 : Identity Nat := ⟨⟨0,[0,0,1,2,2,2]⟩,⟨2,[2,2,1,0,0,0]⟩⟩
def law08 : Identity Nat := ⟨⟨0,[0,0,1,2,2]⟩,⟨0,[0,0,1,0,0,0,2,2]⟩⟩
def law09 : Identity Nat := ⟨⟨0,[0,1,2,2,2]⟩,⟨0,[0,2,2,2,1,2,2,2]⟩⟩
def law10 : Identity Nat := ⟨⟨0,[0,1,1,2,3,3]⟩,⟨0,[0,2,1,1,3,3]⟩⟩
def law11 : Identity Nat := ⟨⟨0,[1,0,2,0]⟩,⟨0,[2,0,1,0]⟩⟩
def law12 : Identity Nat := ⟨⟨0,[0,1,2,2,3,4,4]⟩,⟨0,[0,3,2,2,1,4,4]⟩⟩

def basis : List (Identity Nat) :=
  [law00,law01,law02,law03,law04,law05,law06,law07,law08,law09,law10,law11,law12]

theorem basis_length : basis.length = 13 := by decide

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
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact renamedLaw Displayed.law00 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law01 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law02 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law03 (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw Displayed.law04 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law05 (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw Displayed.law06 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law07 (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw Displayed.law08 (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw Displayed.law09 (by decide) (renameFive 2 1 0 3 4)
  · exact renamedLaw Displayed.law10 (by decide) (renameFive 2 0 1 3 4)
  · exact renamedLaw Displayed.law11 (by decide) (renameFive 2 0 1 3 4)
  · exact renamedLaw Displayed.law12 (by decide) (renameFive 2 0 3 1 4)

theorem displayedBasis_to_paperBasis (law : Identity Nat) (member : law ∈ Displayed.basis) :
    Derives basis law.lhs law.rhs := by
  simp only [Displayed.basis,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact renamedLaw lawLeft (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawRight (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawSquare (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawSquareH (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw lawCubeSquare (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawCubeSquareH (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw lawCubes (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawCubesH (by decide) (renameFive 0 2 1 3 4)
  · exact renamedLaw lawSpreadRight (by decide) (renameFive 0 1 2 3 4)
  · exact renamedLaw lawSpreadLeft (by decide) (renameFive 2 1 0 3 4)
  · exact renamedLaw lawSlide (by decide) (renameFive 1 2 0 3 4)
  · exact renamedLaw lawSwapBlocks (by decide) (renameFive 1 2 0 3 4)
  · exact renamedLaw lawSwapSquareBlocks (by decide) (renameFive 1 3 0 2 4)

theorem displayed_models (which : Bool) : Models (Semantics.table which).semigroup Displayed.basis := by
  intro law member
  exact (displayedBasis_to_paperBasis law member).sound (Semantics.models which)

namespace S6_2778

theorem representative_basis : BasisFor table.semigroup Displayed.basis :=
  BasisFor.replace (paper_basis false) (displayed_models false) paperBasis_to_displayedBasis

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis Displayed.basis) :=
  representative_basis.oppositeReversed

end S6_2778

namespace S6_2779

theorem representative_basis : BasisFor table.semigroup Displayed.basis :=
  BasisFor.replace (paper_basis true) (displayed_models true) paperBasis_to_displayedBasis

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis Displayed.basis) :=
  representative_basis.oppositeReversed

end S6_2779

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.complete
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.paper_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Displayed.basis_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.paperBasis_to_displayedBasis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.displayedBasis_to_paperBasis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.displayed_models
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.S6_2778.representative_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.S6_2778.opposite_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.S6_2779.representative_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.S6_2779.opposite_basis

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6

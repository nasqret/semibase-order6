import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Cap303NormalForm
import SemigroupBasis.CoRoots.S5_303Completeness
import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Subdirect

/-! A complete intersection basis for the two actual Cap303 factors.
Only the approved B3 is exported; the stronger S5_303 basis is used to
establish factor soundness, never as a target-class basis. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion

open SemigroupBasis
open SemigroupBasis.Examples
open ApprovedB3BridgesFinite

theorem leftTable_eq : Generated.Catalogue.S3_8.table = commutativeExponentThree := by
  unfold Generated.Catalogue.S3_8.table commutativeExponentThree
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem leftDerivesApproved (e : Identity Nat) (member : e ∈ B3) :
    Derives commutativeExponentThreeBasis e.lhs e.rhs := by
  simp only [B3, Cap303.approvedBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (exponentDerivesTripleContraction (Word.singleton 3)).symm
  · exact exponentDerivesPermutation _ _ (List.Perm.swap 3 2 [3])
  · exact exponentDerivesPermutation _ _ (List.Perm.swap 3 2 [1, 0])

theorem rightDerivesApproved (e : Identity Nat) (member : e ∈ B3) :
    Derives S5_303.basis e.lhs e.rhs := by
  simp only [B3, Cap303.approvedBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact S5_303.derivesPowerExpansion (Word.singleton 3)
  · exact (S5_303.derivesRotate (Word.singleton 3) (Word.singleton 2)).symm
  · exact S5_303.derivesPrefixSwap (Word.singleton 2) (Word.singleton 3)
      (Word.singleton 1) (Word.singleton 0)

theorem leftModels : Models Generated.Catalogue.S3_8.table.semigroup B3 := by
  rw [leftTable_eq]
  intro e member
  exact (leftDerivesApproved e member).sound commutativeExponentThreeBasis_models

theorem rightModels : Models Generated.Catalogue.S5_303.table.semigroup B3 := by
  intro e member
  exact (rightDerivesApproved e member).sound S5_303.models

/-- Actual validity on both frozen factors supplies every unrestricted
normal-form invariant; the converse follows by the new derivation theorem. -/
theorem jointValid_iff_capped_endpoint (e : Identity Nat) :
    (e.SatisfiedBy Generated.Catalogue.S3_8.table.semigroup ∧
      e.SatisfiedBy Generated.Catalogue.S5_303.table.semigroup) ↔
    ((∀ z, min (e.lhs.toList.count z) 2 = min (e.rhs.toList.count z) 2) ∧
      S5_303.SameContentEndpointSignature e.lhs e.rhs) := by
  constructor
  · rintro ⟨leftValid, rightValid⟩
    have countValid : e.SatisfiedBy commutativeExponentThree.semigroup := by
      rw [← leftTable_eq]
      exact leftValid
    exact ⟨exponentValid_capped_count_eq e countValid, S5_303.valid_signature e rightValid⟩
  · rintro ⟨counts, endpoints⟩
    have derivation := derives_of_capped_endpoint counts endpoints
    exact ⟨derivation.sound leftModels, derivation.sound rightModels⟩

theorem intersection :
    IntersectionBasis Generated.Catalogue.S3_8.table.semigroup
      Generated.Catalogue.S5_303.table.semigroup B3 := by
  refine ⟨leftModels, rightModels, ?_⟩
  intro e leftValid rightValid
  have invariants := (jointValid_iff_capped_endpoint e).mp ⟨leftValid, rightValid⟩
  exact derives_of_capped_endpoint invariants.1 invariants.2

theorem basisFor_pair {carrier : Type} {semigroup : Semigroup carrier}
    (pair : SubdirectPair semigroup Generated.Catalogue.S3_8.table.semigroup
      Generated.Catalogue.S5_303.table.semigroup) : BasisFor semigroup B3 :=
  intersection.basisFor pair

example : IntersectionBasis Generated.Catalogue.S3_8.table.semigroup
    Generated.Catalogue.S5_303.table.semigroup
      [Cap303.approvedBasisLaw0, Cap303.approvedBasisLaw1, Cap303.approvedBasisLaw2] :=
  intersection

example : ∀ {carrier : Type} {semigroup : Semigroup carrier},
    SubdirectPair semigroup Generated.Catalogue.S3_8.table.semigroup
      Generated.Catalogue.S5_303.table.semigroup → BasisFor semigroup B3 :=
  basisFor_pair

end SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion

#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.leftTable_eq
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.leftDerivesApproved
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.rightDerivesApproved
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.leftModels
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.rightModels
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.jointValid_iff_capped_endpoint
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.intersection
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.basisFor_pair

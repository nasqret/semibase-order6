import SemigroupBasis.CoRoots.S5_442Invariant
import SemigroupBasis.CoRoots.S5_442ParityEnvelope
import SemigroupBasis.CoRoots.S5_442ParityEnvelopeNormalize
import SemigroupBasis.CoRoots.S5_442ParityEnvelopeRetarget
import SemigroupBasis.CoRoots.S5_442ComponentCompleteness

namespace SemigroupBasis.CoRoots.S5_442

open SemigroupBasis

/-- The global derivational-completeness proposition for the documented
20-law argument. The imported component theorem supplies it constructively
by parity-envelope replay, fixed-endpoint normalization, endpoint retargeting,
and ordered component assembly. -/
def ParityComponentDerivationalCompleteness : Prop :=
  ∀ left right : Word Nat,
    S5_442Invariant.SameParityComponentSignature left right →
      Derives basis left right

/-- Constructive closure of the global parity-component obligation. -/
theorem parityComponentDerivationalCompleteness :
    ParityComponentDerivationalCompleteness :=
  fun _left _right same =>
    derives_of_sameParityComponentSignature same

/-- The representative `BasisFor` theorem is exactly the global
parity-component derivation obligation. -/
theorem basisFor_iff_parityComponentDerivationalCompleteness :
    BasisFor Generated.Catalogue.S5_442.table.semigroup basis ↔
      ParityComponentDerivationalCompleteness := by
  constructor
  · intro complete left right same
    exact complete.2 (⟨left, right⟩ : Identity Nat)
      (valid_of_sameParityComponentSignature
        (⟨left, right⟩ : Identity Nat) same)
  · intro normalize
    refine ⟨catalogueModels, ?_⟩
    intro identity valid
    exact normalize identity.lhs identity.rhs
      (valid_sameParityComponentSignature identity valid)

theorem representative_basis_of_parityComponentDerivationalCompleteness
    (complete : ParityComponentDerivationalCompleteness) :
    BasisFor Generated.Catalogue.S5_442.table.semigroup basis :=
  basisFor_iff_parityComponentDerivationalCompleteness.mpr complete

theorem opposite_basis_of_parityComponentDerivationalCompleteness
    (complete : ParityComponentDerivationalCompleteness) :
    BasisFor Generated.Catalogue.S5_442.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using
    (representative_basis_of_parityComponentDerivationalCompleteness
      complete).oppositeReversed

/-- Unconditional basis theorem for the catalogue representative. -/
theorem representative_basis :
    BasisFor Generated.Catalogue.S5_442.table.semigroup basis :=
  representative_basis_of_parityComponentDerivationalCompleteness
    parityComponentDerivationalCompleteness

/-- Unconditional reversed-basis theorem for the opposite endpoint. -/
theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_442.table.semigroup.opposite
      oppositeBasis :=
  opposite_basis_of_parityComponentDerivationalCompleteness
    parityComponentDerivationalCompleteness

private def swapThreeFour : Fin 5 → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 3

private theorem swapThreeFour_injective :
    Function.Injective swapThreeFour := by
  intro left right
  revert left right
  decide

/-- The audited permutation `[1,2,3,5,4]` identifies `S5_442` with its
opposite. -/
def selfDualEmbedding :
    Embedding Generated.Catalogue.S5_442.table.semigroup.opposite
      Generated.Catalogue.S5_442.table.semigroup where
  toFun := swapThreeFour
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := swapThreeFour_injective

theorem selfDualInvolution (value : Fin 5) :
    selfDualEmbedding.toFun (selfDualEmbedding.toFun value) = value := by
  revert value
  decide

end SemigroupBasis.CoRoots.S5_442

namespace SemigroupBasis.CoRoots.S5_613

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_442

/-- The non-self-dual endpoint has the same exact identity theory and the
same single derivational obstruction. -/
theorem basisFor_iff_parityComponentDerivationalCompleteness :
    BasisFor Generated.Catalogue.S5_613.table.semigroup basis ↔
      ParityComponentDerivationalCompleteness := by
  constructor
  · intro complete left right same
    exact complete.2 (⟨left, right⟩ : Identity Nat)
      (valid_of_sameParityComponentSignature
        (⟨left, right⟩ : Identity Nat) same)
  · intro normalize
    refine ⟨catalogueModels, ?_⟩
    intro identity valid
    exact normalize identity.lhs identity.rhs
      (valid_sameParityComponentSignature identity valid)

theorem representative_basis_of_parityComponentDerivationalCompleteness
    (complete : ParityComponentDerivationalCompleteness) :
    BasisFor Generated.Catalogue.S5_613.table.semigroup basis :=
  basisFor_iff_parityComponentDerivationalCompleteness.mpr complete

/-- Explicit opposite endpoint for the non-self-dual anti-isomorphism
class. -/
theorem opposite_basis_of_parityComponentDerivationalCompleteness
    (complete : ParityComponentDerivationalCompleteness) :
    BasisFor Generated.Catalogue.S5_613.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using
    (representative_basis_of_parityComponentDerivationalCompleteness
      complete).oppositeReversed

/-- Unconditional basis theorem for the non-self-dual representative. -/
theorem representative_basis :
    BasisFor Generated.Catalogue.S5_613.table.semigroup basis :=
  representative_basis_of_parityComponentDerivationalCompleteness
    parityComponentDerivationalCompleteness

/-- Unconditional reversed-basis theorem for its opposite endpoint. -/
theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_613.table.semigroup.opposite
      oppositeBasis :=
  opposite_basis_of_parityComponentDerivationalCompleteness
    parityComponentDerivationalCompleteness

end SemigroupBasis.CoRoots.S5_613

namespace SemigroupBasis.CoRoots.S5_442

open SemigroupBasis

theorem representative_basis_iff_s5_613_representative_basis :
    BasisFor Generated.Catalogue.S5_442.table.semigroup basis ↔
      BasisFor Generated.Catalogue.S5_613.table.semigroup basis := by
  rw [basisFor_iff_parityComponentDerivationalCompleteness,
    SemigroupBasis.CoRoots.S5_613.basisFor_iff_parityComponentDerivationalCompleteness]

end SemigroupBasis.CoRoots.S5_442

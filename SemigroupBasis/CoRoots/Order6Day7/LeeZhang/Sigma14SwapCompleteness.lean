import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14Semantics
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14ProbeInstances
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-! Exact three-class, six-orientation Sigma14 completeness approved by msg-0424.
The representative seed uses the actual S6_2636 table. The other two literal
class endpoints receive genuine unrestricted theory transports through the
reviewed transportNormalizer. C1 quotient representatives are constructed only
from an already-proved intersection basis. No finite screen is a premise.

The Word-key algorithm is total by structural definitions. Canonical confluence
below concerns equational branches and does not assert termination of the
system obtained by orienting every displayed equation. The older raw STOPs
are untouched: this theorem uses exactly the separately approved fourteen laws.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14.Swap

open SemigroupBasis

/-- Generic proof from the finite probe fields, not an assumed completeness field. -/
theorem complete_from_probe {G : Semigroup (Fin 6)} (model : ProbeModel G true)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G) :
    Derives swapBasis identity.lhs identity.rhs :=
  swap_derives_of_key_eq identity.lhs identity.rhs
    (swapNormal_eq_of_equivalent model identity.lhs identity.rhs valid)

def seedNormalizer : IntersectionNormalizer table2636.semigroup table2636.semigroup swapBasis where
  normal := swapNormal
  derives_normal := derives_swapNormal
  normal_eq_of_factor_valid := fun identity valid _ =>
    swapNormal_eq_of_equivalent probe2636 identity.lhs identity.rhs valid

def seedIntersection : IntersectionBasis table2636.semigroup table2636.semigroup swapBasis :=
  seedNormalizer.toIntersectionBasis models2636 models2636

theorem complete2636 : CompletenessStatement table2636 swapBasis :=
  fun identity valid => seedIntersection.complete identity valid valid

noncomputable def seedQuotientNormalizer :
    IntersectionNormalizer table2636.semigroup table2636.semigroup swapBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer seedIntersection

/-- A valid identity of the actual S6_2637 table holds in the actual seed table. -/
theorem theory2637_to_2636 (identity : Identity Nat)
    (valid : identity.SatisfiedBy table2637.semigroup) : identity.SatisfiedBy table2636.semigroup :=
  Derives.sound models2636 (complete_from_probe probe2637 identity valid)

def normalizer2637 : IntersectionNormalizer table2637.semigroup table2637.semigroup swapBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    seedNormalizer (fun _ member => Derives.fromBasis member)
    theory2637_to_2636 theory2637_to_2636

theorem normalizer2637_normal (word : Word Nat) : normalizer2637.normal word = swapNormal word := rfl

def intersection2637 : IntersectionBasis table2637.semigroup table2637.semigroup swapBasis :=
  normalizer2637.toIntersectionBasis models2637 models2637

theorem complete2637 : CompletenessStatement table2637 swapBasis :=
  fun identity valid => intersection2637.complete identity valid valid

/-- A valid identity of the actual S6_2705 table holds in the actual seed table. -/
theorem theory2705_to_2636 (identity : Identity Nat)
    (valid : identity.SatisfiedBy table2705.semigroup) : identity.SatisfiedBy table2636.semigroup :=
  Derives.sound models2636 (complete_from_probe probe2705 identity valid)

def normalizer2705 : IntersectionNormalizer table2705.semigroup table2705.semigroup swapBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    seedNormalizer (fun _ member => Derives.fromBasis member)
    theory2705_to_2636 theory2705_to_2636

theorem normalizer2705_normal (word : Word Nat) : normalizer2705.normal word = swapNormal word := rfl

def intersection2705 : IntersectionBasis table2705.semigroup table2705.semigroup swapBasis :=
  normalizer2705.toIntersectionBasis models2705 models2705

theorem complete2705 : CompletenessStatement table2705 swapBasis :=
  fun identity valid => intersection2705.complete identity valid valid

theorem representative_basis2636 : BasisFor table2636.semigroup swapBasis :=
  ⟨models2636, complete2636⟩

theorem opposite_basis2636 : BasisFor table2636.semigroup.opposite (reversedBasis swapBasis) :=
  representative_basis2636.oppositeReversed

theorem opposite_complete2636 : OppositeCompletenessStatement table2636 swapBasis :=
  opposite_basis2636.2

def oppositeIntersection2636 :
    IntersectionBasis table2636.semigroup.opposite table2636.semigroup.opposite (reversedBasis swapBasis) where
  leftModels := models_opposite2636
  rightModels := models_opposite2636
  complete := fun identity valid _ => opposite_complete2636 identity valid

noncomputable def oppositeNormalizer2636 :
    IntersectionNormalizer table2636.semigroup.opposite table2636.semigroup.opposite (reversedBasis swapBasis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer oppositeIntersection2636

theorem representative_basis2637 : BasisFor table2637.semigroup swapBasis :=
  ⟨models2637, complete2637⟩

theorem opposite_basis2637 : BasisFor table2637.semigroup.opposite (reversedBasis swapBasis) :=
  representative_basis2637.oppositeReversed

theorem opposite_complete2637 : OppositeCompletenessStatement table2637 swapBasis :=
  opposite_basis2637.2

def oppositeIntersection2637 :
    IntersectionBasis table2637.semigroup.opposite table2637.semigroup.opposite (reversedBasis swapBasis) where
  leftModels := models_opposite2637
  rightModels := models_opposite2637
  complete := fun identity valid _ => opposite_complete2637 identity valid

noncomputable def oppositeNormalizer2637 :
    IntersectionNormalizer table2637.semigroup.opposite table2637.semigroup.opposite (reversedBasis swapBasis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer oppositeIntersection2637

theorem representative_basis2705 : BasisFor table2705.semigroup swapBasis :=
  ⟨models2705, complete2705⟩

theorem opposite_basis2705 : BasisFor table2705.semigroup.opposite (reversedBasis swapBasis) :=
  representative_basis2705.oppositeReversed

theorem opposite_complete2705 : OppositeCompletenessStatement table2705 swapBasis :=
  opposite_basis2705.2

def oppositeIntersection2705 :
    IntersectionBasis table2705.semigroup.opposite table2705.semigroup.opposite (reversedBasis swapBasis) where
  leftModels := models_opposite2705
  rightModels := models_opposite2705
  complete := fun identity valid _ => opposite_complete2705 identity valid

noncomputable def oppositeNormalizer2705 :
    IntersectionNormalizer table2705.semigroup.opposite table2705.semigroup.opposite (reversedBasis swapBasis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer oppositeIntersection2705

/-- This is the exact predeclared statement, now approved and proved without weakening. -/
theorem approved_complete : ProposedSwapBothOrientations :=
  ⟨complete2636, opposite_complete2636, complete2637, opposite_complete2637,
    complete2705, opposite_complete2705⟩

theorem equivalent_iff_normal {G : Semigroup (Fin 6)} (model : ProbeModel G true)
    (sound : Models G swapBasis) (left right : Word Nat) :
    Equivalent G left right ↔ swapNormal left = swapNormal right :=
  ⟨swapNormal_eq_of_equivalent model left right,
    fun equal => Derives.sound sound (swap_derives_of_key_eq left right equal)⟩

theorem normal_idempotent (word : Word Nat) : swapNormal (swapNormal word) = swapNormal word :=
  (swapNormal_eq_of_equivalent probe2636 word (swapNormal word)
    (Derives.sound models2636 (derives_swapNormal word))).symm

theorem derives_iff_normal (left right : Word Nat) :
    Derives swapBasis left right ↔ swapNormal left = swapNormal right :=
  ⟨fun derivation => swapNormal_eq_of_equivalent probe2636 left right (Derives.sound models2636 derivation),
    swap_derives_of_key_eq left right⟩

theorem canonical_confluence (word left right : Word Nat)
    (leftBranch : Derives swapBasis word left) (rightBranch : Derives swapBasis word right) :
    swapNormal left = swapNormal right :=
  ((derives_iff_normal word left).mp leftBranch).symm.trans
    ((derives_iff_normal word right).mp rightBranch)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14.Swap

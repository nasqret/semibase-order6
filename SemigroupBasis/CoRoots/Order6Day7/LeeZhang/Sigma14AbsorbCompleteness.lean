import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14Semantics
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14ProbeInstances
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-! Exact three-class, six-orientation Sigma14 completeness approved by msg-0424.
The representative seed uses the actual S6_2676 table. The other two literal
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

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14.Absorb

open SemigroupBasis

/-- Generic proof from the finite probe fields, not an assumed completeness field. -/
theorem complete_from_probe {G : Semigroup (Fin 6)} (model : ProbeModel G false)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G) :
    Derives absorbBasis identity.lhs identity.rhs :=
  absorb_derives_of_key_eq identity.lhs identity.rhs
    (absorbNormal_eq_of_equivalent model identity.lhs identity.rhs valid)

def seedNormalizer : IntersectionNormalizer table2676.semigroup table2676.semigroup absorbBasis where
  normal := absorbNormal
  derives_normal := derives_absorbNormal
  normal_eq_of_factor_valid := fun identity valid _ =>
    absorbNormal_eq_of_equivalent probe2676 identity.lhs identity.rhs valid

def seedIntersection : IntersectionBasis table2676.semigroup table2676.semigroup absorbBasis :=
  seedNormalizer.toIntersectionBasis models2676 models2676

theorem complete2676 : CompletenessStatement table2676 absorbBasis :=
  fun identity valid => seedIntersection.complete identity valid valid

noncomputable def seedQuotientNormalizer :
    IntersectionNormalizer table2676.semigroup table2676.semigroup absorbBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer seedIntersection

/-- A valid identity of the actual S6_2680 table holds in the actual seed table. -/
theorem theory2680_to_2676 (identity : Identity Nat)
    (valid : identity.SatisfiedBy table2680.semigroup) : identity.SatisfiedBy table2676.semigroup :=
  Derives.sound models2676 (complete_from_probe probe2680 identity valid)

def normalizer2680 : IntersectionNormalizer table2680.semigroup table2680.semigroup absorbBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    seedNormalizer (fun _ member => Derives.fromBasis member)
    theory2680_to_2676 theory2680_to_2676

theorem normalizer2680_normal (word : Word Nat) : normalizer2680.normal word = absorbNormal word := rfl

def intersection2680 : IntersectionBasis table2680.semigroup table2680.semigroup absorbBasis :=
  normalizer2680.toIntersectionBasis models2680 models2680

theorem complete2680 : CompletenessStatement table2680 absorbBasis :=
  fun identity valid => intersection2680.complete identity valid valid

/-- A valid identity of the actual S6_2702 table holds in the actual seed table. -/
theorem theory2702_to_2676 (identity : Identity Nat)
    (valid : identity.SatisfiedBy table2702.semigroup) : identity.SatisfiedBy table2676.semigroup :=
  Derives.sound models2676 (complete_from_probe probe2702 identity valid)

def normalizer2702 : IntersectionNormalizer table2702.semigroup table2702.semigroup absorbBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    seedNormalizer (fun _ member => Derives.fromBasis member)
    theory2702_to_2676 theory2702_to_2676

theorem normalizer2702_normal (word : Word Nat) : normalizer2702.normal word = absorbNormal word := rfl

def intersection2702 : IntersectionBasis table2702.semigroup table2702.semigroup absorbBasis :=
  normalizer2702.toIntersectionBasis models2702 models2702

theorem complete2702 : CompletenessStatement table2702 absorbBasis :=
  fun identity valid => intersection2702.complete identity valid valid

theorem representative_basis2676 : BasisFor table2676.semigroup absorbBasis :=
  ⟨models2676, complete2676⟩

theorem opposite_basis2676 : BasisFor table2676.semigroup.opposite (reversedBasis absorbBasis) :=
  representative_basis2676.oppositeReversed

theorem opposite_complete2676 : OppositeCompletenessStatement table2676 absorbBasis :=
  opposite_basis2676.2

def oppositeIntersection2676 :
    IntersectionBasis table2676.semigroup.opposite table2676.semigroup.opposite (reversedBasis absorbBasis) where
  leftModels := models_opposite2676
  rightModels := models_opposite2676
  complete := fun identity valid _ => opposite_complete2676 identity valid

noncomputable def oppositeNormalizer2676 :
    IntersectionNormalizer table2676.semigroup.opposite table2676.semigroup.opposite (reversedBasis absorbBasis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer oppositeIntersection2676

theorem representative_basis2680 : BasisFor table2680.semigroup absorbBasis :=
  ⟨models2680, complete2680⟩

theorem opposite_basis2680 : BasisFor table2680.semigroup.opposite (reversedBasis absorbBasis) :=
  representative_basis2680.oppositeReversed

theorem opposite_complete2680 : OppositeCompletenessStatement table2680 absorbBasis :=
  opposite_basis2680.2

def oppositeIntersection2680 :
    IntersectionBasis table2680.semigroup.opposite table2680.semigroup.opposite (reversedBasis absorbBasis) where
  leftModels := models_opposite2680
  rightModels := models_opposite2680
  complete := fun identity valid _ => opposite_complete2680 identity valid

noncomputable def oppositeNormalizer2680 :
    IntersectionNormalizer table2680.semigroup.opposite table2680.semigroup.opposite (reversedBasis absorbBasis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer oppositeIntersection2680

theorem representative_basis2702 : BasisFor table2702.semigroup absorbBasis :=
  ⟨models2702, complete2702⟩

theorem opposite_basis2702 : BasisFor table2702.semigroup.opposite (reversedBasis absorbBasis) :=
  representative_basis2702.oppositeReversed

theorem opposite_complete2702 : OppositeCompletenessStatement table2702 absorbBasis :=
  opposite_basis2702.2

def oppositeIntersection2702 :
    IntersectionBasis table2702.semigroup.opposite table2702.semigroup.opposite (reversedBasis absorbBasis) where
  leftModels := models_opposite2702
  rightModels := models_opposite2702
  complete := fun identity valid _ => opposite_complete2702 identity valid

noncomputable def oppositeNormalizer2702 :
    IntersectionNormalizer table2702.semigroup.opposite table2702.semigroup.opposite (reversedBasis absorbBasis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer oppositeIntersection2702

/-- This is the exact predeclared statement, now approved and proved without weakening. -/
theorem approved_complete : ProposedAbsorbBothOrientations :=
  ⟨complete2676, opposite_complete2676, complete2680, opposite_complete2680,
    complete2702, opposite_complete2702⟩

theorem equivalent_iff_normal {G : Semigroup (Fin 6)} (model : ProbeModel G false)
    (sound : Models G absorbBasis) (left right : Word Nat) :
    Equivalent G left right ↔ absorbNormal left = absorbNormal right :=
  ⟨absorbNormal_eq_of_equivalent model left right,
    fun equal => Derives.sound sound (absorb_derives_of_key_eq left right equal)⟩

theorem normal_idempotent (word : Word Nat) : absorbNormal (absorbNormal word) = absorbNormal word :=
  (absorbNormal_eq_of_equivalent probe2676 word (absorbNormal word)
    (Derives.sound models2676 (derives_absorbNormal word))).symm

theorem derives_iff_normal (left right : Word Nat) :
    Derives absorbBasis left right ↔ absorbNormal left = absorbNormal right :=
  ⟨fun derivation => absorbNormal_eq_of_equivalent probe2676 left right (Derives.sound models2676 derivation),
    absorb_derives_of_key_eq left right⟩

theorem canonical_confluence (word left right : Word Nat)
    (leftBranch : Derives absorbBasis word left) (rightBranch : Derives absorbBasis word right) :
    absorbNormal left = absorbNormal right :=
  ((derives_iff_normal word left).mp leftBranch).symm.trans
    ((derives_iff_normal word right).mp rightBranch)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14.Absorb

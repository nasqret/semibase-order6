import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708Sigma12Normalization
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708Raw11Obstruction
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-! Unrestricted completeness of exactly the twelve equations approved by
msg-0419. The concrete Word-key algorithm is total by its structural definitions;
its single public stage is sound and idempotent. Canonical confluence here means
that arbitrary equational branches have the same computed normal form, not that
orienting every displayed equation gives a terminating rewrite system.

The eight-law core is a literal subset of the approved twelve laws, not a new
amendment. C1 quotient normality is invoked only after core completeness has
been proved. The reviewed transportNormalizer also exports the concrete normal
word unchanged. No bounded screen or historical completeness field is a premise.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708.Sigma12

open SemigroupBasis

def normalStage : Normalization.Stage (Normalization.derivesSystem coreBasis) (Word Nat) id where
  run := normalForm
  sound := derives_normalForm

theorem runStages_normalForm (word : Word Nat) :
    Normalization.runStages [normalStage] word = normalForm word := rfl

theorem core_derives_of_normalForm_eq (left right : Word Nat)
    (same : normalForm left = normalForm right) : Derives coreBasis left right :=
  Normalization.derives_of_key [normalStage] normalForm id (fun _ => rfl) same

theorem normalForm_idempotent (word : Word Nat) :
    normalForm (normalForm word) = normalForm word :=
  (normalForm_eq_of_equivalent word (normalForm word)
    (Derives.sound core_models (derives_normalForm word))).symm

theorem normalStage_idempotent (word : Word Nat) :
    normalStage.run (normalStage.run word) = normalStage.run word := normalForm_idempotent word

theorem equivalent_iff_normalForm_eq (left right : Word Nat) :
    Equivalent left right ↔ normalForm left = normalForm right :=
  ⟨normalForm_eq_of_equivalent left right,
    fun same => Derives.sound core_models (core_derives_of_normalForm_eq left right same)⟩

theorem normalForm_eq_of_sigma12_derives {left right : Word Nat}
    (derivation : Derives sigma12 left right) : normalForm left = normalForm right :=
  normalForm_eq_of_equivalent left right (Derives.sound models_sigma12 derivation)

theorem canonical_confluence (word left right : Word Nat)
    (leftBranch : Derives sigma12 word left) (rightBranch : Derives sigma12 word right) :
    normalForm left = normalForm right :=
  (normalForm_eq_of_sigma12_derives leftBranch).symm.trans
    (normalForm_eq_of_sigma12_derives rightBranch)

theorem core_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives coreBasis identity.lhs identity.rhs :=
  core_derives_of_normalForm_eq identity.lhs identity.rhs
    (normalForm_eq_of_equivalent identity.lhs identity.rhs valid)

theorem core_representative_basis : BasisFor table.semigroup coreBasis := ⟨core_models, core_complete⟩

theorem sigma12_laws_derive_from_core (identity : Identity Nat) (member : identity ∈ sigma12) :
    Derives coreBasis identity.lhs identity.rhs := core_complete identity (models_sigma12 identity member)

def coreIntersection : IntersectionBasis table.semigroup table.semigroup coreBasis where
  leftModels := core_models
  rightModels := core_models
  complete := fun identity valid _ => core_complete identity valid

noncomputable def coreNormalizer : IntersectionNormalizer table.semigroup table.semigroup coreBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer coreIntersection

def coreConcreteNormalizer : IntersectionNormalizer table.semigroup table.semigroup coreBasis where
  normal := normalForm
  derives_normal := derives_normalForm
  normal_eq_of_factor_valid := fun identity valid _ =>
    normalForm_eq_of_equivalent identity.lhs identity.rhs valid

def normalizer : IntersectionNormalizer table.semigroup table.semigroup sigma12 :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    coreConcreteNormalizer (fun identity member => Derives.fromBasis (core_subset_sigma12 identity member))
    (fun _ valid => valid) (fun _ valid => valid)

theorem normalizer_normal (word : Word Nat) : normalizer.normal word = normalForm word := rfl

noncomputable def quotientNormalizer : IntersectionNormalizer table.semigroup table.semigroup sigma12 :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    coreNormalizer (fun identity member => Derives.fromBasis (core_subset_sigma12 identity member))
    (fun _ valid => valid) (fun _ valid => valid)

def diagonalIntersection : IntersectionBasis table.semigroup table.semigroup sigma12 :=
  normalizer.toIntersectionBasis models_sigma12 models_sigma12

theorem complete (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives sigma12 identity.lhs identity.rhs := diagonalIntersection.complete identity valid valid

theorem approved_complete : ProposedSigma12Completeness := complete

theorem derives_sigma12_iff_normalForm_eq (left right : Word Nat) :
    Derives sigma12 left right ↔ normalForm left = normalForm right :=
  ⟨normalForm_eq_of_sigma12_derives,
    fun same => complete ⟨left, right⟩ ((equivalent_iff_normalForm_eq left right).2 same)⟩

theorem representative_basis : BasisFor table.semigroup sigma12 := ⟨models_sigma12, complete⟩

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis sigma12) :=
  representative_basis.oppositeReversed

def oppositeIntersection : IntersectionBasis table.semigroup.opposite table.semigroup.opposite
    (reversedBasis sigma12) where
  leftModels := models_opposite_sigma12
  rightModels := models_opposite_sigma12
  complete := fun identity valid _ => opposite_basis.2 identity valid

noncomputable def oppositeNormalizer :
    IntersectionNormalizer table.semigroup.opposite table.semigroup.opposite (reversedBasis sigma12) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer oppositeIntersection

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708.Sigma12

import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5441Semantics
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-!
# Unconditional raw11 completeness through a proved three-law core

The internal core is literally laws04,05,08 of the unchanged raw11.
The arbitrary-word separator proof closes that core first. Only then does
the C1 quotient interface produce a normalizer, and the shared reviewed
transportNormalizer transports it to all eleven displayed laws.
The internal core is not an amended target or an additional completed system.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5441

open SemigroupBasis

def coreBasis : List (Identity Nat) := [law04, law05, law08]

theorem coreBasis_length : coreBasis.length = 3 := rfl

theorem core_subset_raw (identity : Identity Nat) (member : identity ∈ coreBasis) : identity ∈ basis := by
  simp only [coreBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [basis]

private def substituteThree (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

def core_calculus : PrefixTwoEndpoint.Rules coreBasis where
  prefixIdempotence := by
    intro x y z
    have primitive : Derives coreBasis law04.lhs law04.rhs := Derives.fromBasis (by simp [coreBasis])
    simpa [law04, substituteThree, Word.bind, Word.append, Word.append_assoc] using
      primitive.subst (substituteThree x y z)
  terminalSwitch := by
    intro x y
    have primitive : Derives coreBasis law05.lhs law05.rhs := Derives.fromBasis (by simp [coreBasis])
    simpa [law05, substituteThree, Word.bind, Word.append, Word.append_assoc] using
      primitive.subst (substituteThree x y y)
  terminalSwap := by
    intro x y
    have primitive : Derives coreBasis law08.lhs law08.rhs := Derives.fromBasis (by simp [coreBasis])
    simpa [law08, substituteThree, Word.bind, Word.append, Word.append_assoc] using
      primitive.subst (substituteThree x y y)

theorem derives_of_probeEquivalent_for (derivationBasis : List (Identity Nat))
    (rules : PrefixTwoEndpoint.Rules derivationBasis) (left right : Word Nat)
    (same : ProbeEquivalent left right) : Derives derivationBasis left right := by
  rcases PrefixTwoEndpoint.existsSingletonOrFrame left with ⟨leftLetter, rfl⟩ |
    ⟨leftFront, leftPenultimate, leftLast, rfl⟩
  · rcases PrefixTwoEndpoint.existsSingletonOrFrame right with ⟨rightLetter, rfl⟩ |
      ⟨rightFront, rightPenultimate, rightLast, rfl⟩
    · have equal := singleton_eq_of_probeEquivalent leftLetter rightLetter same
      subst rightLetter
      exact Derives.refl _
    · exact False.elim (singleton_not_probeEquivalent_frame leftLetter rightPenultimate rightLast rightFront same)
  · rcases PrefixTwoEndpoint.existsSingletonOrFrame right with ⟨rightLetter, rfl⟩ |
      ⟨rightFront, rightPenultimate, rightLast, rfl⟩
    · exact False.elim (singleton_not_probeEquivalent_frame rightLetter leftPenultimate leftLast leftFront same.symm)
    · exact derivesFramesOfProbeEquivalentWith derivationBasis rules leftFront rightFront
        leftPenultimate leftLast rightPenultimate rightLast same

/-- The three-law core is proved for every identity, not inferred from an HFB label. -/
theorem core_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives coreBasis identity.lhs identity.rhs :=
  derives_of_probeEquivalent_for coreBasis core_calculus identity.lhs identity.rhs
    (valid_probeEquivalent valid)

theorem core_models : Models table.semigroup coreBasis :=
  fun identity member => models_raw identity (core_subset_raw identity member)

theorem core_representative_basis : BasisFor table.semigroup coreBasis := ⟨core_models, core_complete⟩

theorem raw_laws_derive_from_core (identity : Identity Nat) (member : identity ∈ basis) :
    Derives coreBasis identity.lhs identity.rhs :=
  core_complete identity (models_raw identity member)

/-- Diagonal on the actual table twice, not an invented factorization. -/
def coreIntersection : IntersectionBasis table.semigroup table.semigroup coreBasis where
  leftModels := core_models
  rightModels := core_models
  complete := fun identity valid _ => core_complete identity valid

noncomputable def coreNormalizer : IntersectionNormalizer table.semigroup table.semigroup coreBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    coreIntersection

/-- Genuine displayed-basis transport from the proved core to the exact raw11. -/
noncomputable def normalizer : IntersectionNormalizer table.semigroup table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    coreNormalizer
    (fun identity member => Derives.fromBasis (core_subset_raw identity member))
    (fun _ valid => valid) (fun _ valid => valid)

def diagonalIntersection : IntersectionBasis table.semigroup table.semigroup basis :=
  normalizer.toIntersectionBasis models_raw models_raw

theorem complete (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  diagonalIntersection.complete identity valid valid

theorem derives_of_probeEquivalent (left right : Word Nat) (same : ProbeEquivalent left right) :
    Derives basis left right :=
  derives_of_probeEquivalent_for basis calculus left right same

theorem valid_iff_probeEquivalent (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ ProbeEquivalent identity.lhs identity.rhs := by
  constructor
  · exact valid_probeEquivalent
  · intro same valuation
    exact Derives.sound models_raw (derives_of_probeEquivalent identity.lhs identity.rhs same) valuation

theorem representative_basis : BasisFor table.semigroup basis := ⟨models_raw, complete⟩

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

def oppositeIntersection : IntersectionBasis table.semigroup.opposite table.semigroup.opposite (reversedBasis basis) where
  leftModels := models_opposite_raw
  rightModels := models_opposite_raw
  complete := fun identity valid _ => opposite_basis.2 identity valid

noncomputable def oppositeNormalizer :
    IntersectionNormalizer table.semigroup.opposite table.semigroup.opposite (reversedBasis basis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    oppositeIntersection

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5441

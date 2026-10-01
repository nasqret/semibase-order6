import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2664Semantics
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-!
# Unconditional exact raw12 completeness and normalizers for S6_2664

All words are decomposed literally into a singleton or a frame. The
unrestricted separators and shared derivation calculus close that exact
presentation. C1 quotient normalization is used only after completeness;
transportNormalizer uses an explicit self-duality map of the actual table.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2664

open SemigroupBasis

/-- No short-word preparation: in particular, `xx` remains distinct from `xxx`. -/
theorem derives_of_probeEquivalent (left right : Word Nat)
    (same : ProbeEquivalent left right) : Derives basis left right := by
  rcases InteriorEndpoint.existsSingletonOrFrame left with ⟨leftLetter, rfl⟩ |
    ⟨leftFirst, leftInterior, leftLast, rfl⟩
  · rcases InteriorEndpoint.existsSingletonOrFrame right with ⟨rightLetter, rfl⟩ |
      ⟨rightFirst, rightInterior, rightLast, rfl⟩
    · have equal := singleton_eq_of_probeEquivalent leftLetter rightLetter same
      subst rightLetter
      exact Derives.refl _
    · exact False.elim (singleton_not_probeEquivalent_frame leftLetter rightFirst rightLast rightInterior same)
  · rcases InteriorEndpoint.existsSingletonOrFrame right with ⟨rightLetter, rfl⟩ |
      ⟨rightFirst, rightInterior, rightLast, rfl⟩
    · exact False.elim (singleton_not_probeEquivalent_frame rightLetter leftFirst leftLast leftInterior
        (fun selected => (same selected).symm))
    · exact derivesFramesOfProbeEquivalent leftFirst leftLast rightFirst rightLast
        leftInterior rightInterior same

/-- Every valid identity, with unrestricted variables and endpoint lengths. -/
theorem complete (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derives_of_probeEquivalent identity.lhs identity.rhs
    (fun selected => valid (probeValuation selected))

theorem valid_iff_probeEquivalent (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ ProbeEquivalent identity.lhs identity.rhs := by
  constructor
  · exact fun valid selected => valid (probeValuation selected)
  · intro same valuation
    exact Derives.sound models (derives_of_probeEquivalent identity.lhs identity.rhs same) valuation

/-- The diagonal interface uses the same actual table twice, not a factorization. -/
def diagonalIntersection : IntersectionBasis table.semigroup table.semigroup basis where
  leftModels := models
  rightModels := models
  complete := fun identity leftValid _ => complete identity leftValid

noncomputable def normalizer : IntersectionNormalizer table.semigroup table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    diagonalIntersection

theorem representative_basis : BasisFor table.semigroup basis := ⟨models, complete⟩

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

/-- The exact anti-isomorphism swaps zero-based catalogue elements2 and3. -/
def selfDualMap (value : Fin 6) : Fin 6 :=
  if value = 2 then 3 else if value = 3 then 2 else value

def toOpposite : SplitSurjection table.semigroup table.semigroup.opposite where
  toFun := selfDualMap
  map_mul := by decide
  preimage := selfDualMap
  right_inverse := by intro value; exact by decide +revert

def fromOpposite : SplitSurjection table.semigroup.opposite table.semigroup where
  toFun := selfDualMap
  map_mul := by decide
  preimage := selfDualMap
  right_inverse := by intro value; exact by decide +revert

theorem oppositeTheory (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup.opposite ↔ identity.SatisfiedBy table.semigroup :=
  ⟨fromOpposite.pushforwardIdentity identity, toOpposite.pushforwardIdentity identity⟩

/-- Reuse the kernel-green shared transport with genuine theory implications. -/
noncomputable def oppositeRawNormalizer :
    IntersectionNormalizer table.semigroup.opposite table.semigroup.opposite basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer
    (fun _ member => Derives.fromBasis member)
    (fun identity valid => (oppositeTheory identity).1 valid)
    (fun identity valid => (oppositeTheory identity).1 valid)

/-- This unreversed-raw variant is the same opposite orientation, not another class. -/
theorem opposite_raw_basis : BasisFor table.semigroup.opposite basis := by
  have oppositeModels : Models table.semigroup.opposite basis := by
    intro identity member
    exact toOpposite.pushforwardIdentity identity (models identity member)
  have intersection := oppositeRawNormalizer.toIntersectionBasis oppositeModels oppositeModels
  exact ⟨oppositeModels, fun identity valid => intersection.complete identity valid valid⟩

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2664

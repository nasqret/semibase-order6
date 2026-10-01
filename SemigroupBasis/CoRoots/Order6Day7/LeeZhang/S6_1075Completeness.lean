import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_1075Semantics
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-!
# Unconditional raw10 basis and normalizer for S6_1075

The six-state separators and the arbitrary-length interior/endpoint
derivations close the exact displayed presentation. The existing C1
quotient-normalizer construction is used only AFTER completeness has been
proved. Its diagonal pair is the same actual table twice, not a newly
asserted lower-order factorization. The shared transportNormalizer is then
reused across an explicitly proved self-duality map.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_1075

open SemigroupBasis

/-- All words with the same separating profile are derivably equal.
This includes both singleton cases and the prepared `xx` boundary. -/
theorem derives_of_probeEquivalent (left right : Word Nat)
    (same : ProbeEquivalent left right) : Derives basis left right := by
  have preparedSame {leftPrepared rightPrepared : Word Nat}
      (leftDerivation : Derives basis left leftPrepared)
      (rightDerivation : Derives basis right rightPrepared) :
      ProbeEquivalent leftPrepared rightPrepared := by
    intro selected
    exact (Derives.sound models leftDerivation (probeValuation selected)).symm.trans
      ((same selected).trans (Derives.sound models rightDerivation (probeValuation selected)))
  rcases existsPrepared left with ⟨leftLetter, leftDerivation⟩ |
    ⟨leftFirst, leftInterior, leftLast, leftRegular, leftDerivation⟩
  · rcases existsPrepared right with ⟨rightLetter, rightDerivation⟩ |
      ⟨rightFirst, rightInterior, rightLast, rightRegular, rightDerivation⟩
    · have equal := singleton_eq_of_probeEquivalent leftLetter rightLetter
        (preparedSame leftDerivation rightDerivation)
      subst rightLetter
      exact leftDerivation.trans rightDerivation.symm
    · exact False.elim (singleton_not_probeEquivalent_frame leftLetter rightFirst rightLast
        rightInterior rightRegular (preparedSame leftDerivation rightDerivation))
  · rcases existsPrepared right with ⟨rightLetter, rightDerivation⟩ |
      ⟨rightFirst, rightInterior, rightLast, rightRegular, rightDerivation⟩
    · exact False.elim (singleton_not_probeEquivalent_frame rightLetter leftFirst leftLast
        leftInterior leftRegular
        (fun selected => (preparedSame leftDerivation rightDerivation selected).symm))
    · have middle := derivesFramesOfProbeEquivalent leftFirst leftLast rightFirst rightLast
        leftInterior rightInterior leftRegular rightRegular
        (preparedSame leftDerivation rightDerivation)
      exact leftDerivation.trans (middle.trans rightDerivation.symm)

/-- Unrestricted completeness for exactly the unchanged ten displayed laws. -/
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

/-- A proved diagonal theory intersection for the C1 interface, not a factor-map claim. -/
def diagonalIntersection : IntersectionBasis table.semigroup table.semigroup basis where
  leftModels := models
  rightModels := models
  complete := fun identity leftValid _ => complete identity leftValid

/-- C1's proof-producing normalizer is used only after the unrestricted theorem. -/
noncomputable def normalizer : IntersectionNormalizer table.semigroup table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    diagonalIntersection

theorem representative_basis : BasisFor table.semigroup basis := ⟨models, complete⟩

/-- The opposite endpoint uses the literally reversed ordered basis. -/
theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

/-- The exact self-duality relabelling swaps zero-based catalogue elements 2 and 4. -/
def selfDualMap (value : Fin 6) : Fin 6 :=
  if value = 2 then 4 else if value = 4 then 2 else value

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

/-- Reuse the kernel-green shared transport with actual unrestricted theory
implications from the checked self-duality, not with a finite projection. -/
noncomputable def oppositeRawNormalizer :
    IntersectionNormalizer table.semigroup.opposite table.semigroup.opposite basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer
    (fun _ member => Derives.fromBasis member)
    (fun identity valid => (oppositeTheory identity).1 valid)
    (fun identity valid => (oppositeTheory identity).1 valid)

/-- Self-duality also permits the unreversed raw10 basis on the opposite;
this is the same orientation, not an additional class or census increment. -/
theorem opposite_raw_basis : BasisFor table.semigroup.opposite basis := by
  have oppositeModels : Models table.semigroup.opposite basis := by
    intro identity member
    exact toOpposite.pushforwardIdentity identity (models identity member)
  have intersection := oppositeRawNormalizer.toIntersectionBasis oppositeModels oppositeModels
  exact ⟨oppositeModels, fun identity valid => intersection.complete identity valid valid⟩

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_1075

import SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLawNormal
import SemigroupBasis.Normalization.OneLocalFordLord
import SemigroupBasis.Opposite

/-!
# Shared unrestricted reach for the capped-at-two Ford/Lord family

The seven-law normalizer already proves unrestricted completeness for words
with the same first-occurrence order, last-occurrence order, and
multiplicities capped at two.  This module exposes that result at the
`OneLocalFordLord.Profile 2 1` boundary and transports it to any displayed
system deriving the seven laws.

The result is pairwise reach over `Nat` words, not a bounded certificate:
equal profiles imply a `Derives` proof directly.  Consequently the joint
factor obligation needs only profile necessity and displayed-law derivations;
there is no per-obligation `ReachPlan`.
-/

namespace SemigroupBasis
namespace OneLocalFordLord
namespace SharedReach

universe u v w x

open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_1089

/-- The exact syntactic interface required by the shared normalizer.

The seven laws may be literal members of `basis` or derived consequences of
it.  Keeping derivability, rather than membership, as the interface makes the
transport theorem usable by both displayed supersets and future compressed
presentations. -/
structure Laws (basis : List (Identity Nat)) : Prop where
  sourceAxiomsDerive :
    ∀ identity : Identity Nat,
      identity ∈
          SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.basis →
        Derives basis identity.lhs identity.rhs

namespace Laws

/-- Decidable finite check used by exact displayed systems. -/
def containsSharedBasis (basis : List (Identity Nat)) : Bool :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.basis.all
    (fun identity => decide (identity ∈ basis))

/-- Build the shared-law interface when every seven-law axiom occurs literally
in the displayed system. -/
def ofSubset {basis : List (Identity Nat)}
    (subset :
      ∀ identity : Identity Nat,
        identity ∈
            SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.basis →
          identity ∈ basis) :
    Laws basis where
  sourceAxiomsDerive := fun identity member =>
    Derives.fromBasis (subset identity member)

/-- Turn the finite inclusion check into derivations of all seven source
axioms.  This keeps displayed-system instances as one kernel-reduced check. -/
def ofContainsSharedBasis {basis : List (Identity Nat)}
    (included : containsSharedBasis basis = true) :
    Laws basis where
  sourceAxiomsDerive := fun identity member =>
    Derives.fromBasis <| of_decide_eq_true <|
      (List.all_eq_true.mp included) identity member

end Laws

/-- Equality of first-occurrence sequences gives unrestricted derivability in
the complete three-element left-regular-band presentation. -/
theorem lrbDerives_of_ford_eq
    {left right : Word Nat}
    (fordEqual :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    Derives leftRegularBandThreeBasis left right := by
  have leftNormal := lrbDerivesNormal left
  have rightNormal := lrbDerivesNormal right
  cases leftSequence :
      firstOccurrenceSequence left.toList with
  | nil =>
      cases left with
      | mk head tail =>
          simp [Word.toList, firstOccurrenceSequence] at leftSequence
  | cons leftHead leftTail =>
      cases rightSequence :
          firstOccurrenceSequence right.toList with
      | nil =>
          cases right with
          | mk head tail =>
              simp [Word.toList, firstOccurrenceSequence] at rightSequence
      | cons rightHead rightTail =>
          rw [leftSequence] at leftNormal
          rw [rightSequence] at rightNormal
          have normalListsEqual :
              leftHead :: leftTail = rightHead :: rightTail := by
            calc
              leftHead :: leftTail =
                  firstOccurrenceSequence left.toList :=
                leftSequence.symm
              _ = firstOccurrenceSequence right.toList := fordEqual
              _ = rightHead :: rightTail := rightSequence
          cases normalListsEqual
          exact leftNormal.trans rightNormal.symm

private theorem lrbEval_eq_initialListEval
    (valuation : Nat → Fin 3) (word : Word Nat) :
    leftRegularBandThree.semigroup.eval valuation word =
      SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.initialListEval
          valuation word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              leftRegularBandThreeMul current (valuation letter))
            (valuation head) =
          tail.foldl
            (fun current letter =>
              leftRegularBandThreeMul current (valuation letter))
            (leftRegularBandThreeMul 1 (valuation head))
      rw [show leftRegularBandThreeMul 1 (valuation head) =
          valuation head by
        simp [leftRegularBandThreeMul]]

private theorem oppositeLrbEval_eq_finalListEval
    (valuation : Nat → Fin 3) (word : Word Nat) :
    leftRegularBandThree.semigroup.opposite.eval valuation word =
      SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.finalListEval
          valuation word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              leftRegularBandThreeMul (valuation letter) current)
            (valuation head) =
          tail.foldl
            (fun current letter =>
              leftRegularBandThreeMul (valuation letter) current)
            (leftRegularBandThreeMul (valuation head) 1)
      rw [show leftRegularBandThreeMul (valuation head) 1 =
          valuation head by
        have rightIdentity :
            ∀ value : Fin 3,
              leftRegularBandThreeMul value 1 = value := by
          decide
        exact rightIdentity (valuation head)]

/-- Literal Ford/Lord equality implies the semantic endpoint equivalence used
by the seven-law normalizer. -/
theorem endpointEquivalent_of_ford_lord_eq
    {left right : Word Nat}
    (fordEqual :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (lordEqual :
      lastOccurrenceSequence left.toList =
        lastOccurrenceSequence right.toList) :
    SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.EndpointEquivalent
        left.toList right.toList := by
  constructor
  · intro valuation
    have derivation := lrbDerives_of_ford_eq fordEqual
    have sound :=
      derivation.sound leftRegularBandThreeBasis_models valuation
    simpa only [lrbEval_eq_initialListEval] using sound
  · intro valuation
    have reversedFordEqual :
        firstOccurrenceSequence left.reverse.toList =
          firstOccurrenceSequence right.reverse.toList := by
      have reversedLordEqual := congrArg List.reverse lordEqual
      simpa only [
        lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence,
        Word.toList_reverse, List.reverse_reverse
      ] using reversedLordEqual
    have reversedDerivation :=
      lrbDerives_of_ford_eq reversedFordEqual
    have reversedSound :=
      reversedDerivation.sound
        leftRegularBandThreeBasis_models valuation
    have oppositeSound :
        leftRegularBandThree.semigroup.opposite.eval valuation left =
          leftRegularBandThree.semigroup.opposite.eval valuation right := by
      simpa only [Semigroup.eval_opposite_eq_reverse] using reversedSound
    simpa only [oppositeLrbEval_eq_finalListEval] using oppositeSound

/-- The `(2,1)` one-local count profile is exactly multiplicity capped at two. -/
theorem capped_two_one_eq_min (count : Nat) :
    JointCompleteness.capped 2 1 count = min count 2 := by
  unfold JointCompleteness.capped
  split <;> rename_i bound
  · exact (Nat.min_eq_left bound).symm
  · have two_le : 2 ≤ count := by omega
    simpa only [Nat.mod_one, Nat.add_zero] using
      (Nat.min_eq_right two_le).symm

/-- Assemble the invariant consumed by the unrestricted seven-law normalizer
from the three literal one-local components. -/
theorem cappedEndpointInvariant_of_ford_lord_cappedCounts
    {left right : Word Nat}
    (fordEqual :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (lordEqual :
      lastOccurrenceSequence left.toList =
        lastOccurrenceSequence right.toList)
    (cappedCountsEqual :
      ∀ letter,
        min (left.toList.count letter) 2 =
          min (right.toList.count letter) 2) :
    SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.CappedEndpointInvariant
        ⟨left, right⟩ where
  endpoints :=
    endpointEquivalent_of_ford_lord_eq fordEqual lordEqual
  cappedCounts := cappedCountsEqual

namespace Laws

/-- Transport the existing unrestricted seven-law normalizer into any target
system satisfying the shared-law interface. -/
theorem derivesOfInvariant
    {basis : List (Identity Nat)}
    (laws : Laws basis)
    (identity : Identity Nat)
    (invariant :
      SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.CappedEndpointInvariant
          identity) :
    Derives basis identity.lhs identity.rhs :=
  Derives.transport laws.sourceAxiomsDerive <|
    SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.derivesOfInvariant
        identity invariant

/-- Strong pairwise Nat reach: any two words with equal Ford, Lord, and
capped-at-two multiplicity data derive one another in the target system. -/
theorem derivesOfFordLordCappedCounts
    {basis : List (Identity Nat)}
    (laws : Laws basis)
    {left right : Word Nat}
    (fordEqual :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (lordEqual :
      lastOccurrenceSequence left.toList =
        lastOccurrenceSequence right.toList)
    (cappedCountsEqual :
      ∀ letter,
        min (left.toList.count letter) 2 =
          min (right.toList.count letter) 2) :
    Derives basis left right :=
  laws.derivesOfInvariant ⟨left, right⟩
    (cappedEndpointInvariant_of_ford_lord_cappedCounts
      fordEqual lordEqual cappedCountsEqual)

/-- Equal `(2,1)` Ford/Lord profiles imply unrestricted derivability in every
displayed system satisfying `Laws`. -/
theorem derivesOfProfileEq
    {basis : List (Identity Nat)}
    (laws : Laws basis)
    {left right : Word Nat}
    (profilesEqual : profile 2 1 left = profile 2 1 right) :
    Derives basis left right := by
  apply laws.derivesOfFordLordCappedCounts
  · exact congrArg (fun value => value.ford) profilesEqual
  · exact congrArg (fun value => value.lord) profilesEqual
  · intro letter
    have equal :=
      congrArg (fun value => value.cappedCounts letter) profilesEqual
    simpa only [profile, capped_two_one_eq_min] using equal

/-- Full joint completeness from semantic necessity of the existing `(2,1)`
profile.  No normal-form choice and no per-obligation reach proof remains. -/
theorem obligation_of_profile
    {A : Type u} {B : Type v}
    {G : Semigroup A} {H : Semigroup B}
    {basis : List (Identity Nat)}
    (laws : Laws basis)
    (profileNecessary :
      ∀ left right : Word Nat,
        (∀ valuation : Nat → A,
          G.eval valuation left = G.eval valuation right) →
        (∀ valuation : Nat → B,
          H.eval valuation left = H.eval valuation right) →
        profile 2 1 left = profile 2 1 right) :
    JointCompleteness.DerivationalObligation G H basis := by
  intro identity leftValid rightValid
  exact laws.derivesOfProfileEq
    (profileNecessary identity.lhs identity.rhs leftValid rightValid)

/-- Production form using the already exposed necessity halves of two sealed
factor profiles. -/
theorem obligation_of_merged_factorProfiles
    {A : Type u} {B : Type v}
    {G : Semigroup A} {H : Semigroup B}
    {basis : List (Identity Nat)}
    {PG : Type w} {PH : Type x}
    (laws : Laws basis)
    (leftProfile : JointCompleteness.FactorProfile G PG)
    (rightProfile : JointCompleteness.FactorProfile H PH)
    (merge : PG × PH → Profile 2 1)
    (merge_profile :
      ∀ word,
        merge (leftProfile.φ word, rightProfile.φ word) =
          profile 2 1 word) :
    JointCompleteness.DerivationalObligation G H basis :=
  laws.obligation_of_profile
    (fun left right leftValid rightValid => by
      calc
        profile 2 1 left =
            merge (leftProfile.φ left, rightProfile.φ left) :=
          (merge_profile left).symm
        _ = merge (leftProfile.φ right, rightProfile.φ right) := by
          rw [leftProfile.nec left right leftValid,
            rightProfile.nec left right rightValid]
        _ = profile 2 1 right := merge_profile right)

/-- Package the shared completeness theorem as the exact intersection object
consumed by order-six subdirect wrappers. -/
def intersectionBasis_of_merged_factorProfiles
    {A : Type u} {B : Type v}
    {G : Semigroup A} {H : Semigroup B}
    {basis : List (Identity Nat)}
    {PG : Type w} {PH : Type x}
    (laws : Laws basis)
    (leftModels : Models G basis)
    (rightModels : Models H basis)
    (leftProfile : JointCompleteness.FactorProfile G PG)
    (rightProfile : JointCompleteness.FactorProfile H PH)
    (merge : PG × PH → Profile 2 1)
    (merge_profile :
      ∀ word,
        merge (leftProfile.φ word, rightProfile.φ word) =
          profile 2 1 word) :
    IntersectionBasis G H basis where
  leftModels := leftModels
  rightModels := rightModels
  complete :=
    laws.obligation_of_merged_factorProfiles
      leftProfile rightProfile merge merge_profile

end Laws

end SharedReach
end OneLocalFordLord
end SemigroupBasis

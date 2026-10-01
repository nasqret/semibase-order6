import SemigroupBasis.CoRoots.Order6SporadicSection15Adjacency
import SemigroupBasis.CoRoots.Order6SporadicSection15InvariantSyntax
import SemigroupBasis.CoRoots.Order6SporadicSection15Semantics
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.CoRoots.S5_381Invariant
import SemigroupBasis.Examples.CommutativeExponentFour

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open SemigroupBasis.Examples

private theorem simpleCount_iff_of_countStrata
    (identity : Identity Nat)
    (countStrata : SameCountStrata identity.lhs identity.rhs)
    (letter : Nat) :
    identity.lhs.toList.count letter = 1 ↔
      identity.rhs.toList.count letter = 1 := by
  rw [← S5_213Syntax.cappedMultiplicity_eq_one_iff,
    ← S5_213Syntax.cappedMultiplicity_eq_one_iff,
    countStrata letter]

private theorem sameFSS_of_detector
    {S : Type u} (candidate : Semigroup S)
    {zero one targetState sourceState otherState : S}
    (laws : DirectedSimpleAdjacencyLaws candidate
      zero one targetState sourceState otherState)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy candidate)
    (countStrata : SameCountStrata identity.lhs identity.rhs) :
    SameFSS identity.lhs identity.rhs := by
  intro source target
  by_cases different : source ≠ target
  · have sourceSimple :=
      simpleCount_iff_of_countStrata identity countStrata source
    have targetSimple :=
      simpleCount_iff_of_countStrata identity countStrata target
    by_cases lhsSource : identity.lhs.toList.count source = 1
    · have rhsSource := sourceSimple.mp lhsSource
      by_cases lhsTarget : identity.lhs.toList.count target = 1
      · have rhsTarget := targetSimple.mp lhsTarget
        exact valid_simpleAdjacent_iff candidate laws identity valid
          source target different lhsSource lhsTarget rhsSource rhsTarget
      · have rhsTarget : identity.rhs.toList.count target ≠ 1 := by
          intro simple
          exact lhsTarget (targetSimple.mpr simple)
        constructor
        · intro adjacent
          exact False.elim (lhsTarget adjacent.2.1)
        · intro adjacent
          exact False.elim (rhsTarget adjacent.2.1)
    · have rhsSource : identity.rhs.toList.count source ≠ 1 := by
        intro simple
        exact lhsSource (sourceSimple.mpr simple)
      constructor
      · intro adjacent
        exact False.elim (lhsSource adjacent.1)
      · intro adjacent
        exact False.elim (rhsSource adjacent.1)
  · have equal : source = target := Decidable.not_not.mp different
    subst target
    constructor
    · intro adjacent
      exact False.elim ((simpleAdjacent_ne adjacent) rfl)
    · intro adjacent
      exact False.elim ((simpleAdjacent_ne adjacent) rfl)

/-- Factor validity plus the target's five-state detector proves all four
parts of Lee--Zhang Lemma 15.2. -/
theorem lemma15_2_of_semantics
    {S : Type u} (candidate : Semigroup S)
    {zero one targetState sourceState otherState : S}
    (laws : DirectedSimpleAdjacencyLaws candidate
      zero one targetState sourceState otherState)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy candidate)
    (countValid :
      identity.SatisfiedBy Generated.S4_40.table.semigroup)
    (finalValid :
      identity.SatisfiedBy Generated.S3_6.table.semigroup)
    (initialValid :
      identity.SatisfiedBy Generated.S3_6.table.semigroup.opposite) :
    Lemma15_2Invariants identity.lhs identity.rhs := by
  have countStrata : SameCountStrata identity.lhs identity.rhs := by
    intro letter
    change
      min 3 (identity.lhs.toList.count letter) =
        min 3 (identity.rhs.toList.count letter)
    rw [Nat.min_comm 3 (identity.lhs.toList.count letter),
      Nat.min_comm 3 (identity.rhs.toList.count letter)]
    exact exponentFourValid_capped_count_eq identity
      (by
        simpa [Generated.S4_40.table, commutativeExponentFour] using
          countValid) letter
  refine
    { countStrata := countStrata
      simpleInitial := ?_
      simpleFinal := ?_
      fss := sameFSS_of_detector candidate laws identity valid countStrata }
  · intro letter
    exact S5_381Invariant.oppositeFinalMarkerValid_simpleInitial_iff
      identity
      (by
        simpa [Generated.S3_6.table, finalMarkerThree] using
          initialValid)
      letter
  · intro letter
    exact S5_345Factors.finalMarkerThreeValid_simpleFinal_iff
      identity
      (by
        simpa [Generated.S3_6.table, finalMarkerThree] using
          finalValid)
      letter

namespace S6_2771

theorem lemma15_2 (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    Lemma15_2Invariants identity.lhs identity.rhs :=
  lemma15_2_of_semantics publishedSemigroup directedSimpleAdjacencyLaws
    identity valid (valid_count identity valid)
    (valid_final identity valid) (valid_initial identity valid)

end S6_2771

namespace S6_2772

theorem lemma15_2 (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    Lemma15_2Invariants identity.lhs identity.rhs :=
  lemma15_2_of_semantics publishedSemigroup directedSimpleAdjacencyLaws
    identity valid (valid_count identity valid)
    (valid_final identity valid) (valid_initial identity valid)

end S6_2772

namespace S6_2773

theorem lemma15_2 (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    Lemma15_2Invariants identity.lhs identity.rhs :=
  lemma15_2_of_semantics publishedSemigroup directedSimpleAdjacencyLaws
    identity valid (valid_count identity valid)
    (valid_final identity valid) (valid_initial identity valid)

end S6_2773

namespace S6_5240

theorem lemma15_2 (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    Lemma15_2Invariants identity.lhs identity.rhs :=
  lemma15_2_of_semantics publishedSemigroup directedSimpleAdjacencyLaws
    identity valid (valid_count identity valid)
    (valid_final identity valid) (valid_initial identity valid)

end S6_5240

namespace S6_5241

theorem lemma15_2 (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    Lemma15_2Invariants identity.lhs identity.rhs :=
  lemma15_2_of_semantics publishedSemigroup directedSimpleAdjacencyLaws
    identity valid (valid_count identity valid)
    (valid_final identity valid) (valid_initial identity valid)

end S6_5241

namespace S6_9313

theorem lemma15_2 (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    Lemma15_2Invariants identity.lhs identity.rhs :=
  lemma15_2_of_semantics publishedSemigroup directedSimpleAdjacencyLaws
    identity valid (valid_count identity valid)
    (valid_final identity valid) (valid_initial identity valid)

end S6_9313

end SemigroupBasis.CoRoots.Order6SporadicSection15

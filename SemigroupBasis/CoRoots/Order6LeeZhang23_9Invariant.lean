import SemigroupBasis.CoRoots.Order6LeeZhang23_9Syntax
import SemigroupBasis.CoRoots.S5_793Invariant
import SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op

namespace SemigroupBasis.CoRoots.Order6LeeZhang23_9Invariant

open SemigroupBasis
open Order6LeeZhang23_9Syntax

/-! ## The compact and published invariant presentations -/

private theorem globallySimple_ne_of_adjacent
    {word : Word Nat} {source target : Nat}
    (sourceSimple : S5_402.GloballySimple word source)
    (adjacent : (source, target) ∈ word.adjacentPairs) :
    source ≠ target := by
  intro equal
  subst target
  obtain ⟨before, after, shape⟩ :=
    (S5_107.mem_adjacentPairs_iff_exists_split
      source source word).mp adjacent
  unfold S5_402.GloballySimple S5_107.SimpleIn at sourceSimple
  rw [shape, List.count_append] at sourceSimple
  simp only [List.count_cons_self] at sourceSimple
  omega

private theorem cappedMultiplicity_eq_of_support_and_simple
    {left right : Word Nat}
    (support : S5_402.SameSupport left right)
    (simple : S5_402.SameGloballySimpleVariables left right)
    (letter : Nat) :
    S5_402.cappedMultiplicity left letter =
      S5_402.cappedMultiplicity right letter := by
  have positive :
      0 < left.toList.count letter ↔
        0 < right.toList.count letter := by
    simpa only [List.count_pos_iff] using support letter
  have countOne :
      left.toList.count letter = 1 ↔
        right.toList.count letter = 1 := by
    simpa only [S5_402.GloballySimple, S5_107.SimpleIn] using
      simple letter
  by_cases leftZero : left.toList.count letter = 0
  · have leftNotPositive : ¬0 < left.toList.count letter := by omega
    have rightNotPositive : ¬0 < right.toList.count letter :=
      (not_congr positive).mp leftNotPositive
    have rightZero : right.toList.count letter = 0 := by omega
    simp [S5_402.cappedMultiplicity, S5_107.cappedMultiplicity,
      leftZero, rightZero]
  · by_cases leftOne : left.toList.count letter = 1
    · have rightOne : right.toList.count letter = 1 :=
        countOne.mp leftOne
      simp [S5_402.cappedMultiplicity, S5_107.cappedMultiplicity,
        leftOne, rightOne]
    · have leftPositive : 0 < left.toList.count letter := by omega
      have rightPositive : 0 < right.toList.count letter :=
        positive.mp leftPositive
      have rightNotOne : right.toList.count letter ≠ 1 := by
        intro rightOne
        exact leftOne (countOne.mpr rightOne)
      have leftAtLeastTwo : 2 ≤ left.toList.count letter := by omega
      have rightAtLeastTwo : 2 ≤ right.toList.count letter := by omega
      unfold S5_402.cappedMultiplicity S5_107.cappedMultiplicity
      calc
        Nat.min 2 (left.toList.count letter) = 2 :=
          Nat.min_eq_left leftAtLeastTwo
        _ = Nat.min 2 (right.toList.count letter) :=
          (Nat.min_eq_left rightAtLeastTwo).symm

/-- The compact source-native signature implies exactly the six coordinates
of Lee--Zhang Lemma 23.11. -/
theorem samePublishedLeeZhang23_9Signature_of_compact
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right) :
    SamePublishedLeeZhang23_9Signature left right := by
  have simple : S5_402.SameGloballySimpleVariables left right := by
    intro letter
    simpa only [globallySimple_reverse_iff] using
      same.reversedS5_402.globallySimple letter
  refine
    { support := ?_
      globallySimple := simple
      head := same.head
      final := ?_
      fns := ?_
      fss := ?_ }
  · intro letter
    simpa only [Word.toList_reverse, List.mem_reverse] using
      same.reversedS5_402.support letter
  · simpa only [reverse_head_eq_final] using
      same.reversedS5_402.head
  · intro source target
    have successor := same.reversedS5_402.successor target source
    constructor
    · rintro ⟨sourceNonSimple, targetSimple, adjacent⟩
      have leftSuccessor :
          S5_402.ImmediateSuccessor left.reverse target source := by
        refine ⟨?_, ?_, ?_⟩
        · intro equal
          subst target
          exact sourceNonSimple targetSimple
        · simpa only [globallySimple_reverse_iff] using targetSimple
        · exact (adjacentPairs_reverse_iff left target source).mpr adjacent
      rcases successor.mp leftSuccessor with
        ⟨_, rightTargetSimple, rightAdjacent⟩
      exact
        ⟨(not_congr (simple source)).mp sourceNonSimple,
          (globallySimple_reverse_iff right target).mp rightTargetSimple,
          (adjacentPairs_reverse_iff right target source).mp rightAdjacent⟩
    · rintro ⟨sourceNonSimple, targetSimple, adjacent⟩
      have rightSuccessor :
          S5_402.ImmediateSuccessor right.reverse target source := by
        refine ⟨?_, ?_, ?_⟩
        · intro equal
          subst target
          exact sourceNonSimple targetSimple
        · simpa only [globallySimple_reverse_iff] using targetSimple
        · exact (adjacentPairs_reverse_iff right target source).mpr adjacent
      rcases successor.mpr rightSuccessor with
        ⟨_, leftTargetSimple, leftAdjacent⟩
      exact
        ⟨(not_congr (simple source)).mpr sourceNonSimple,
          (globallySimple_reverse_iff left target).mp leftTargetSimple,
          (adjacentPairs_reverse_iff left target source).mp leftAdjacent⟩
  · intro source target
    have successor := same.reversedS5_402.successor target source
    constructor
    · rintro ⟨sourceSimple, targetSimple, adjacent⟩
      have leftSuccessor :
          S5_402.ImmediateSuccessor left.reverse target source := by
        refine ⟨?_, ?_, ?_⟩
        · exact Ne.symm
            (globallySimple_ne_of_adjacent sourceSimple adjacent)
        · simpa only [globallySimple_reverse_iff] using targetSimple
        · exact (adjacentPairs_reverse_iff left target source).mpr adjacent
      rcases successor.mp leftSuccessor with
        ⟨_, rightTargetSimple, rightAdjacent⟩
      exact
        ⟨(simple source).mp sourceSimple,
          (globallySimple_reverse_iff right target).mp rightTargetSimple,
          (adjacentPairs_reverse_iff right target source).mp rightAdjacent⟩
    · rintro ⟨sourceSimple, targetSimple, adjacent⟩
      have rightSuccessor :
          S5_402.ImmediateSuccessor right.reverse target source := by
        refine ⟨?_, ?_, ?_⟩
        · exact Ne.symm
            (globallySimple_ne_of_adjacent sourceSimple adjacent)
        · simpa only [globallySimple_reverse_iff] using targetSimple
        · exact (adjacentPairs_reverse_iff right target source).mpr adjacent
      rcases successor.mpr rightSuccessor with
        ⟨_, leftTargetSimple, leftAdjacent⟩
      exact
        ⟨(simple source).mpr sourceSimple,
          (globallySimple_reverse_iff left target).mp leftTargetSimple,
          (adjacentPairs_reverse_iff left target source).mp leftAdjacent⟩

/-- Conversely, the six published coordinates reconstruct the compact
reversed `S5_402` signature without retaining multiplicities above two. -/
theorem sameLeeZhang23_9Signature_of_published
    {left right : Word Nat}
    (same : SamePublishedLeeZhang23_9Signature left right) :
    SameLeeZhang23_9Signature left right := by
  refine ⟨same.head, ?_⟩
  refine
    { capped := ?_
      support := ?_
      head := ?_
      globallySimple := ?_
      successor := ?_ }
  · intro letter
    simpa only [cappedMultiplicity_reverse] using
      cappedMultiplicity_eq_of_support_and_simple
        same.support same.globallySimple letter
  · intro letter
    simpa only [Word.toList_reverse, List.mem_reverse] using
      same.support letter
  · simpa only [reverse_head_eq_final] using same.final
  · intro letter
    simpa only [globallySimple_reverse_iff] using
      same.globallySimple letter
  · intro source target
    constructor
    · rintro ⟨different, sourceSimple, adjacent⟩
      have leftSourceSimple : S5_402.GloballySimple left source :=
        (globallySimple_reverse_iff left source).mp sourceSimple
      have leftAdjacent : (target, source) ∈ left.adjacentPairs :=
        (adjacentPairs_reverse_iff left source target).mp adjacent
      by_cases leftTargetSimple : S5_402.GloballySimple left target
      · rcases (same.fss target source).mp
            ⟨leftTargetSimple, leftSourceSimple, leftAdjacent⟩ with
          ⟨_, rightSourceSimple, rightAdjacent⟩
        exact
          ⟨different,
            (globallySimple_reverse_iff right source).mpr rightSourceSimple,
            (adjacentPairs_reverse_iff right source target).mpr
              rightAdjacent⟩
      · rcases (same.fns target source).mp
            ⟨leftTargetSimple, leftSourceSimple, leftAdjacent⟩ with
          ⟨_, rightSourceSimple, rightAdjacent⟩
        exact
          ⟨different,
            (globallySimple_reverse_iff right source).mpr rightSourceSimple,
            (adjacentPairs_reverse_iff right source target).mpr
              rightAdjacent⟩
    · rintro ⟨different, sourceSimple, adjacent⟩
      have rightSourceSimple : S5_402.GloballySimple right source :=
        (globallySimple_reverse_iff right source).mp sourceSimple
      have rightAdjacent : (target, source) ∈ right.adjacentPairs :=
        (adjacentPairs_reverse_iff right source target).mp adjacent
      by_cases rightTargetSimple : S5_402.GloballySimple right target
      · rcases (same.fss target source).mpr
            ⟨rightTargetSimple, rightSourceSimple, rightAdjacent⟩ with
          ⟨_, leftSourceSimple, leftAdjacent⟩
        exact
          ⟨different,
            (globallySimple_reverse_iff left source).mpr leftSourceSimple,
            (adjacentPairs_reverse_iff left source target).mpr
              leftAdjacent⟩
      · rcases (same.fns target source).mpr
            ⟨rightTargetSimple, rightSourceSimple, rightAdjacent⟩ with
          ⟨_, leftSourceSimple, leftAdjacent⟩
        exact
          ⟨different,
            (globallySimple_reverse_iff left source).mpr leftSourceSimple,
            (adjacentPairs_reverse_iff left source target).mpr
              leftAdjacent⟩

/-- The compact carrier is propositionally equivalent to the six-coordinate
Lee--Zhang signature. -/
theorem sameLeeZhang23_9Signature_iff_published
    {left right : Word Nat} :
    SameLeeZhang23_9Signature left right ↔
      SamePublishedLeeZhang23_9Signature left right :=
  ⟨samePublishedLeeZhang23_9Signature_of_compact,
    sameLeeZhang23_9Signature_of_published⟩

/-! ## Necessity from the two product factors -/

/-- Validity in the left-zero factor `S2_4` preserves the literal head. -/
theorem leftFactorValid_head_eq
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.G) :
    identity.lhs.head = identity.rhs.head := by
  have leftZeroValid :
      identity.SatisfiedBy
        SemigroupBasis.Examples.leftZeroTwo.semigroup := by
    rw [← S5_793Invariant.catalogueS2_4_table_eq_leftZeroTwo]
    simpa [SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.G,
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.leftTable] using
        leftValid
  exact S5_793Invariant.leftZeroValid_head_eq identity leftZeroValid

/-- Validity in `S5_402^op` supplies the established `S5_402` signature on
the two reversed words. -/
theorem rightFactorValid_reversedS5_402
    (identity : Identity Nat)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.H) :
    S5_402.SameSimpleSuccessorSignature
      identity.lhs.reverse identity.rhs.reverse := by
  have oppositeValid :
      identity.SatisfiedBy S5_402.table.semigroup.opposite := by
    simpa [SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.H,
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.rightTable] using
        rightValid
  have reversedValid :
      identity.reversed.SatisfiedBy S5_402.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity S5_402.table.semigroup).mp oppositeValid
  simpa [Identity.reversed] using
    S5_402.sameSignature_of_valid identity.reversed reversedValid

/-- Every identity valid in both exact factors has the compact
Lee--Zhang Proposition 23.9 signature. -/
theorem sameLeeZhang23_9Signature_of_factorValidity
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.G)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.H) :
    SameLeeZhang23_9Signature identity.lhs identity.rhs :=
  ⟨leftFactorValid_head_eq identity leftValid,
    rightFactorValid_reversedS5_402 identity rightValid⟩

end SemigroupBasis.CoRoots.Order6LeeZhang23_9Invariant

import SemigroupBasis.CoRoots.Order6PublishedMonoid14Normalization
import SemigroupBasis.CoRoots.S5_213Syntax

namespace SemigroupBasis.CoRoots.Order6PublishedMonoid14

open SemigroupBasis

/-! ## First-occurrence banks -/

/-- Retain either of two selected letters. -/
def pairKeep (first second letter : Nat) : Bool :=
  letter == first || letter == second

/-- The pair projection's head is the first occurrence selected by the Bool
predicate used by the finite-table order probes. -/
theorem pairProjection_head?_eq_findPair
    (letters : List Nat) (first second : Nat) :
    (letters.filter (pairKeep first second)).head? =
      letters.find? (fun letter =>
        decide (letter = first ∨ letter = second)) := by
  rw [List.head?_filter]
  congr 1
  funext letter
  simp only [pairKeep]
  by_cases h1 : letter = first
  · simp [h1]
  · by_cases h2 : letter = second
    · simp [h1, h2]
    · simp [h1, h2]

/-- The square-bank deduplicator is the standard first-occurrence scan. -/
theorem distinctLetters_eq_firstOccurrenceSequence :
    ∀ letters : List Nat,
      S5_107.distinctLetters letters =
        SemigroupBasis.Examples.firstOccurrenceSequence letters
  | [] => rfl
  | letter :: rest => by
      simp [S5_107.distinctLetters,
        SemigroupBasis.Examples.firstOccurrenceSequence,
        distinctLetters_eq_firstOccurrenceSequence rest]

@[simp]
theorem distinctLetters_head? (letters : List Nat) :
    (S5_107.distinctLetters letters).head? = letters.head? := by
  cases letters <;> rfl

/-- Deduplicating a list does not change which of two selected letters occurs
first. -/
theorem pairProjection_distinctLetters_head?
    (letters : List Nat) (first second : Nat) :
    ((S5_107.distinctLetters letters).filter
        (pairKeep first second)).head? =
      (letters.filter (pairKeep first second)).head? := by
  have commutation :
      S5_107.distinctLetters
          (letters.filter (pairKeep first second)) =
        (S5_107.distinctLetters letters).filter
          (pairKeep first second) := by
    simpa [distinctLetters_eq_firstOccurrenceSequence] using
      S5_213Syntax.firstOccurrenceSequence_filter
        (pairKeep first second) letters
  calc
    ((S5_107.distinctLetters letters).filter
          (pairKeep first second)).head? =
        (S5_107.distinctLetters
          (letters.filter (pairKeep first second))).head? := by
      rw [commutation]
    _ = (letters.filter (pairKeep first second)).head? :=
      distinctLetters_head? _

private theorem nodup_eq_of_pairProjection_head :
    ∀ {left right : List Nat},
      left.Nodup →
      right.Nodup →
      (∀ value, value ∈ left ↔ value ∈ right) →
      (∀ first second,
        first ≠ second →
        first ∈ left →
        second ∈ left →
        (left.filter (pairKeep first second)).head? =
          (right.filter (pairKeep first second)).head?) →
      left = right
  | [], [], _, _, _, _ => rfl
  | [], head :: tail, _, _, sameMembers, _ => by
      have impossible : head ∈ ([] : List Nat) :=
        (sameMembers head).mpr (by simp)
      simp at impossible
  | head :: tail, [], _, _, sameMembers, _ => by
      have impossible : head ∈ ([] : List Nat) :=
        (sameMembers head).mp (by simp)
      simp at impossible
  | leftHead :: leftTail, rightHead :: rightTail,
      leftNodup, rightNodup, sameMembers, sameHeads => by
      simp only [List.nodup_cons] at leftNodup rightNodup
      have headsEqual : leftHead = rightHead := by
        apply Decidable.byContradiction
        intro different
        have pairHeads :=
          sameHeads leftHead rightHead different
            (by simp) ((sameMembers rightHead).mpr (by simp))
        simp [pairKeep, different] at pairHeads
      subst rightHead
      have tailMembers :
          ∀ value, value ∈ leftTail ↔ value ∈ rightTail := by
        intro value
        constructor
        · intro member
          have inRight : value ∈ leftHead :: rightTail :=
            (sameMembers value).mp (by simp [member])
          rcases List.mem_cons.mp inRight with equality | tailMember
          · subst value
            exact False.elim (leftNodup.1 member)
          · exact tailMember
        · intro member
          have inLeft : value ∈ leftHead :: leftTail :=
            (sameMembers value).mpr (by simp [member])
          rcases List.mem_cons.mp inLeft with equality | tailMember
          · subst value
            exact False.elim (rightNodup.1 member)
          · exact tailMember
      have tailHeads :
          ∀ first second,
            first ≠ second →
            first ∈ leftTail →
            second ∈ leftTail →
            (leftTail.filter (pairKeep first second)).head? =
              (rightTail.filter (pairKeep first second)).head? := by
        intro first second different firstMember secondMember
        have firstNotHead : first ≠ leftHead := by
          intro equality
          subst first
          exact leftNodup.1 firstMember
        have secondNotHead : second ≠ leftHead := by
          intro equality
          subst second
          exact leftNodup.1 secondMember
        have inherited :=
          sameHeads first second different
            (by simp [firstMember]) (by simp [secondMember])
        simpa [pairKeep, Ne.symm firstNotHead,
          Ne.symm secondNotHead] using inherited
      have tailEqual :=
        nodup_eq_of_pairProjection_head
          leftNodup.2 rightNodup.2 tailMembers tailHeads
      rw [tailEqual]

/-- Equal support and equal two-letter first-occurrence probes determine the
complete ordered square bank. -/
theorem distinctLetters_eq_of_support_pairHeads
    (left right : List Nat)
    (support : ∀ letter, letter ∈ left ↔ letter ∈ right)
    (pairHeads :
      ∀ first second,
        first ≠ second →
        first ∈ left →
        second ∈ left →
        (left.filter (pairKeep first second)).head? =
          (right.filter (pairKeep first second)).head?) :
    S5_107.distinctLetters left = S5_107.distinctLetters right := by
  apply nodup_eq_of_pairProjection_head
  · exact S5_107.distinctLetters_nodup left
  · exact S5_107.distinctLetters_nodup right
  · intro letter
    simpa only [S5_107.distinctLetters_mem_iff] using support letter
  · intro first second different firstMember secondMember
    rw [pairProjection_distinctLetters_head?,
      pairProjection_distinctLetters_head?]
    exact pairHeads first second different
      ((S5_107.distinctLetters_mem_iff first left).mp firstMember)
      ((S5_107.distinctLetters_mem_iff second left).mp secondMember)

/-! ## Globally simple separator alignment -/

def simpleKeep (letters : List Nat) (letter : Nat) : Bool :=
  decide (letters.count letter = 1)

def simpleProjection (letters : List Nat) : List Nat :=
  letters.filter (simpleKeep letters)

private theorem repeatedGap_filter_simple_nil
    (whole gap : List Nat)
    (repeated : ∀ letter, letter ∈ gap →
      2 ≤ whole.count letter) :
    gap.filter (simpleKeep whole) = [] := by
  induction gap with
  | nil => rfl
  | cons letter rest induction =>
      have letterRepeated := repeated letter (by simp)
      have letterNotSimple : whole.count letter ≠ 1 := by omega
      simp [simpleKeep, letterNotSimple,
        induction (by
          intro tested member
          exact repeated tested (List.Mem.tail letter member))]

/-- A globally-simple decomposition lists exactly the singleton variables in
their literal order. -/
theorem separatorSequence_eq_simpleProjection
    {whole source : List Nat}
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        whole source segments finalGap) :
    segments.map Prod.snd =
      source.filter (simpleKeep whole) := by
  induction decomposition with
  | final gap gapRepeated =>
      simpa using
        repeatedGap_filter_simple_nil whole gap gapRepeated
  | step gap separator remainder segments finalGap
      separatorSimple gapRepeated tail induction =>
      have gapEmpty :=
        repeatedGap_filter_simple_nil whole gap gapRepeated
      simp [List.filter_append, gapEmpty, simpleKeep,
        separatorSimple, induction]

private theorem simple_count_iff_of_capped
    {left right : Word Nat}
    (capped :
      ∀ letter,
        S5_107.cappedMultiplicity left letter =
          S5_107.cappedMultiplicity right letter)
    (letter : Nat) :
    left.toList.count letter = 1 ↔
      right.toList.count letter = 1 := by
  rw [← S5_107.cappedMultiplicity_eq_one_iff,
    ← S5_107.cappedMultiplicity_eq_one_iff, capped letter]

private theorem simpleKeep_eq_of_capped
    {left right : Word Nat}
    (capped :
      ∀ letter,
        S5_107.cappedMultiplicity left letter =
          S5_107.cappedMultiplicity right letter) :
    simpleKeep left.toList = simpleKeep right.toList := by
  funext letter
  have agreement := simple_count_iff_of_capped capped letter
  by_cases leftSimple : left.toList.count letter = 1
  · have rightSimple := agreement.mp leftSimple
    simp [simpleKeep, leftSimple, rightSimple]
  · have rightNotSimple : right.toList.count letter ≠ 1 :=
      fun rightSimple => leftSimple (agreement.mpr rightSimple)
    simp [simpleKeep, leftSimple, rightNotSimple]

/-- Capped multiplicities identify the singleton variables, while global
first-occurrence order identifies their sequence. -/
theorem simpleProjection_eq_of_capped_firstOccurrences
    {left right : Word Nat}
    (capped :
      ∀ letter,
        S5_107.cappedMultiplicity left letter =
          S5_107.cappedMultiplicity right letter)
    (firstOccurrences :
      SemigroupBasis.Examples.firstOccurrenceSequence left.toList =
        SemigroupBasis.Examples.firstOccurrenceSequence right.toList) :
    simpleProjection left.toList = simpleProjection right.toList := by
  have keepEq := simpleKeep_eq_of_capped capped
  have leftShape :
      simpleProjection left.toList =
        (SemigroupBasis.Examples.firstOccurrenceSequence
          left.toList).filter (simpleKeep left.toList) := by
    simpa [simpleProjection, simpleKeep,
      S5_213Syntax.singletonSequence] using
        S5_213Syntax.singletonSequence_eq_firstOccurrence_filter left
  have rightShape :
      simpleProjection right.toList =
        (SemigroupBasis.Examples.firstOccurrenceSequence
          right.toList).filter (simpleKeep right.toList) := by
    simpa [simpleProjection, simpleKeep,
      S5_213Syntax.singletonSequence] using
        S5_213Syntax.singletonSequence_eq_firstOccurrence_filter right
  rw [leftShape, rightShape, firstOccurrences, keepEq]

/-- The two staged global invariants align the separator labels of any two
globally-simple decompositions. -/
theorem separatorSequence_eq_of_capped_firstOccurrences
    {left right : Word Nat}
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (leftDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        left.toList left.toList leftSegments leftFinal)
    (rightDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        right.toList right.toList rightSegments rightFinal)
    (capped :
      ∀ letter,
        S5_107.cappedMultiplicity left letter =
          S5_107.cappedMultiplicity right letter)
    (firstOccurrences :
      SemigroupBasis.Examples.firstOccurrenceSequence left.toList =
        SemigroupBasis.Examples.firstOccurrenceSequence right.toList) :
    leftSegments.map Prod.snd = rightSegments.map Prod.snd := by
  calc
    leftSegments.map Prod.snd = simpleProjection left.toList := by
      simpa [simpleProjection] using
        separatorSequence_eq_simpleProjection leftDecomposition
    _ = simpleProjection right.toList :=
      simpleProjection_eq_of_capped_firstOccurrences
        capped firstOccurrences
    _ = rightSegments.map Prod.snd := by
      simpa [simpleProjection] using
        (separatorSequence_eq_simpleProjection rightDecomposition).symm

/-! ## Structural assembly -/

/-- Segment lists are canonically aligned when corresponding separators agree
and corresponding gaps have the same ordered first-occurrence bank. -/
inductive CanonicalDecompositionAgreement :
    List (List Nat × Nat) → List Nat →
      List (List Nat × Nat) → List Nat → Prop where
  | final {leftFinal rightFinal : List Nat}
      (gapEq :
        S5_107.distinctLetters leftFinal =
          S5_107.distinctLetters rightFinal) :
      CanonicalDecompositionAgreement
        [] leftFinal [] rightFinal
  | step {leftGap rightGap : List Nat}
      {leftSeparator rightSeparator : Nat}
      {leftRest rightRest : List (List Nat × Nat)}
      {leftFinal rightFinal : List Nat}
      (gapEq :
        S5_107.distinctLetters leftGap =
          S5_107.distinctLetters rightGap)
      (separatorEq : leftSeparator = rightSeparator)
      (tail :
        CanonicalDecompositionAgreement
          leftRest leftFinal rightRest rightFinal) :
      CanonicalDecompositionAgreement
        ((leftGap, leftSeparator) :: leftRest) leftFinal
        ((rightGap, rightSeparator) :: rightRest) rightFinal

theorem renderCanonicalDecomposition_eq_of_agreement
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (agreement :
      CanonicalDecompositionAgreement
        leftSegments leftFinal rightSegments rightFinal) :
    renderCanonicalDecomposition leftSegments leftFinal =
      renderCanonicalDecomposition rightSegments rightFinal := by
  induction agreement with
  | final gapEq =>
      simp [renderCanonicalDecomposition, gapEq]
  | step gapEq separatorEq tail induction =>
      simp [renderCanonicalDecomposition, gapEq,
        separatorEq, induction]

/-! ## Generic separator recursion -/

/-- The four semantic obligations needed to align two globally-simple
separator decompositions.  A finite target proves this interface with its
table-specific support and first-occurrence probes; the recursive assembly
below is target-independent. -/
structure CanonicalGapOracle (left right : Word Nat) : Prop where
  whole :
    ∀ {leftGap rightGap : List Nat},
      left.toList = leftGap →
      right.toList = rightGap →
      S5_107.distinctLetters leftGap =
        S5_107.distinctLetters rightGap
  initial :
    ∀ {leftGap rightGap leftRemainder rightRemainder : List Nat}
      {separator : Nat},
      left.toList = leftGap ++ separator :: leftRemainder →
      right.toList = rightGap ++ separator :: rightRemainder →
      left.toList.count separator = 1 →
      right.toList.count separator = 1 →
      (∀ letter, letter ∈ leftGap →
        2 ≤ left.toList.count letter) →
      (∀ letter, letter ∈ rightGap →
        2 ≤ right.toList.count letter) →
      S5_107.distinctLetters leftGap =
        S5_107.distinctLetters rightGap
  interior :
    ∀ {leftBefore rightBefore leftGap rightGap
        leftAfter rightAfter : List Nat}
      {previous current : Nat},
      left.toList =
        leftBefore ++ previous :: (leftGap ++ current :: leftAfter) →
      right.toList =
        rightBefore ++ previous :: (rightGap ++ current :: rightAfter) →
      left.toList.count previous = 1 →
      right.toList.count previous = 1 →
      left.toList.count current = 1 →
      right.toList.count current = 1 →
      (∀ letter, letter ∈ leftGap →
        2 ≤ left.toList.count letter) →
      (∀ letter, letter ∈ rightGap →
        2 ≤ right.toList.count letter) →
      S5_107.distinctLetters leftGap =
        S5_107.distinctLetters rightGap
  final :
    ∀ {leftBefore rightBefore leftGap rightGap : List Nat}
      {separator : Nat},
      left.toList = leftBefore ++ separator :: leftGap →
      right.toList = rightBefore ++ separator :: rightGap →
      left.toList.count separator = 1 →
      right.toList.count separator = 1 →
      (∀ letter, letter ∈ leftGap →
        2 ≤ left.toList.count letter) →
      (∀ letter, letter ∈ rightGap →
        2 ≤ right.toList.count letter) →
      S5_107.distinctLetters leftGap =
        S5_107.distinctLetters rightGap

private theorem canonicalAgreement_eq_after
    (left right : Word Nat)
    (oracle : CanonicalGapOracle left right)
    {leftSource rightSource : List Nat}
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (leftDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        left.toList leftSource leftSegments leftFinal)
    (rightDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        right.toList rightSource rightSegments rightFinal)
    (previous : Nat)
    (leftPreviousSimple : left.toList.count previous = 1)
    (rightPreviousSimple : right.toList.count previous = 1)
    (leftBefore rightBefore : List Nat)
    (leftShape :
      left.toList = leftBefore ++ previous :: leftSource)
    (rightShape :
      right.toList = rightBefore ++ previous :: rightSource)
    (separatorEq :
      leftSegments.map Prod.snd = rightSegments.map Prod.snd) :
    CanonicalDecompositionAgreement
      leftSegments leftFinal rightSegments rightFinal := by
  induction leftDecomposition generalizing
      rightSource rightSegments rightFinal previous leftBefore rightBefore with
  | final leftGap leftRepeated =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          exact .final <|
            oracle.final leftShape rightShape
              leftPreviousSimple rightPreviousSimple
              leftRepeated rightRepeated
      | step rightGap rightSeparator rightRemainder rightRest
          rightFinal rightSeparatorSimple rightRepeated rightTail =>
          simp at separatorEq
  | step leftGap leftSeparator leftRemainder leftRest leftFinal
      leftSeparatorSimple leftRepeated leftTail leftInduction =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          simp at separatorEq
      | step rightGap rightSeparator rightRemainder rightRest
          rightFinal rightSeparatorSimple rightRepeated rightTail =>
          simp only [List.map_cons, List.cons.injEq] at separatorEq
          obtain ⟨separatorHeadEq, separatorTailEq⟩ := separatorEq
          subst rightSeparator
          have gapEq :=
            oracle.interior leftShape rightShape
              leftPreviousSimple rightPreviousSimple
              leftSeparatorSimple rightSeparatorSimple
              leftRepeated rightRepeated
          have leftTailShape :
              left.toList =
                (leftBefore ++ previous :: leftGap) ++
                  leftSeparator :: leftRemainder := by
            simpa [List.append_assoc] using leftShape
          have rightTailShape :
              right.toList =
                (rightBefore ++ previous :: rightGap) ++
                  leftSeparator :: rightRemainder := by
            simpa [List.append_assoc] using rightShape
          have tailAgreement :=
            leftInduction rightTail leftSeparator
              leftSeparatorSimple rightSeparatorSimple
              (leftBefore ++ previous :: leftGap)
              (rightBefore ++ previous :: rightGap)
              leftTailShape rightTailShape separatorTailEq
          exact .step gapEq rfl tailAgreement

private theorem canonicalAgreement_eq_from_start
    (left right : Word Nat)
    (oracle : CanonicalGapOracle left right)
    {leftSource rightSource : List Nat}
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (leftDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        left.toList leftSource leftSegments leftFinal)
    (rightDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        right.toList rightSource rightSegments rightFinal)
    (leftShape : left.toList = leftSource)
    (rightShape : right.toList = rightSource)
    (separatorEq :
      leftSegments.map Prod.snd = rightSegments.map Prod.snd) :
    CanonicalDecompositionAgreement
      leftSegments leftFinal rightSegments rightFinal := by
  cases leftDecomposition with
  | final leftGap leftRepeated =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          exact .final (oracle.whole leftShape rightShape)
      | step rightGap rightSeparator rightRemainder rightRest
          rightFinal rightSeparatorSimple rightRepeated rightTail =>
          simp at separatorEq
  | step leftGap leftSeparator leftRemainder leftRest leftFinal
      leftSeparatorSimple leftRepeated leftTail =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          simp at separatorEq
      | step rightGap rightSeparator rightRemainder rightRest
          rightFinal rightSeparatorSimple rightRepeated rightTail =>
          simp only [List.map_cons, List.cons.injEq] at separatorEq
          obtain ⟨separatorHeadEq, separatorTailEq⟩ := separatorEq
          subst rightSeparator
          have gapEq :=
            oracle.initial leftShape rightShape
              leftSeparatorSimple rightSeparatorSimple
              leftRepeated rightRepeated
          have tailAgreement :=
            canonicalAgreement_eq_after left right oracle
              leftTail rightTail leftSeparator
              leftSeparatorSimple rightSeparatorSimple
              leftGap rightGap leftShape rightShape separatorTailEq
          exact .step gapEq rfl tailAgreement

/-- A target-specific four-case oracle plus aligned separator labels yields
the full canonical-decomposition agreement. -/
theorem canonicalDecompositionAgreement_of_oracle
    (left right : Word Nat)
    (oracle : CanonicalGapOracle left right)
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (leftDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        left.toList left.toList leftSegments leftFinal)
    (rightDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        right.toList right.toList rightSegments rightFinal)
    (separatorEq :
      leftSegments.map Prod.snd = rightSegments.map Prod.snd) :
    CanonicalDecompositionAgreement
      leftSegments leftFinal rightSegments rightFinal :=
  canonicalAgreement_eq_from_start
    left right oracle leftDecomposition rightDecomposition
      rfl rfl separatorEq

end SemigroupBasis.CoRoots.Order6PublishedMonoid14

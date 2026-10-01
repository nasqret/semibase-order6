import SemigroupBasis.CoRoots.Order6SporadicSection12A2Semantics
import SemigroupBasis.CoRoots.S5_530Normalization

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots
open S5_207.DirectCompletenessArchitecture

namespace A2Canonical

/-- First-occurrence blocks of length one or two. -/
inductive PrefixNormal : List Nat -> Prop
  | nil : PrefixNormal []
  | single (letter : Nat) (rest : List Nat) :
      PrefixNormal rest -> letter ∉ rest ->
        PrefixNormal (letter :: rest)
  | double (letter : Nat) (rest : List Nat) :
      PrefixNormal rest -> letter ∉ rest ->
        PrefixNormal (letter :: letter :: rest)

namespace PrefixNormal

theorem toS5_530Normal {letters : List Nat}
    (normal : PrefixNormal letters) :
    S5_530.S5_530Normal letters := by
  induction normal with
  | nil => exact .nil
  | single letter rest _ absent induction =>
      exact .single letter rest induction absent
  | double letter rest _ absent induction =>
      exact .double letter rest induction absent

theorem count_le_two {letters : List Nat}
    (normal : PrefixNormal letters) :
    ∀ tested, letters.count tested ≤ 2 := by
  induction normal with
  | nil => simp
  | single letter rest _ absent induction =>
      intro tested
      by_cases equal : tested = letter
      · subst tested
        simp [List.count_eq_zero.mpr absent]
      · rw [List.count_cons_of_ne (Ne.symm equal)]
        exact induction tested
  | double letter rest _ absent induction =>
      intro tested
      by_cases equal : tested = letter
      · subst tested
        simp [List.count_eq_zero.mpr absent]
      · rw [List.count_cons_of_ne (Ne.symm equal),
          List.count_cons_of_ne (Ne.symm equal)]
        exact induction tested

end PrefixNormal

private theorem mem_renderBlocks_iff
    (source : List Nat) (selected : Nat) :
    ∀ labels : List Nat,
      selected ∈ labels.flatMap (S5_345.saturatedBlock source) ↔
        selected ∈ labels
  | [] => by simp
  | label :: rest => by
      rw [List.flatMap_cons, List.mem_append,
        mem_renderBlocks_iff source selected rest]
      by_cases single : source.count label = 1 <;>
        simp [S5_345.saturatedBlock, single]

private theorem renderBlocks_normal
    (source : List Nat) :
    ∀ labels : List Nat, labels.Nodup ->
      PrefixNormal
        (labels.flatMap (S5_345.saturatedBlock source))
  | [], _ => .nil
  | label :: rest, nodup => by
      have tailNormal :=
        renderBlocks_normal source rest (List.nodup_cons.mp nodup).2
      have absent :
          label ∉ rest.flatMap (S5_345.saturatedBlock source) := by
        intro member
        exact (List.nodup_cons.mp nodup).1 <|
          (mem_renderBlocks_iff source label rest).1 member
      by_cases single : source.count label = 1
      · simpa [S5_345.saturatedBlock, single] using
          PrefixNormal.single label _ tailNormal absent
      · simpa [S5_345.saturatedBlock, single] using
          PrefixNormal.double label _ tailNormal absent

theorem doubleCanonicalList_normal (source : List Nat) :
    PrefixNormal (S5_345.doubleCanonicalList source) := by
  rw [S5_345.doubleCanonicalList_eq_saturatedCanonicalList]
  unfold S5_345.saturatedCanonicalList
  exact renderBlocks_normal source
    (firstOccurrenceSequence source)
    (firstOccurrenceSequence_nodup source)

private theorem count_renderBlocks
    (source : List Nat) (selected : Nat) :
    ∀ labels : List Nat, labels.Nodup ->
      (labels.flatMap
          (S5_345.saturatedBlock source)).count selected =
        if selected ∈ labels then
          if source.count selected = 1 then 1 else 2
        else
          0
  | [], _ => by simp
  | label :: rest, nodup => by
      have restNodup := (List.nodup_cons.mp nodup).2
      have labelAbsent := (List.nodup_cons.mp nodup).1
      have induction := count_renderBlocks source selected rest restNodup
      rw [List.flatMap_cons, List.count_append, induction]
      by_cases equal : selected = label
      · subst label
        by_cases single : source.count selected = 1 <;>
          simp [S5_345.saturatedBlock, single, labelAbsent]
      · by_cases blockSingle : source.count label = 1 <;>
          simp [S5_345.saturatedBlock, blockSingle, equal, Ne.symm equal]

/-- The cap-two block renderer has the advertised exact multiplicities. -/
theorem count_doubleCanonicalList
    (source : List Nat) (selected : Nat) :
    (S5_345.doubleCanonicalList source).count selected =
      A2Normalization.prefixMultiplicity source selected := by
  rw [S5_345.doubleCanonicalList_eq_saturatedCanonicalList]
  unfold S5_345.saturatedCanonicalList
  rw [count_renderBlocks source selected
    (firstOccurrenceSequence source)
    (firstOccurrenceSequence_nodup source)]
  by_cases zero : source.count selected = 0
  · have absent : selected ∉ firstOccurrenceSequence source := by
      rw [S5_345.mem_firstOccurrenceSequence_iff]
      exact List.count_eq_zero.mp zero
    simp [absent, A2Normalization.prefixMultiplicity, zero]
  · have member : selected ∈ firstOccurrenceSequence source := by
      rw [S5_345.mem_firstOccurrenceSequence_iff]
      exact List.count_pos_iff.mp (Nat.pos_of_ne_zero zero)
    by_cases one : source.count selected = 1
    · simp [member, one, A2Normalization.prefixMultiplicity]
    · have multiple : 2 ≤ source.count selected := by omega
      simp [member, one, A2Normalization.prefixMultiplicity,
        Nat.min_eq_left multiple]

private theorem firstOccurrences_single
    {letter : Nat} {rest : List Nat} (absent : letter ∉ rest) :
    firstOccurrenceSequence (letter :: rest) =
      letter :: firstOccurrenceSequence rest := by
  simp only [firstOccurrenceSequence]
  congr 1
  apply List.filter_eq_self.mpr
  intro selected member
  simp only [decide_eq_true_eq]
  intro equal
  subst selected
  exact absent <|
    (S5_345.mem_firstOccurrenceSequence_iff letter rest).1 member

private theorem firstOccurrences_double
    {letter : Nat} {rest : List Nat} (absent : letter ∉ rest) :
    firstOccurrenceSequence (letter :: letter :: rest) =
      letter :: firstOccurrenceSequence rest := by
  have filtered :
      (firstOccurrenceSequence rest).filter
          (fun selected => decide (selected ≠ letter)) =
        firstOccurrenceSequence rest := by
    apply List.filter_eq_self.mpr
    intro selected member
    simp only [decide_eq_true_eq]
    intro equal
    subst selected
    exact absent <|
      (S5_345.mem_firstOccurrenceSequence_iff letter rest).1 member
  rw [firstOccurrenceSequence, firstOccurrences_single absent]
  rw [List.filter_cons_of_neg (by simp)]
  exact congrArg (List.cons letter) filtered

private theorem firstOccurrences_renderBlocks
    (source : List Nat) :
    ∀ labels : List Nat, labels.Nodup ->
      firstOccurrenceSequence
          (labels.flatMap (S5_345.saturatedBlock source)) = labels
  | [], _ => rfl
  | label :: rest, nodup => by
      have restNodup := (List.nodup_cons.mp nodup).2
      have induction :=
        firstOccurrences_renderBlocks source rest restNodup
      have absent :
          label ∉ rest.flatMap (S5_345.saturatedBlock source) := by
        intro member
        exact (List.nodup_cons.mp nodup).1 <|
          (mem_renderBlocks_iff source label rest).1 member
      by_cases single : source.count label = 1
      · have blockShape :
            S5_345.saturatedBlock source label = [label] := by
          simp [S5_345.saturatedBlock, single]
        rw [List.flatMap_cons, blockShape]
        change firstOccurrenceSequence
          (label :: rest.flatMap (S5_345.saturatedBlock source)) =
            label :: rest
        rw [firstOccurrences_single absent, induction]
      · have blockShape :
            S5_345.saturatedBlock source label = [label, label] := by
          simp [S5_345.saturatedBlock, single]
        rw [List.flatMap_cons, blockShape]
        change firstOccurrenceSequence
          (label :: label ::
            rest.flatMap (S5_345.saturatedBlock source)) =
              label :: rest
        rw [firstOccurrences_double absent, induction]

/-- Cap-two rendering preserves the sequence of first occurrences. -/
theorem firstOccurrences_doubleCanonicalList (source : List Nat) :
    firstOccurrenceSequence (S5_345.doubleCanonicalList source) =
      firstOccurrenceSequence source := by
  rw [S5_345.doubleCanonicalList_eq_saturatedCanonicalList]
  unfold S5_345.saturatedCanonicalList
  exact firstOccurrences_renderBlocks source
    (firstOccurrenceSequence source)
    (firstOccurrenceSequence_nodup source)

/-- Cap-two block lists are uniquely determined by first-occurrence order and
their capped multiplicities. -/
theorem prefixNormal_eq_of_invariants
    {left right : List Nat}
    (leftNormal : PrefixNormal left)
    (rightNormal : PrefixNormal right)
    (order :
      firstOccurrenceSequence left =
        firstOccurrenceSequence right)
    (capped :
      ∀ letter,
        A2Normalization.prefixMultiplicity left letter =
          A2Normalization.prefixMultiplicity right letter) :
    left = right := by
  apply S5_530.s5_530Normal_eq_of_invariants
    leftNormal.toS5_530Normal rightNormal.toS5_530Normal order
  intro letter
  have leftBound := leftNormal.count_le_two letter
  have rightBound := rightNormal.count_le_two letter
  have equality := capped letter
  unfold A2Normalization.prefixMultiplicity at equality
  simp only [Nat.min_def] at equality
  split at equality <;> split at equality <;> omega

/-- Condition (II) of the paper's display (12.2). -/
def ConditionII (stem : List Nat) (final : Nat) : Prop :=
  ∀ before after,
    firstOccurrenceSequence stem = before ++ final :: after ->
    stem.count final = 2 ->
    ∀ letter, letter ∈ before -> stem.count letter = 1

private theorem splitPrefix_unique
    (marker : Nat) :
    ∀ (left right leftTail rightTail : List Nat),
      left ++ marker :: leftTail = right ++ marker :: rightTail ->
      marker ∉ left -> marker ∉ right -> left = right
  | [], [], _, _, _, _, _ => rfl
  | [], head :: tail, leftTail, rightTail, equality,
      _, markerNotRight => by
      have heads : marker = head := by
        simpa using congrArg (fun xs : List Nat => xs.head?) equality
      subst head
      exact False.elim (markerNotRight (by simp))
  | head :: tail, [], leftTail, rightTail, equality,
      markerNotLeft, _ => by
      have heads : head = marker := by
        simpa using congrArg (fun xs : List Nat => xs.head?) equality
      subst head
      exact False.elim (markerNotLeft (by simp))
  | leftHead :: leftRest, rightHead :: rightRest,
      leftTail, rightTail, equality, markerNotLeft, markerNotRight => by
      have heads : leftHead = rightHead := by
        simpa using congrArg (fun xs : List Nat => xs.head?) equality
      subst rightHead
      have tails :
          leftRest ++ marker :: leftTail =
            rightRest ++ marker :: rightTail := by
        simpa using congrArg (fun xs : List Nat => xs.tail) equality
      have markerNotLeftRest : marker ∉ leftRest := by
        intro member
        exact markerNotLeft (by simp [member])
      have markerNotRightRest : marker ∉ rightRest := by
        intro member
        exact markerNotRight (by simp [member])
      exact congrArg (List.cons leftHead) <|
        splitPrefix_unique marker leftRest rightRest
          leftTail rightTail tails
          markerNotLeftRest markerNotRightRest

private theorem not_mem_before_of_nodup_split
    {whole before after : List Nat} {marker : Nat}
    (nodup : whole.Nodup)
    (split : whole = before ++ marker :: after) :
    marker ∉ before := by
  have splitNodup : (before ++ marker :: after).Nodup := by
    rw [← split]
    exact nodup
  intro member
  exact (List.nodup_append.mp splitNodup).2.2
    marker member marker (by simp) rfl

/-- The deterministic terminal-owner repair satisfies condition (II). -/
theorem repaired_conditionII
    (sourcePrefix : List Nat) (oldFinal : Nat) :
    ConditionII
      (S5_345.doubleCanonicalList sourcePrefix)
      (A2Normalization.terminalOwner sourcePrefix oldFinal) := by
  by_cases finalDouble :
      A2Normalization.prefixMultiplicity sourcePrefix oldFinal = 2
  · have finalMember : oldFinal ∈ firstOccurrenceSequence sourcePrefix := by
      rw [S5_345.mem_firstOccurrenceSequence_iff]
      apply List.count_pos_iff.mp
      have :=
        (A2Normalization.prefixMultiplicity_eq_two_iff
          sourcePrefix oldFinal).1 finalDouble
      omega
    obtain
        ⟨marker, selectedBefore, markerTail, firstShape, labelsShape,
          beforeNonmultiple, markerDouble⟩ :=
      S5_345.firstMultiple_split_of_exists
        (A2Normalization.prefixMultiplicity sourcePrefix)
        (firstOccurrenceSequence sourcePrefix)
        ⟨oldFinal, finalMember, finalDouble⟩
    have ownerShape :
        A2Normalization.terminalOwner sourcePrefix oldFinal = marker := by
      simp [A2Normalization.terminalOwner, finalDouble, firstShape]
    rw [ownerShape]
    intro before after order markerCount letter member
    have orderSource :
        firstOccurrenceSequence sourcePrefix =
          before ++ marker :: after := by
      rw [← firstOccurrences_doubleCanonicalList sourcePrefix]
      exact order
    have labelsNodup := firstOccurrenceSequence_nodup sourcePrefix
    have markerNotSelected : marker ∉ selectedBefore :=
      not_mem_before_of_nodup_split labelsNodup labelsShape
    have markerNotBefore : marker ∉ before :=
      not_mem_before_of_nodup_split labelsNodup orderSource
    have beforeEq : selectedBefore = before :=
      splitPrefix_unique marker selectedBefore before
        markerTail after (labelsShape.symm.trans orderSource)
        markerNotSelected markerNotBefore
    rw [← beforeEq] at member
    have sourceMember : letter ∈ sourcePrefix :=
      (S5_345.mem_firstOccurrenceSequence_iff letter sourcePrefix).1 <|
        by rw [labelsShape]; exact List.mem_append_left _ member
    have positive : 0 < sourcePrefix.count letter :=
      List.count_pos_iff.mpr sourceMember
    have notDouble := beforeNonmultiple letter member
    have sourceCountOne : sourcePrefix.count letter = 1 := by
      apply Decidable.byContradiction
      intro notOne
      have atLeastTwo : 2 ≤ sourcePrefix.count letter := by omega
      exact notDouble <|
        (A2Normalization.prefixMultiplicity_eq_two_iff
          sourcePrefix letter).2 atLeastTwo
    rw [count_doubleCanonicalList]
    simp [A2Normalization.prefixMultiplicity, sourceCountOne]
  · have ownerShape :
        A2Normalization.terminalOwner sourcePrefix oldFinal = oldFinal := by
      simp [A2Normalization.terminalOwner, finalDouble]
    rw [ownerShape]
    intro _ _ _ outputDouble
    have outputCount := count_doubleCanonicalList sourcePrefix oldFinal
    rw [outputDouble] at outputCount
    exact False.elim <| finalDouble outputCount.symm

/-- Explicit canonical witness used by the unrestricted proof interface. -/
structure Shape (word : Word Nat) : Type where
  stem : List Nat
  final : Nat
  word_eq : word = wordOfPrefixFinal stem final
  prefixNormal : PrefixNormal stem
  conditionII : ConditionII stem final

private def canonicalWord_shape_from
    (source : Word Nat) : Shape (A2Normalization.canonicalWord source) := by
  cases source with
  | mk head tail =>
      let letters := head :: tail
      let oldFinal := tail.getLastD head
      let sourcePrefix := letters.dropLast
      let stem := S5_345.doubleCanonicalList sourcePrefix
      let final := A2Normalization.terminalOwner sourcePrefix oldFinal
      refine
        ⟨stem, final, ?_,
          doubleCanonicalList_normal sourcePrefix,
          repaired_conditionII sourcePrefix oldFinal⟩
      apply Word.toList_injective
      rw [A2Normalization.toList_canonicalWord,
        toList_wordOfPrefixFinal]
      change
        A2Normalization.canonicalList (head :: tail) =
          S5_345.doubleCanonicalList (head :: tail).dropLast ++
            [A2Normalization.terminalOwner
              (head :: tail).dropLast (tail.getLastD head)]
      rfl

private theorem shapeOfCanonical_nonempty
    {word : Word Nat} (canonical : A2Normalization.Canonical word) :
    Nonempty (Shape word) := by
  rcases canonical with ⟨source, rfl⟩
  exact ⟨canonicalWord_shape_from source⟩

noncomputable def shapeOfCanonical
    {word : Word Nat} (canonical : A2Normalization.Canonical word) :
    Shape word :=
  Classical.choice (shapeOfCanonical_nonempty canonical)

private theorem prefixCounts_eq
    {left right : Word Nat}
    (leftShape : Shape left) (rightShape : Shape right)
    (same : A2Semantics.SameSignature left right) :
    ∀ letter,
      leftShape.stem.count letter =
        rightShape.stem.count letter := by
  intro letter
  have stateEq := same.marker letter
  rw [leftShape.word_eq, rightShape.word_eq,
    markerState_wordOfPrefixFinal,
    markerState_wordOfPrefixFinal] at stateEq
  have cappedEq := congrArg prefixMultiplicityOfState stateEq
  have leftBound := leftShape.prefixNormal.count_le_two letter
  have rightBound := rightShape.prefixNormal.count_le_two letter
  simpa [splitMarkerState,
    Nat.min_eq_left leftBound,
    Nat.min_eq_left rightBound] using cappedEq

private theorem prefixOrder_eq_of_final_eq
    {left right : Word Nat}
    (leftShape : Shape left) (rightShape : Shape right)
    (same : A2Semantics.SameSignature left right)
    (finalEq : leftShape.final = rightShape.final) :
    firstOccurrenceSequence leftShape.stem =
      firstOccurrenceSequence rightShape.stem := by
  have wholeOrder := same.firstOccurrences
  rw [leftShape.word_eq, rightShape.word_eq,
    toList_wordOfPrefixFinal, toList_wordOfPrefixFinal,
    S5_345.firstOccurrenceSequence_append_final,
    S5_345.firstOccurrenceSequence_append_final] at wholeOrder
  rw [← finalEq] at wholeOrder
  have counts := prefixCounts_eq leftShape rightShape same
  by_cases leftMember : leftShape.final ∈ leftShape.stem
  · have rightMember : leftShape.final ∈ rightShape.stem := by
      apply List.count_pos_iff.mp
      rw [← counts leftShape.final]
      exact List.count_pos_iff.mpr leftMember
    simpa [leftMember, rightMember] using wholeOrder
  · have rightAbsent : leftShape.final ∉ rightShape.stem := by
      apply List.count_eq_zero.mp
      rw [← counts leftShape.final]
      exact List.count_eq_zero.mpr leftMember
    simp [leftMember, rightAbsent] at wholeOrder
    exact wholeOrder

private theorem final_eq_of_sameSignature
    {left right : Word Nat}
    (leftShape : Shape left) (rightShape : Shape right)
    (same : A2Semantics.SameSignature left right) :
    leftShape.final = rightShape.final := by
  apply Decidable.byContradiction
  intro finalsNe
  have leftMarker :
      markerState
          (wordOfPrefixFinal leftShape.stem leftShape.final)
          leftShape.final =
        markerState
          (wordOfPrefixFinal rightShape.stem rightShape.final)
          leftShape.final := by
    calc
      _ = markerState left leftShape.final :=
        congrArg (fun word => markerState word leftShape.final)
          leftShape.word_eq.symm
      _ = markerState right leftShape.final :=
        same.marker leftShape.final
      _ = _ :=
        congrArg (fun word => markerState word leftShape.final)
          rightShape.word_eq
  rw [markerState_wordOfPrefixFinal,
    markerState_wordOfPrefixFinal] at leftMarker
  have leftForced :=
    S5_207.markerStateFrom_true_false_forces_two
    (leftShape.stem.count leftShape.final)
    (rightShape.stem.count leftShape.final) <| by
      simpa only [splitMarkerState, beq_self_eq_true,
        beq_eq_false_iff_ne.mpr (Ne.symm finalsNe)] using leftMarker
  have rightMarker :
      markerState
          (wordOfPrefixFinal leftShape.stem leftShape.final)
          rightShape.final =
        markerState
          (wordOfPrefixFinal rightShape.stem rightShape.final)
          rightShape.final := by
    calc
      _ = markerState left rightShape.final :=
        congrArg (fun word => markerState word rightShape.final)
          leftShape.word_eq.symm
      _ = markerState right rightShape.final :=
        same.marker rightShape.final
      _ = _ :=
        congrArg (fun word => markerState word rightShape.final)
          rightShape.word_eq
  rw [markerState_wordOfPrefixFinal,
    markerState_wordOfPrefixFinal] at rightMarker
  have rightForced :=
    S5_207.markerStateFrom_false_true_forces_two
    (leftShape.stem.count rightShape.final)
    (rightShape.stem.count rightShape.final) <| by
      simpa only [splitMarkerState, beq_self_eq_true,
        beq_eq_false_iff_ne.mpr finalsNe] using rightMarker
  have leftFinalCount : leftShape.stem.count leftShape.final = 2 := by
    have bound := leftShape.prefixNormal.count_le_two leftShape.final
    simpa [Nat.min_eq_left bound] using leftForced.1
  have rightFinalCount :
      rightShape.stem.count rightShape.final = 2 := by
    have bound := rightShape.prefixNormal.count_le_two rightShape.final
    simpa [Nat.min_eq_left bound] using rightForced.2
  have counts := prefixCounts_eq leftShape rightShape same
  have leftOtherCount : leftShape.stem.count rightShape.final = 2 := by
    rw [counts rightShape.final]
    exact rightFinalCount
  have rightOtherCount : rightShape.stem.count leftShape.final = 2 := by
    rw [← counts leftShape.final]
    exact leftFinalCount
  have leftFinalMember : leftShape.final ∈ leftShape.stem :=
    List.count_pos_iff.mp (by omega)
  have rightFinalMember : rightShape.final ∈ rightShape.stem :=
    List.count_pos_iff.mp (by omega)
  have prefixOrder :
      firstOccurrenceSequence leftShape.stem =
        firstOccurrenceSequence rightShape.stem := by
    have wholeOrder := same.firstOccurrences
    rw [leftShape.word_eq, rightShape.word_eq,
      toList_wordOfPrefixFinal, toList_wordOfPrefixFinal,
      S5_345.firstOccurrenceSequence_append_final,
      S5_345.firstOccurrenceSequence_append_final,
      if_pos leftFinalMember, if_pos rightFinalMember] at wholeOrder
    exact wholeOrder
  have leftFinalLabel :
      leftShape.final ∈ firstOccurrenceSequence leftShape.stem :=
    (S5_345.mem_firstOccurrenceSequence_iff
      leftShape.final leftShape.stem).2 leftFinalMember
  obtain ⟨leftSplit, leftSplitShape⟩ :=
    S5_345.splitFirst_some_of_mem leftShape.final leftFinalLabel
  have leftOrderShape :
      firstOccurrenceSequence leftShape.stem =
        leftSplit.before ++ leftShape.final :: leftSplit.after :=
    S5_345.splitFirst_reconstruction
      leftShape.final _ leftSplit leftSplitShape
  have rightFinalInLeftOrder :
      rightShape.final ∈ firstOccurrenceSequence leftShape.stem := by
    rw [prefixOrder]
    exact
      (S5_345.mem_firstOccurrenceSequence_iff
        rightShape.final rightShape.stem).2 rightFinalMember
  rw [leftOrderShape] at rightFinalInLeftOrder
  rcases List.mem_append.mp rightFinalInLeftOrder with
    rightBefore | rightAtOrAfter
  · have forcedOne :=
      leftShape.conditionII leftSplit.before leftSplit.after
        leftOrderShape leftFinalCount rightShape.final rightBefore
    omega
  · rcases List.mem_cons.mp rightAtOrAfter with
      finalsEq | rightInTail
    · exact finalsNe finalsEq.symm
    · obtain ⟨rightSplit, rightSplitShape⟩ :=
        S5_345.splitFirst_some_of_mem rightShape.final rightInTail
      have tailShape :
          leftSplit.after =
            rightSplit.before ++ rightShape.final :: rightSplit.after :=
        S5_345.splitFirst_reconstruction
          rightShape.final _ rightSplit rightSplitShape
      have rightOrderShape :
          firstOccurrenceSequence rightShape.stem =
            (leftSplit.before ++
              leftShape.final :: rightSplit.before) ++
              rightShape.final :: rightSplit.after := by
        rw [← prefixOrder, leftOrderShape, tailShape]
        simp [List.append_assoc]
      have leftInRightBefore :
          leftShape.final ∈
            leftSplit.before ++ leftShape.final :: rightSplit.before := by
        simp
      have forcedOne :=
        rightShape.conditionII
          (leftSplit.before ++ leftShape.final :: rightSplit.before)
          rightSplit.after rightOrderShape rightFinalCount
          leftShape.final leftInRightBefore
      omega

/-- Canonical A2 representatives with the same exact semantic signature are
literally equal. -/
theorem canonical_eq_of_sameSignature
    {left right : Word Nat}
    (leftCanonical : A2Normalization.Canonical left)
    (rightCanonical : A2Normalization.Canonical right)
    (same : A2Semantics.SameSignature left right) :
    left = right := by
  let leftShape := shapeOfCanonical leftCanonical
  let rightShape := shapeOfCanonical rightCanonical
  have finalEq := final_eq_of_sameSignature leftShape rightShape same
  have orderEq :=
    prefixOrder_eq_of_final_eq leftShape rightShape same finalEq
  have countsEq := prefixCounts_eq leftShape rightShape same
  have cappedEq :
      ∀ letter,
        A2Normalization.prefixMultiplicity leftShape.stem letter =
          A2Normalization.prefixMultiplicity rightShape.stem letter := by
    intro letter
    simp [A2Normalization.prefixMultiplicity, countsEq letter]
  have prefixEq := prefixNormal_eq_of_invariants
    leftShape.prefixNormal rightShape.prefixNormal orderEq cappedEq
  rw [leftShape.word_eq, rightShape.word_eq, finalEq, prefixEq]

/-- Semantic uniqueness in the exact A2 table. -/
theorem uniqueOfValid
    (left right : Word Nat)
    (leftCanonical : A2Normalization.Canonical left)
    (rightCanonical : A2Normalization.Canonical right)
    (valid :
      (Identity.mk left right).SatisfiedBy S6_5597.table.semigroup) :
    left = right :=
  canonical_eq_of_sameSignature leftCanonical rightCanonical
    (A2Semantics.valid_sameSignature ⟨left, right⟩ valid)

def canonicalProof : UnrestrictedCanonicalProof S6_5597.table a2Basis :=
  A2Normalization.unrestrictedCanonicalProofOfUnique uniqueOfValid

theorem basisFor : BasisFor S6_5597.table.semigroup a2Basis :=
  S6_5597.basisFor_of_canonicalProof canonicalProof

theorem oppositeBasisFor :
    BasisFor S6_5597.table.semigroup.opposite a2OppositeBasis :=
  S6_5597.oppositeBasisFor_of_canonicalProof canonicalProof

end A2Canonical

end SemigroupBasis.CoRoots.Order6SporadicSection12

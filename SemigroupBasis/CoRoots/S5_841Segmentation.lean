import SemigroupBasis.CoRoots.S5_841BlockPermutation
import SemigroupBasis.Examples.LeftRegularBandThree

namespace SemigroupBasis.CoRoots.S5_841

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Globally singleton projections -/

/-- Retain the letters of `letters` that are globally singleton in `whole`. -/
private def simpleProjection
    (whole letters : List Nat) : List Nat :=
  letters.filter fun letter => decide (whole.count letter = 1)

private theorem filter_filter_ne_comm
    (keep : Nat → Bool) (selected : Nat)
    (letters : List Nat) :
    (letters.filter keep).filter
        (fun letter => decide (letter ≠ selected)) =
      (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro letter _
  exact Bool.and_comm _ _

private theorem filter_ne_then_keep_of_drop
    (keep : Nat → Bool) (selected : Nat)
    (dropped : ¬keep selected)
    (letters : List Nat) :
    (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep =
      letters.filter keep := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro letter _
  by_cases equal : letter = selected
  · subst letter
    simp [dropped]
  · simp [equal]

private theorem firstOccurrenceSequence_filter
    (keep : Nat → Bool) :
    ∀ letters : List Nat,
      firstOccurrenceSequence (letters.filter keep) =
        (firstOccurrenceSequence letters).filter keep
  | [] => rfl
  | letter :: rest => by
      by_cases kept : keep letter
      · rw [List.filter_cons, if_pos kept,
          firstOccurrenceSequence, firstOccurrenceSequence,
          firstOccurrenceSequence_filter keep rest,
          List.filter_cons, if_pos kept]
        exact congrArg (List.cons letter) <|
          filter_filter_ne_comm keep letter
            (firstOccurrenceSequence rest)
      · rw [List.filter_cons, if_neg kept,
          firstOccurrenceSequence_filter keep rest,
          firstOccurrenceSequence,
          List.filter_cons, if_neg kept]
        exact
          (filter_ne_then_keep_of_drop
            keep letter kept (firstOccurrenceSequence rest)).symm

private theorem firstOccurrenceSequence_eq_self_of_nodup
    {letters : List Nat} (nodup : letters.Nodup) :
    firstOccurrenceSequence letters = letters := by
  induction letters with
  | nil => rfl
  | cons letter rest induction =>
      have data := List.nodup_cons.mp nodup
      rw [firstOccurrenceSequence, induction data.2]
      congr 1
      apply List.filter_eq_self.mpr
      intro next member
      exact decide_eq_true <| by
        intro equal
        subst next
        exact data.1 member

private theorem nodup_of_count_le_one
    {letters : List Nat}
    (bounded : ∀ letter, letters.count letter ≤ 1) :
    letters.Nodup := by
  induction letters with
  | nil => simp
  | cons first rest induction =>
      simp only [List.nodup_cons]
      constructor
      · intro member
        have positive : 1 ≤ rest.count first :=
          List.count_pos_iff.mpr member
        have bound := bounded first
        simp only [List.count_cons_self] at bound
        omega
      · apply induction
        intro letter
        have bound := bounded letter
        by_cases equal : first = letter
        · subst first
          simp only [List.count_cons_self] at bound
          omega
        · simpa [equal] using bound

private theorem simpleProjection_self_nodup (letters : List Nat) :
    (simpleProjection letters letters).Nodup := by
  apply nodup_of_count_le_one
  intro letter
  by_cases simple : letters.count letter = 1
  · exact Nat.le_trans
      (List.filter_sublist.count_le letter) (by omega)
  · have absent : letter ∉ simpleProjection letters letters := by
      intro member
      have kept := (List.mem_filter.mp member).2
      simp [simpleProjection, simple] at kept
    rw [List.count_eq_zero.mpr absent]
    omega

private theorem simpleProjection_self_eq_firstOccurrenceFilter
    (letters : List Nat) :
    simpleProjection letters letters =
      (firstOccurrenceSequence letters).filter
        (fun letter => decide (letters.count letter = 1)) := by
  calc
    simpleProjection letters letters =
        firstOccurrenceSequence (simpleProjection letters letters) :=
      (firstOccurrenceSequence_eq_self_of_nodup
        (simpleProjection_self_nodup letters)).symm
    _ = _ := by
      simpa [simpleProjection] using
        firstOccurrenceSequence_filter
          (fun letter => decide (letters.count letter = 1)) letters

private theorem simpleProjection_congr
    {leftWhole rightWhole : List Nat}
    (counts : ∀ letter, leftWhole.count letter = rightWhole.count letter)
    (letters : List Nat) :
    simpleProjection leftWhole letters =
      simpleProjection rightWhole letters := by
  unfold simpleProjection
  apply List.filter_congr
  intro letter _
  simp [counts letter]

private theorem simpleProjection_cons_split
    (pre tail : List Nat) (separator : Nat) (remaining : List Nat)
    (projection :
      simpleProjection (pre ++ tail) tail = separator :: remaining) :
    ∃ before after,
      tail = before ++ separator :: after ∧
      (∀ letter, letter ∈ before →
        (pre ++ tail).count letter ≠ 1) ∧
      simpleProjection (pre ++ tail) after = remaining ∧
      (pre ++ tail).count separator = 1 := by
  have separatorProjected :
      separator ∈ simpleProjection (pre ++ tail) tail := by
    rw [projection]
    simp
  have separatorData := List.mem_filter.mp separatorProjected
  have separatorInTail : separator ∈ tail := separatorData.1
  have separatorSimple : (pre ++ tail).count separator = 1 := by
    simpa [simpleProjection] using separatorData.2
  obtain ⟨before, after, tailShape⟩ :=
    List.append_of_mem separatorInTail
  have separatorSimpleShaped :
      (pre ++ (before ++ separator :: after)).count separator = 1 := by
    simpa [tailShape] using separatorSimple
  have separatorNotBefore : separator ∉ before := by
    intro member
    have positive : 1 ≤ before.count separator :=
      List.one_le_count_iff.mpr member
    simp only [List.count_append, List.count_cons_self] at separatorSimpleShaped
    omega
  have expanded :
      simpleProjection (pre ++ tail) before ++
        separator :: simpleProjection (pre ++ tail) after =
      separator :: remaining := by
    have expandedProjection := projection
    rw [tailShape] at expandedProjection
    unfold simpleProjection at expandedProjection
    rw [List.filter_append] at expandedProjection
    have separatorKept :
        decide
            ((pre ++ (before ++ separator :: after)).count separator = 1) =
          true := by
      simp [separatorSimpleShaped]
    rw [List.filter_cons, if_pos separatorKept] at expandedProjection
    simpa [simpleProjection, tailShape, List.append_assoc] using
      expandedProjection
  have beforeEmpty :
      simpleProjection (pre ++ tail) before = [] := by
    cases beforeProjection : simpleProjection (pre ++ tail) before with
    | nil => rfl
    | cons first rest =>
        rw [beforeProjection] at expanded
        simp only [List.cons_append] at expanded
        have firstEqual : first = separator := by
          injection expanded
        subst first
        have separatorProjectedBefore :
            separator ∈ simpleProjection (pre ++ tail) before := by
          rw [beforeProjection]
          simp
        have separatorBefore : separator ∈ before :=
          (List.mem_filter.mp separatorProjectedBefore).1
        exact False.elim (separatorNotBefore separatorBefore)
  have afterProjection :
      simpleProjection (pre ++ tail) after = remaining := by
    rw [beforeEmpty] at expanded
    simpa using expanded
  have beforeNonlinear :
      ∀ letter, letter ∈ before →
        (pre ++ tail).count letter ≠ 1 := by
    intro letter member countOne
    have projected :
        letter ∈ simpleProjection (pre ++ tail) before :=
      List.mem_filter.mpr ⟨member, by simp [countOne]⟩
    rw [beforeEmpty] at projected
    simp at projected
  exact
    ⟨before, after, tailShape, beforeNonlinear,
      afterProjection, separatorSimple⟩

private theorem nonlinear_of_simpleProjection_nil
    (whole letters : List Nat)
    (projection : simpleProjection whole letters = []) :
    ∀ letter, letter ∈ letters → whole.count letter ≠ 1 := by
  intro letter member countOne
  have projected : letter ∈ simpleProjection whole letters :=
    List.mem_filter.mpr ⟨member, by simp [countOne]⟩
  rw [projection] at projected
  simp at projected

/-! ## Complete precedence orders the singleton projection -/

private def pairKeep (x y value : Nat) : Bool :=
  value == x || value == y

private def pairProjection
    (letters : List Nat) (x y : Nat) : List Nat :=
  letters.filter (pairKeep x y)

private theorem count_filter_of_kept
    (letters : List Nat) (keep : Nat → Bool) (letter : Nat)
    (kept : keep letter = true) :
    (letters.filter keep).count letter = letters.count letter := by
  induction letters with
  | nil => simp
  | cons first rest induction =>
      by_cases equality : first = letter
      · subst first
        simp [kept, induction]
      · by_cases firstKept : keep first
        · simp [firstKept, equality, induction]
        · simp [firstKept, equality, induction]

private theorem pairKeep_member
    {letters : List Nat} {x y value : Nat}
    (member : value ∈ letters.filter (pairKeep x y)) :
    value = x ∨ value = y := by
  have kept := (List.mem_filter.mp member).2
  simpa [pairKeep] using kept

private theorem length_eq_pair_counts
    {x y : Nat} (different : x ≠ y) :
    ∀ letters : List Nat,
      (∀ value, value ∈ letters → value = x ∨ value = y) →
      letters.length = letters.count x + letters.count y
  | [], _ => by simp
  | value :: rest, onlyPair => by
      have headPair := onlyPair value (by simp)
      have restPair :
          ∀ selected, selected ∈ rest →
            selected = x ∨ selected = y := by
        intro selected member
        exact onlyPair selected (by simp [member])
      have induction :=
        length_eq_pair_counts different rest restPair
      rcases headPair with rfl | rfl
      · simp [different, induction]
        omega
      · simp [Ne.symm different, induction]
        omega

private theorem pairList_shape_of_counts_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : letters.count x = 1)
    (yCount : letters.count y = 1)
    (onlyPair :
      ∀ value, value ∈ letters → value = x ∨ value = y) :
    letters = [x, y] ∨ letters = [y, x] := by
  have lengthTwo : letters.length = 2 := by
    rw [length_eq_pair_counts different letters onlyPair,
      xCount, yCount]
  rcases letters with _ | ⟨head, rest⟩
  · simp at lengthTwo
  rcases rest with _ | ⟨next, rest⟩
  · simp at lengthTwo
  have restEmpty : rest = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using lengthTwo
  subst rest
  have headPair := onlyPair head (by simp)
  have nextPair := onlyPair next (by simp)
  rcases headPair with rfl | rfl
  · rcases nextPair with rfl | rfl
    · simp at xCount
    · exact Or.inl rfl
  · rcases nextPair with rfl | rfl
    · exact Or.inr rfl
    · simp at yCount

private theorem pairProjection_shape
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xSimple : letters.count x = 1)
    (ySimple : letters.count y = 1) :
    pairProjection letters x y = [x, y] ∨
      pairProjection letters x y = [y, x] := by
  apply pairList_shape_of_counts_one
  · exact different
  · unfold pairProjection
    rw [count_filter_of_kept letters (pairKeep x y) x]
    · exact xSimple
    · simp [pairKeep]
  · unfold pairProjection
    rw [count_filter_of_kept letters (pairKeep x y) y]
    · exact ySimple
    · simp [pairKeep]
  · intro value member
    exact pairKeep_member member

private def segmentationPrecedenceStep
    (x y : Nat) (state : PrecedenceState) (letter : Nat) :
    PrecedenceState :=
  if letter = x then
    match state with
    | .neither => .onlyX
    | .onlyX => .onlyX
    | .onlyY | .ordered | .violated => .violated
  else if letter = y then
    match state with
    | .neither => .onlyY
    | .onlyX => .ordered
    | .onlyY => .onlyY
    | .ordered => .ordered
    | .violated => .violated
  else state

private theorem precedenceScanList_eq_segmentationFold
    (letters : List Nat) (x y : Nat) :
    precedenceScanList letters x y =
      letters.foldl (segmentationPrecedenceStep x y) .neither := by
  rfl

private theorem segmentationPrecedenceFold_filter
    (x y : Nat) :
    ∀ (letters : List Nat) (initial : PrecedenceState),
      letters.foldl (segmentationPrecedenceStep x y) initial =
        (letters.filter (pairKeep x y)).foldl
          (segmentationPrecedenceStep x y) initial
  | [], _ => rfl
  | value :: rest, initial => by
      by_cases isX : value = x
      · subst value
        have induction :=
          segmentationPrecedenceFold_filter x y rest
            (segmentationPrecedenceStep x y initial x)
        simpa [pairKeep] using induction
      · by_cases isY : value = y
        · subst value
          have induction :=
            segmentationPrecedenceFold_filter x y rest
              (segmentationPrecedenceStep x y initial y)
          simpa [pairKeep, isX] using induction
        · have induction :=
            segmentationPrecedenceFold_filter x y rest initial
          simpa [pairKeep, segmentationPrecedenceStep, isX, isY]
            using induction

private theorem precedenceScanList_eq_pairProjectionFold
    (letters : List Nat) (x y : Nat) :
    precedenceScanList letters x y =
      (pairProjection letters x y).foldl
        (segmentationPrecedenceStep x y) .neither := by
  rw [precedenceScanList_eq_segmentationFold]
  unfold pairProjection
  exact segmentationPrecedenceFold_filter x y letters .neither

private theorem completePrecedence_iff_pairProjection_head
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xSimple : letters.count x = 1)
    (ySimple : letters.count y = 1) :
    CompletePrecedenceList letters x y ↔
      (pairProjection letters x y).head? = some x := by
  unfold CompletePrecedenceList
  rw [precedenceScanList_eq_pairProjectionFold]
  rcases pairProjection_shape letters different xSimple ySimple with
      shape | shape <;>
    rw [shape] <;>
    simp [segmentationPrecedenceStep, different, Ne.symm different]

private theorem simpleProjection_pairProjection
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xSimple : letters.count x = 1)
    (ySimple : letters.count y = 1) :
    (simpleProjection letters letters).filter (pairKeep x y) =
      pairProjection letters x y := by
  unfold simpleProjection pairProjection
  rw [List.filter_filter]
  apply List.filter_congr
  intro value _
  by_cases isX : value = x
  · subst value
    simp [pairKeep, xSimple]
  · by_cases isY : value = y
    · subst value
      simp [pairKeep, isX, ySimple]
    · simp [pairKeep, isX, isY]

private theorem nodup_eq_of_pairProjection_head :
    ∀ {left right : List Nat},
      left.Nodup →
      right.Nodup →
      (∀ value, value ∈ left ↔ value ∈ right) →
      (∀ x y,
        x ≠ y →
        x ∈ left →
        y ∈ left →
        (left.filter (pairKeep x y)).head? =
          (right.filter (pairKeep x y)).head?) →
      left = right
  | [], [], _, _, _, _ => rfl
  | [], head :: tail, _, _, sameMembers, _ => by
      have : head ∈ ([] : List Nat) :=
        (sameMembers head).mpr (by simp)
      simp at this
  | head :: tail, [], _, _, sameMembers, _ => by
      have : head ∈ ([] : List Nat) :=
        (sameMembers head).mp (by simp)
      simp at this
  | leftHead :: leftTail, rightHead :: rightTail,
      leftNodup, rightNodup, sameMembers, sameHeads => by
      simp only [List.nodup_cons] at leftNodup rightNodup
      have headsEqual : leftHead = rightHead := by
        apply Decidable.byContradiction
        intro different
        have leftHeadMember :
            leftHead ∈ leftHead :: leftTail := by simp
        have rightHeadMember :
            rightHead ∈ leftHead :: leftTail :=
          (sameMembers rightHead).mpr (by simp)
        have pairHeads :=
          sameHeads leftHead rightHead different
            leftHeadMember rightHeadMember
        simp [pairKeep, different] at pairHeads
      subst rightHead
      have tailMembers :
          ∀ value, value ∈ leftTail ↔ value ∈ rightTail := by
        intro value
        constructor
        · intro member
          have inRight :
              value ∈ leftHead :: rightTail :=
            (sameMembers value).mp (by simp [member])
          rcases List.mem_cons.mp inRight with equality | tailMember
          · subst value
            exact False.elim (leftNodup.1 member)
          · exact tailMember
        · intro member
          have inLeft :
              value ∈ leftHead :: leftTail :=
            (sameMembers value).mpr (by simp [member])
          rcases List.mem_cons.mp inLeft with equality | tailMember
          · subst value
            exact False.elim (rightNodup.1 member)
          · exact tailMember
      have tailHeads :
          ∀ x y,
            x ≠ y →
            x ∈ leftTail →
            y ∈ leftTail →
            (leftTail.filter (pairKeep x y)).head? =
              (rightTail.filter (pairKeep x y)).head? := by
        intro x y different xMember yMember
        have xNotHead : x ≠ leftHead := by
          intro equality
          subst x
          exact leftNodup.1 xMember
        have yNotHead : y ≠ leftHead := by
          intro equality
          subst y
          exact leftNodup.1 yMember
        have inherited :=
          sameHeads x y different
            (by simp [xMember]) (by simp [yMember])
        simpa [pairKeep, Ne.symm xNotHead,
          Ne.symm yNotHead] using inherited
      have tailEqual :=
        nodup_eq_of_pairProjection_head
          leftNodup.2 rightNodup.2 tailMembers tailHeads
      rw [tailEqual]

private theorem simpleProjection_eq_of_counts_precedence
    {left right : List Nat}
    (counts : ∀ letter, left.count letter = right.count letter)
    (precedence :
      ∀ x y,
        CompletePrecedenceList left x y ↔
          CompletePrecedenceList right x y) :
    simpleProjection left left = simpleProjection right right := by
  apply nodup_eq_of_pairProjection_head
  · exact simpleProjection_self_nodup left
  · exact simpleProjection_self_nodup right
  · intro letter
    simp only [simpleProjection, List.mem_filter]
    constructor
    · rintro ⟨member, simple⟩
      refine ⟨?_, ?_⟩
      · exact List.count_pos_iff.mp <| by
          rw [← counts letter]
          exact List.count_pos_iff.mpr member
      · simpa [counts letter] using simple
    · rintro ⟨member, simple⟩
      refine ⟨?_, ?_⟩
      · exact List.count_pos_iff.mp <| by
          rw [counts letter]
          exact List.count_pos_iff.mpr member
      · simpa [counts letter] using simple
  · intro x y different xMember yMember
    have leftX : left.count x = 1 := by
      have kept := (List.mem_filter.mp xMember).2
      simpa [simpleProjection] using kept
    have leftY : left.count y = 1 := by
      have kept := (List.mem_filter.mp yMember).2
      simpa [simpleProjection] using kept
    have rightX : right.count x = 1 := by
      rw [← counts x]
      exact leftX
    have rightY : right.count y = 1 := by
      rw [← counts y]
      exact leftY
    rw [simpleProjection_pairProjection left different leftX leftY,
      simpleProjection_pairProjection right different rightX rightY]
    rcases pairProjection_shape left different leftX leftY with
        leftXY | leftYX <;>
      rcases pairProjection_shape right different rightX rightY with
        rightXY | rightYX
    · simp [leftXY, rightXY]
    · have leftPrecedes : CompletePrecedenceList left x y :=
        (completePrecedence_iff_pairProjection_head
          left different leftX leftY).2 <| by
            simp [leftXY]
      have rightPrecedes := (precedence x y).1 leftPrecedes
      have rightHead :=
        (completePrecedence_iff_pairProjection_head
          right different rightX rightY).1 rightPrecedes
      rw [rightYX] at rightHead
      have equal : y = x := Option.some.inj rightHead
      exact False.elim (different equal.symm)
    · have rightPrecedes : CompletePrecedenceList right x y :=
        (completePrecedence_iff_pairProjection_head
          right different rightX rightY).2 <| by
            simp [rightXY]
      have leftPrecedes := (precedence x y).2 rightPrecedes
      have leftHead :=
        (completePrecedence_iff_pairProjection_head
          left different leftX leftY).1 leftPrecedes
      rw [leftYX] at leftHead
      have equal : y = x := Option.some.inj leftHead
      exact False.elim (different equal.symm)
    · simp [leftYX, rightYX]

/-! ## Prefix counts at a singleton separator -/

private def segmentationPairFree
    (x y : Nat) (letters : List Nat) : Prop :=
  x ∉ letters ∧ y ∉ letters

private theorem segmentationPrecedenceFold_pairFree
    (x y : Nat) :
    ∀ (letters : List Nat) (state : PrecedenceState),
      segmentationPairFree x y letters →
      letters.foldl (segmentationPrecedenceStep x y) state = state
  | [], _, _ => rfl
  | letter :: rest, state, free => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact free.1 (List.Mem.head rest)
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact free.2 (List.Mem.head rest)
      have restFree : segmentationPairFree x y rest :=
        ⟨fun member => free.1 (List.Mem.tail letter member),
          fun member => free.2 (List.Mem.tail letter member)⟩
      simp only [List.foldl_cons]
      rw [show segmentationPrecedenceStep x y state letter = state by
        simp [segmentationPrecedenceStep, letterNeX, letterNeY]]
      exact
        segmentationPrecedenceFold_pairFree x y rest state restFree

private theorem segmentationPrecedenceFold_onlyX_of_y_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      y ∉ letters →
      letters.foldl (segmentationPrecedenceStep x y) .onlyX = .onlyX
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : y ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show segmentationPrecedenceStep x y .onlyX letter = .onlyX by
        by_cases isX : letter = x
        · simp [segmentationPrecedenceStep, isX]
        · simp [segmentationPrecedenceStep, isX, letterNeY]]
      exact
        segmentationPrecedenceFold_onlyX_of_y_absent
          x y rest restAbsent

private theorem segmentationPrecedenceFold_onlyY_of_x_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      letters.foldl (segmentationPrecedenceStep x y) .onlyY = .onlyY
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : x ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show segmentationPrecedenceStep x y .onlyY letter = .onlyY by
        simp [segmentationPrecedenceStep, letterNeX]]
      exact
        segmentationPrecedenceFold_onlyY_of_x_absent
          x y rest restAbsent

private theorem segmentationPrecedenceFold_ordered_of_x_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      letters.foldl (segmentationPrecedenceStep x y) .ordered = .ordered
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : x ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show segmentationPrecedenceStep x y .ordered letter = .ordered by
        simp [segmentationPrecedenceStep, letterNeX]]
      exact
        segmentationPrecedenceFold_ordered_of_x_absent
          x y rest restAbsent

private theorem segmentationPrecedenceFold_violated
    (x y : Nat) :
    ∀ letters : List Nat,
      letters.foldl (segmentationPrecedenceStep x y) .violated = .violated
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show segmentationPrecedenceStep x y .violated letter = .violated by
        simp [segmentationPrecedenceStep]]
      exact segmentationPrecedenceFold_violated x y rest

private theorem
    segmentationPrecedenceFold_violated_of_x_mem_from_onlyY
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      letters.foldl (segmentationPrecedenceStep x y) .onlyY = .violated
  | [], member => by simp at member
  | letter :: rest, member => by
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show segmentationPrecedenceStep x y .onlyY letter =
            .violated by
          simp [segmentationPrecedenceStep, isX]]
        exact segmentationPrecedenceFold_violated x y rest
      · have restMember : x ∈ rest := by
          exact
            (List.mem_cons.mp member).resolve_left (Ne.symm isX)
        rw [show segmentationPrecedenceStep x y .onlyY letter = .onlyY by
          simp [segmentationPrecedenceStep, isX]]
        exact
          segmentationPrecedenceFold_violated_of_x_mem_from_onlyY
            x y rest restMember

private theorem
    segmentationPrecedenceFold_violated_of_x_mem_from_ordered
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      letters.foldl (segmentationPrecedenceStep x y) .ordered = .violated
  | [], member => by simp at member
  | letter :: rest, member => by
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show segmentationPrecedenceStep x y .ordered letter =
            .violated by
          simp [segmentationPrecedenceStep, isX]]
        exact segmentationPrecedenceFold_violated x y rest
      · have restMember : x ∈ rest := by
          exact
            (List.mem_cons.mp member).resolve_left (Ne.symm isX)
        rw [show segmentationPrecedenceStep x y .ordered letter = .ordered by
          simp [segmentationPrecedenceStep, isX]]
        exact
          segmentationPrecedenceFold_violated_of_x_mem_from_ordered
            x y rest restMember

private theorem segmentationPrecedenceFold_onlyX_of_x_mem_y_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      y ∉ letters →
      letters.foldl (segmentationPrecedenceStep x y) .neither = .onlyX
  | [], member, _ => by simp at member
  | letter :: rest, xMember, yAbsent => by
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact yAbsent (List.Mem.head rest)
      have restYAbsent : y ∉ rest :=
        fun member => yAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show segmentationPrecedenceStep x y .neither letter = .onlyX by
          simp [segmentationPrecedenceStep, isX]]
        exact
          segmentationPrecedenceFold_onlyX_of_y_absent
            x y rest restYAbsent
      · have restXMember : x ∈ rest := by
          exact
            (List.mem_cons.mp xMember).resolve_left (Ne.symm isX)
        rw [show segmentationPrecedenceStep x y .neither letter = .neither by
          simp [segmentationPrecedenceStep, isX, letterNeY]]
        exact
          segmentationPrecedenceFold_onlyX_of_x_mem_y_absent
            x y rest restXMember restYAbsent

private theorem segmentationPrecedenceFold_onlyY_of_x_absent_y_mem
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      y ∈ letters →
      letters.foldl (segmentationPrecedenceStep x y) .neither = .onlyY
  | [], _, member => by simp at member
  | letter :: rest, xAbsent, yMember => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact xAbsent (List.Mem.head rest)
      have restXAbsent : x ∉ rest :=
        fun member => xAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases isY : letter = y
      · have yNeX : y ≠ x := by
          intro equal
          exact letterNeX (isY.trans equal)
        rw [show segmentationPrecedenceStep x y .neither letter = .onlyY by
          simp [segmentationPrecedenceStep, isY, yNeX]]
        exact
          segmentationPrecedenceFold_onlyY_of_x_absent
            x y rest restXAbsent
      · have restYMember : y ∈ rest := by
          exact
            (List.mem_cons.mp yMember).resolve_left (Ne.symm isY)
        rw [show segmentationPrecedenceStep x y .neither letter = .neither by
          simp [segmentationPrecedenceStep, letterNeX, isY]]
        exact
          segmentationPrecedenceFold_onlyY_of_x_absent_y_mem
            x y rest restXAbsent restYMember

private theorem segmentationPrecedenceFold_ordered_of_x_absent_y_mem
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      y ∈ letters →
      letters.foldl (segmentationPrecedenceStep x y) .onlyX = .ordered
  | [], _, member => by simp at member
  | letter :: rest, xAbsent, yMember => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact xAbsent (List.Mem.head rest)
      have restXAbsent : x ∉ rest :=
        fun member => xAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases isY : letter = y
      · have yNeX : y ≠ x := by
          intro equal
          exact letterNeX (isY.trans equal)
        rw [show segmentationPrecedenceStep x y .onlyX letter = .ordered by
          simp [segmentationPrecedenceStep, isY, yNeX]]
        exact
          segmentationPrecedenceFold_ordered_of_x_absent
            x y rest restXAbsent
      · have restYMember : y ∈ rest := by
          exact
            (List.mem_cons.mp yMember).resolve_left (Ne.symm isY)
        rw [show segmentationPrecedenceStep x y .onlyX letter = .onlyX by
          simp [segmentationPrecedenceStep, letterNeX, isY]]
        exact
          segmentationPrecedenceFold_ordered_of_x_absent_y_mem
            x y rest restXAbsent restYMember

private theorem precedenceScan_ordered_before_separator
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (xInBefore : x ∈ before)
    (separatorAbsentBefore : separator ∉ before)
    (xAbsentAfter : x ∉ after) :
    precedenceScanList (before ++ separator :: after) x separator =
      .ordered := by
  rw [precedenceScanList_eq_segmentationFold]
  rw [List.foldl_append]
  rw [segmentationPrecedenceFold_onlyX_of_x_mem_y_absent
    x separator before xInBefore separatorAbsentBefore]
  simp only [List.foldl_cons]
  rw [show segmentationPrecedenceStep x separator .onlyX separator =
      .ordered by
    simp [segmentationPrecedenceStep, Ne.symm different]]
  exact
    segmentationPrecedenceFold_ordered_of_x_absent
      x separator after xAbsentAfter

private theorem precedenceScan_ordered_after_separator
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (xAbsentBefore : x ∉ before)
    (separatorAbsentBefore : separator ∉ before)
    (xInAfter : x ∈ after)
    (separatorAbsentAfter : separator ∉ after) :
    precedenceScanList (before ++ separator :: after) separator x =
      .ordered := by
  rw [precedenceScanList_eq_segmentationFold]
  rw [List.foldl_append]
  rw [segmentationPrecedenceFold_pairFree separator x before .neither
    ⟨separatorAbsentBefore, xAbsentBefore⟩]
  simp only [List.foldl_cons]
  rw [show segmentationPrecedenceStep separator x .neither separator =
      .onlyX by
    simp [segmentationPrecedenceStep]]
  exact
    segmentationPrecedenceFold_ordered_of_x_absent_y_mem
      separator x after separatorAbsentAfter xInAfter

private theorem precedenceScan_violated_after_inversion
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (separatorAbsentBefore : separator ∉ before)
    (xInAfter : x ∈ after) :
    precedenceScanList (before ++ separator :: after) x separator =
      .violated := by
  rw [precedenceScanList_eq_segmentationFold]
  rw [List.foldl_append]
  by_cases xInBefore : x ∈ before
  · rw [segmentationPrecedenceFold_onlyX_of_x_mem_y_absent
      x separator before xInBefore separatorAbsentBefore]
    simp only [List.foldl_cons]
    rw [show segmentationPrecedenceStep x separator .onlyX separator =
        .ordered by
      simp [segmentationPrecedenceStep, Ne.symm different]]
    exact
      segmentationPrecedenceFold_violated_of_x_mem_from_ordered
        x separator after xInAfter
  · rw [segmentationPrecedenceFold_pairFree x separator before .neither
      ⟨xInBefore, separatorAbsentBefore⟩]
    simp only [List.foldl_cons]
    rw [show segmentationPrecedenceStep x separator .neither separator =
        .onlyY by
      simp [segmentationPrecedenceStep, Ne.symm different]]
    exact
      segmentationPrecedenceFold_violated_of_x_mem_from_onlyY
        x separator after xInAfter

private theorem precedenceScan_violated_before_separator
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (xInBefore : x ∈ before)
    (separatorAbsentBefore : separator ∉ before) :
    precedenceScanList (before ++ separator :: after) separator x =
      .violated := by
  rw [precedenceScanList_eq_segmentationFold]
  rw [List.foldl_append]
  rw [segmentationPrecedenceFold_onlyY_of_x_absent_y_mem
    separator x before separatorAbsentBefore xInBefore]
  simp only [List.foldl_cons]
  rw [show segmentationPrecedenceStep separator x .onlyY separator =
      .violated by
    simp [segmentationPrecedenceStep]]
  exact segmentationPrecedenceFold_violated separator x after

private theorem precedenceState_violated_ne_ordered :
    (PrecedenceState.violated : PrecedenceState) ≠ .ordered := by
  decide

private theorem completePrecedence_before_separator_iff
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (xQuadratic : (before ++ separator :: after).count x = 2)
    (separatorSimple :
      (before ++ separator :: after).count separator = 1) :
    CompletePrecedenceList
        (before ++ separator :: after) x separator ↔
      before.count x = 2 := by
  have xSplit := xQuadratic
  simp only [List.count_append, List.count_cons] at xSplit
  simp [Ne.symm different] at xSplit
  have separatorSplit := separatorSimple
  simp only [List.count_append, List.count_cons_self] at separatorSplit
  have separatorBeforeZero : before.count separator = 0 := by omega
  have separatorAfterZero : after.count separator = 0 := by omega
  have separatorAbsentBefore : separator ∉ before :=
    List.count_eq_zero.mp separatorBeforeZero
  constructor
  · intro complete
    have xAfterZero : after.count x = 0 := by
      apply Decidable.byContradiction
      intro nonzero
      have xInAfter : x ∈ after :=
        List.one_le_count_iff.mp (by omega)
      have violated :=
        precedenceScan_violated_after_inversion
          different before after separatorAbsentBefore xInAfter
      exact precedenceState_violated_ne_ordered
        (violated.symm.trans complete.2)
    omega
  · intro beforeTwo
    have xInBefore : x ∈ before :=
      List.one_le_count_iff.mp (by omega)
    have xAfterZero : after.count x = 0 := by omega
    have xAbsentAfter : x ∉ after :=
      List.count_eq_zero.mp xAfterZero
    exact
      ⟨different,
        precedenceScan_ordered_before_separator
          different before after xInBefore separatorAbsentBefore
            xAbsentAfter⟩

private theorem completePrecedence_after_separator_iff
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (xQuadratic : (before ++ separator :: after).count x = 2)
    (separatorSimple :
      (before ++ separator :: after).count separator = 1) :
    CompletePrecedenceList
        (before ++ separator :: after) separator x ↔
      before.count x = 0 := by
  have xSplit := xQuadratic
  simp only [List.count_append, List.count_cons] at xSplit
  simp [Ne.symm different] at xSplit
  have separatorSplit := separatorSimple
  simp only [List.count_append, List.count_cons_self] at separatorSplit
  have separatorBeforeZero : before.count separator = 0 := by omega
  have separatorAfterZero : after.count separator = 0 := by omega
  have separatorAbsentBefore : separator ∉ before :=
    List.count_eq_zero.mp separatorBeforeZero
  have separatorAbsentAfter : separator ∉ after :=
    List.count_eq_zero.mp separatorAfterZero
  constructor
  · intro complete
    apply Decidable.byContradiction
    intro nonzero
    have xInBefore : x ∈ before :=
      List.one_le_count_iff.mp (by omega)
    have violated :=
      precedenceScan_violated_before_separator
        different before after xInBefore separatorAbsentBefore
    exact precedenceState_violated_ne_ordered
      (violated.symm.trans complete.2)
  · intro beforeZero
    have xAfterTwo : after.count x = 2 := by omega
    have xInAfter : x ∈ after :=
      List.one_le_count_iff.mp (by omega)
    have xAbsentBefore : x ∉ before :=
      List.count_eq_zero.mp beforeZero
    exact
      ⟨Ne.symm different,
        precedenceScan_ordered_after_separator
          different before after xAbsentBefore separatorAbsentBefore
            xInAfter separatorAbsentAfter⟩

private theorem prefixCount_eq_of_completePrecedence
    {x separator : Nat} (different : x ≠ separator)
    (leftPrefix leftRest rightPrefix rightRest : List Nat)
    (leftQuadratic :
      (leftPrefix ++ separator :: leftRest).count x = 2)
    (rightQuadratic :
      (rightPrefix ++ separator :: rightRest).count x = 2)
    (leftSeparator :
      (leftPrefix ++ separator :: leftRest).count separator = 1)
    (rightSeparator :
      (rightPrefix ++ separator :: rightRest).count separator = 1)
    (precedence :
      ∀ a b,
        CompletePrecedenceList
            (leftPrefix ++ separator :: leftRest) a b ↔
          CompletePrecedenceList
            (rightPrefix ++ separator :: rightRest) a b) :
    leftPrefix.count x = rightPrefix.count x := by
  have leftBefore :=
    completePrecedence_before_separator_iff
      different leftPrefix leftRest leftQuadratic leftSeparator
  have rightBefore :=
    completePrecedence_before_separator_iff
      different rightPrefix rightRest rightQuadratic rightSeparator
  have leftAfter :=
    completePrecedence_after_separator_iff
      different leftPrefix leftRest leftQuadratic leftSeparator
  have rightAfter :=
    completePrecedence_after_separator_iff
      different rightPrefix rightRest rightQuadratic rightSeparator
  by_cases before :
      CompletePrecedenceList
        (leftPrefix ++ separator :: leftRest) x separator
  · have rightValue := (precedence x separator).1 before
    rw [leftBefore.mp before, rightBefore.mp rightValue]
  · have rightNotBefore :
        ¬ CompletePrecedenceList
          (rightPrefix ++ separator :: rightRest) x separator := by
      intro rightValue
      exact before ((precedence x separator).2 rightValue)
    by_cases after :
        CompletePrecedenceList
          (leftPrefix ++ separator :: leftRest) separator x
    · have rightValue := (precedence separator x).1 after
      rw [leftAfter.mp after, rightAfter.mp rightValue]
    · have rightNotAfter :
          ¬ CompletePrecedenceList
            (rightPrefix ++ separator :: rightRest) separator x := by
        intro rightValue
        exact after ((precedence separator x).2 rightValue)
      have leftNotTwo : leftPrefix.count x ≠ 2 :=
        fun equal => before (leftBefore.mpr equal)
      have rightNotTwo : rightPrefix.count x ≠ 2 :=
        fun equal => rightNotBefore (rightBefore.mpr equal)
      have leftNotZero : leftPrefix.count x ≠ 0 :=
        fun equal => after (leftAfter.mpr equal)
      have rightNotZero : rightPrefix.count x ≠ 0 :=
        fun equal => rightNotAfter (rightAfter.mpr equal)
      have leftSplit := leftQuadratic
      have rightSplit := rightQuadratic
      simp only [List.count_append, List.count_cons] at leftSplit rightSplit
      simp [Ne.symm different] at leftSplit rightSplit
      omega

/-! ## Recursive segmentation -/

/-- On two-limited lists the capped multiplicity equality is exact. -/
theorem twoLimited_count_eq_of_capped
    {left right : List Nat}
    (leftLimited : UniqueSeparatorTwoLimited left)
    (rightLimited : UniqueSeparatorTwoLimited right)
    (capped :
      ∀ letter,
        Nat.min (left.count letter) 2 =
          Nat.min (right.count letter) 2) :
    ∀ letter, left.count letter = right.count letter := by
  intro letter
  have leftBound := leftLimited letter
  have rightBound := rightLimited letter
  have equal := capped letter
  simpa [Nat.min_eq_left leftBound,
    Nat.min_eq_left rightBound] using equal

private theorem listDerivesSegmented
    (sourceTail targetTail pre : List Nat)
    (sourceLimited :
      UniqueSeparatorTwoLimited (pre ++ sourceTail))
    (targetLimited :
      UniqueSeparatorTwoLimited (pre ++ targetTail))
    (counts :
      ∀ letter,
        (pre ++ sourceTail).count letter =
          (pre ++ targetTail).count letter)
    (simpleEqual :
      simpleProjection (pre ++ sourceTail) sourceTail =
        simpleProjection (pre ++ targetTail) targetTail)
    (precedence :
      ∀ x y,
        CompletePrecedenceList (pre ++ sourceTail) x y ↔
          CompletePrecedenceList (pre ++ targetTail) x y)
    (equivalent :
      M20ListEquivalent
        (pre ++ sourceTail) (pre ++ targetTail)) :
    S5_107.ListDerives basis
      (pre ++ sourceTail) (pre ++ targetTail) := by
  cases sourceProjection :
      simpleProjection (pre ++ sourceTail) sourceTail with
  | nil =>
      have targetProjection :
          simpleProjection (pre ++ targetTail) targetTail = [] := by
        rw [← simpleEqual, sourceProjection]
      have sourceNonlinear :=
        nonlinear_of_simpleProjection_nil
          (pre ++ sourceTail) sourceTail sourceProjection
      have targetNonlinear :=
        nonlinear_of_simpleProjection_nil
          (pre ++ targetTail) targetTail targetProjection
      have permutation : sourceTail.Perm targetTail := by
        rw [List.perm_iff_count]
        intro letter
        have total := counts letter
        simp only [List.count_append] at total
        omega
      have sourceQuadratic :
          ∀ letter, letter ∈ sourceTail →
            (pre ++ sourceTail ++ []).count letter = 2 := by
        intro letter member
        have positive : 1 ≤ (pre ++ sourceTail).count letter :=
          List.one_le_count_iff.mpr <| by simp [member]
        have bound := sourceLimited letter
        have notOne := sourceNonlinear letter member
        simpa using
          (show (pre ++ sourceTail).count letter = 2 by omega)
      have targetQuadratic :
          ∀ letter, letter ∈ targetTail →
            (pre ++ targetTail ++ []).count letter = 2 := by
        intro letter member
        have positive : 1 ≤ (pre ++ targetTail).count letter :=
          List.one_le_count_iff.mpr <| by simp [member]
        have bound := targetLimited letter
        have notOne := targetNonlinear letter member
        simpa using
          (show (pre ++ targetTail).count letter = 2 by omega)
      simpa using
        listDerivesQuadraticBlockPermutationAgainst
          targetTail sourceTail pre [] [] permutation
          sourceQuadratic targetQuadratic (by simpa using equivalent)
  | cons separator remaining =>
      have targetProjection :
          simpleProjection (pre ++ targetTail) targetTail =
            separator :: remaining := by
        rw [← simpleEqual, sourceProjection]
      obtain
        ⟨sourceBlock, sourceRest, sourceShape,
          sourceBlockNonlinear, sourceRestProjection,
          sourceSeparator⟩ :=
        simpleProjection_cons_split
          pre sourceTail separator remaining sourceProjection
      obtain
        ⟨targetBlock, targetRest, targetShape,
          targetBlockNonlinear, targetRestProjection,
          targetSeparator⟩ :=
        simpleProjection_cons_split
          pre targetTail separator remaining targetProjection
      have sourceRestShorter : sourceRest.length < sourceTail.length := by
        rw [sourceShape]
        simp only [List.length_append, List.length_cons]
        omega
      have sourceLimitedNorm :
          UniqueSeparatorTwoLimited
            (pre ++ sourceBlock ++ separator :: sourceRest) := by
        simpa [sourceShape, List.append_assoc] using sourceLimited
      have targetLimitedNorm :
          UniqueSeparatorTwoLimited
            (pre ++ targetBlock ++ separator :: targetRest) := by
        simpa [targetShape, List.append_assoc] using targetLimited
      have countsNorm :
          ∀ letter,
            (pre ++ sourceBlock ++ separator :: sourceRest).count letter =
              (pre ++ targetBlock ++ separator :: targetRest).count
                letter := by
        intro letter
        simpa [sourceShape, targetShape, List.append_assoc] using
          counts letter
      have precedenceNorm :
          ∀ x y,
            CompletePrecedenceList
                (pre ++ sourceBlock ++ separator :: sourceRest) x y ↔
              CompletePrecedenceList
                (pre ++ targetBlock ++ separator :: targetRest) x y := by
        intro x y
        simpa [sourceShape, targetShape, List.append_assoc] using
          precedence x y
      have equivalentNorm :
          M20ListEquivalent
            (pre ++ sourceBlock ++ separator :: sourceRest)
            (pre ++ targetBlock ++ separator :: targetRest) := by
        simpa [sourceShape, targetShape, List.append_assoc] using equivalent
      have sourceSeparatorNorm :
          (pre ++ sourceBlock ++ separator :: sourceRest).count
              separator = 1 := by
        simpa [sourceShape, List.append_assoc] using sourceSeparator
      have targetSeparatorNorm :
          (pre ++ targetBlock ++ separator :: targetRest).count
              separator = 1 := by
        simpa [targetShape, List.append_assoc] using targetSeparator
      have blockPermutation : sourceBlock.Perm targetBlock := by
        rw [List.perm_iff_count]
        intro letter
        by_cases sourceMember : letter ∈ sourceBlock
        · have sourcePositive :
              1 ≤
                (pre ++ sourceBlock ++ separator :: sourceRest).count
                  letter :=
            List.one_le_count_iff.mpr <| by simp [sourceMember]
          have sourceBound := sourceLimitedNorm letter
          have sourceNotOne :
              (pre ++ sourceBlock ++ separator :: sourceRest).count
                  letter ≠ 1 := by
            simpa [sourceShape, List.append_assoc] using
              sourceBlockNonlinear letter sourceMember
          have sourceTwo :
              (pre ++ sourceBlock ++ separator :: sourceRest).count
                  letter = 2 := by
            omega
          have targetTwo :
              (pre ++ targetBlock ++ separator :: targetRest).count
                  letter = 2 := by
            rw [← countsNorm letter]
            exact sourceTwo
          have different : letter ≠ separator := by
            intro equal
            subst letter
            omega
          have cut :=
            prefixCount_eq_of_completePrecedence
              different (pre ++ sourceBlock) sourceRest
              (pre ++ targetBlock) targetRest
              (by simpa [List.append_assoc] using sourceTwo)
              (by simpa [List.append_assoc] using targetTwo)
              (by simpa [List.append_assoc] using sourceSeparatorNorm)
              (by simpa [List.append_assoc] using targetSeparatorNorm)
              (by
                intro x y
                simpa [List.append_assoc] using precedenceNorm x y)
          simp only [List.count_append] at cut
          omega
        · by_cases targetMember : letter ∈ targetBlock
          · have targetPositive :
                1 ≤
                  (pre ++ targetBlock ++ separator :: targetRest).count
                    letter :=
              List.one_le_count_iff.mpr <| by simp [targetMember]
            have targetBound := targetLimitedNorm letter
            have targetNotOne :
                (pre ++ targetBlock ++ separator :: targetRest).count
                    letter ≠ 1 := by
              simpa [targetShape, List.append_assoc] using
                targetBlockNonlinear letter targetMember
            have targetTwo :
                (pre ++ targetBlock ++ separator :: targetRest).count
                    letter = 2 := by
              omega
            have sourceTwo :
                (pre ++ sourceBlock ++ separator :: sourceRest).count
                    letter = 2 := by
              rw [countsNorm letter]
              exact targetTwo
            have different : letter ≠ separator := by
              intro equal
              subst letter
              omega
            have cut :=
              prefixCount_eq_of_completePrecedence
                different (pre ++ sourceBlock) sourceRest
                (pre ++ targetBlock) targetRest
                (by simpa [List.append_assoc] using sourceTwo)
                (by simpa [List.append_assoc] using targetTwo)
                (by simpa [List.append_assoc] using sourceSeparatorNorm)
                (by simpa [List.append_assoc] using targetSeparatorNorm)
                (by
                  intro x y
                  simpa [List.append_assoc] using precedenceNorm x y)
            simp only [List.count_append] at cut
            omega
          · rw [List.count_eq_zero.mpr sourceMember,
              List.count_eq_zero.mpr targetMember]
      have sourceQuadratic :
          ∀ letter, letter ∈ sourceBlock →
            (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter = 2 := by
        intro letter member
        have positive :
            1 ≤
              (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter :=
          List.one_le_count_iff.mpr <| by simp [member]
        have bound := sourceLimitedNorm letter
        have notOne :
            (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter ≠ 1 := by
          simpa [sourceShape, List.append_assoc] using
            sourceBlockNonlinear letter member
        omega
      have targetQuadratic :
          ∀ letter, letter ∈ targetBlock →
            (pre ++ targetBlock ++ separator :: targetRest).count
                letter = 2 := by
        intro letter member
        have positive :
            1 ≤
              (pre ++ targetBlock ++ separator :: targetRest).count
                letter :=
          List.one_le_count_iff.mpr <| by simp [member]
        have bound := targetLimitedNorm letter
        have notOne :
            (pre ++ targetBlock ++ separator :: targetRest).count
                letter ≠ 1 := by
          simpa [targetShape, List.append_assoc] using
            targetBlockNonlinear letter member
        omega
      have move :=
        listDerivesQuadraticBlockPermutationAgainst
          targetBlock sourceBlock pre
          (separator :: sourceRest) (separator :: targetRest)
          blockPermutation sourceQuadratic targetQuadratic equivalentNorm
      have fullPermutation :
          (pre ++ sourceBlock ++ separator :: sourceRest).Perm
            (pre ++ targetBlock ++ separator :: sourceRest) := by
        simpa [List.append_assoc] using
          List.Perm.append
            (List.Perm.append (List.Perm.refl pre) blockPermutation)
            (List.Perm.refl (separator :: sourceRest))
      let nextPre := pre ++ targetBlock ++ [separator]
      have nextEquivalent :
          M20ListEquivalent
            (nextPre ++ sourceRest) (nextPre ++ targetRest) := by
        have moved :=
          (M20ListEquivalent.of_derives move).symm.trans equivalentNorm
        simpa [nextPre, List.append_assoc] using moved
      have nextCounts :
          ∀ letter,
            (nextPre ++ sourceRest).count letter =
              (nextPre ++ targetRest).count letter := by
        intro letter
        calc
          (nextPre ++ sourceRest).count letter =
              (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter := by
            simpa [nextPre, List.append_assoc] using
              (fullPermutation.count letter).symm
          _ =
              (pre ++ targetBlock ++ separator :: targetRest).count
                letter := countsNorm letter
          _ = (nextPre ++ targetRest).count letter := by
            simp [nextPre, List.append_assoc]
      have nextSourceLimited :
          UniqueSeparatorTwoLimited (nextPre ++ sourceRest) := by
        intro letter
        calc
          (nextPre ++ sourceRest).count letter =
              (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter := by
            simpa [nextPre, List.append_assoc] using
              (fullPermutation.count letter).symm
          _ ≤ 2 := sourceLimitedNorm letter
      have nextTargetLimited :
          UniqueSeparatorTwoLimited (nextPre ++ targetRest) := by
        intro letter
        simpa [nextPre, List.append_assoc] using targetLimitedNorm letter
      have nextSimpleEqual :
          simpleProjection (nextPre ++ sourceRest) sourceRest =
            simpleProjection (nextPre ++ targetRest) targetRest := by
        calc
          simpleProjection (nextPre ++ sourceRest) sourceRest =
              simpleProjection
                (pre ++ sourceBlock ++ separator :: sourceRest)
                sourceRest := by
            apply simpleProjection_congr
            intro letter
            simpa [nextPre, List.append_assoc] using
              (fullPermutation.count letter).symm
          _ = remaining := by
            simpa [sourceShape, List.append_assoc] using
              sourceRestProjection
          _ =
              simpleProjection
                (pre ++ targetBlock ++ separator :: targetRest)
                targetRest := by
            simpa [targetShape, List.append_assoc] using
              targetRestProjection.symm
          _ = simpleProjection (nextPre ++ targetRest) targetRest := by
            simp [nextPre, List.append_assoc]
      have nextPrecedence :
          ∀ x y,
            CompletePrecedenceList (nextPre ++ sourceRest) x y ↔
              CompletePrecedenceList (nextPre ++ targetRest) x y := by
        intro x y
        exact
          m20ListEquivalent_completePrecedenceList nextEquivalent x y
      have recurse :=
        listDerivesSegmented sourceRest targetRest nextPre
          nextSourceLimited nextTargetLimited nextCounts
          nextSimpleEqual nextPrecedence nextEquivalent
      simpa [sourceShape, targetShape, List.append_assoc] using
        move.trans (by
          simpa [nextPre, List.append_assoc] using recurse)
termination_by sourceTail.length
decreasing_by
  exact sourceRestShorter

/-- The six-case quadratic permutation theorem and complete precedence give
the complete two-limited segmentation replay for Edmunds' `M20`. -/
theorem m20SegmentationCompleteness :
    M20SegmentationCompletenessObligation
      quadraticBlockPermutationSixCase := by
  intro left right leftLimited rightLimited equivalent capped precedence
  have counts : ∀ letter, left.count letter = right.count letter :=
    twoLimited_count_eq_of_capped
      leftLimited rightLimited capped
  have simpleEqual :
      simpleProjection left left = simpleProjection right right :=
    simpleProjection_eq_of_counts_precedence counts precedence
  simpa using
    listDerivesSegmented left right []
      leftLimited rightLimited counts simpleEqual precedence equivalent

end SemigroupBasis.CoRoots.S5_841

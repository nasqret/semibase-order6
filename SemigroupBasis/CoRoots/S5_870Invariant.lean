import SemigroupBasis.CoRoots.S5_870GapSort
import SemigroupBasis.CoRoots.S5_345Factors

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_870

open SemigroupBasis
open SemigroupBasis.Examples

/-- Maximal prefix strictly before the first selected occurrence. -/
def prefixBefore (selected : Nat) : List Nat -> List Nat
  | [] => []
  | letter :: rest =>
      if letter = selected then []
      else letter :: prefixBefore selected rest

/-- The five multiplication facts used by the selected/comparator marker. -/
structure MarkerLaws (mul : Fin 5 -> Fin 5 -> Fin 5) : Prop where
  zeroAbsorbing : forall value, mul 0 value = 0
  twoAbsorbing : forall value, mul 2 value = 2
  repeatSelected : mul 1 1 = 0
  passOther : mul 1 3 = 1
  seeComparator : mul 1 4 = 2

namespace MarkerLaws

variable {mul : Fin 5 -> Fin 5 -> Fin 5}

theorem foldZero
    (laws : MarkerLaws mul) (valuation : Nat -> Fin 5) :
    forall letters : List Nat,
      letters.foldl
          (fun current letter => mul current (valuation letter)) 0 = 0
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [laws.zeroAbsorbing]
      exact foldZero laws valuation rest

theorem foldTwo
    (laws : MarkerLaws mul) (valuation : Nat -> Fin 5) :
    forall letters : List Nat,
      letters.foldl
          (fun current letter => mul current (valuation letter)) 2 = 2
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [laws.twoAbsorbing]
      exact foldTwo laws valuation rest

end MarkerLaws

/-!
Semantic separation for the exact catalogue table `S5_870`.

The two three-element embeddings recover the first-occurrence sequence and
multiplicities capped at two.  The remaining five-state valuation scans an
arbitrary selected variable: state `3` is a left identity, states `0`, `2`,
and `4` are absorbing, and state `1` records that the selected variable has
occurred once.  Consequently the value is zero exactly when the selected
variable occurs for the second time before the comparator occurs.
-/

/-! ## The two standard three-element subsemigroups -/

/-- The literal subsemigroup `{0,3,4}` is the three-element left regular
band, with zero-based identity element `3`. -/
def firstOccurrenceEmbedding :
    Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then (0 : Fin 5)
    else if value.val = 1 then (3 : Fin 5)
    else (4 : Fin 5)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The literal subsemigroup `{0,1,3}` records multiplicity as absent,
present once, or present at least twice. -/
def cappedMultiplicityEmbedding :
    Embedding commutativeExponentThree.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then (0 : Fin 5)
    else if value.val = 1 then (1 : Fin 5)
    else (3 : Fin 5)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-! ## Agreement of the two first-occurrence implementations -/

private theorem firstOccurrenceSequenceAux_eq_filter
    (seen : List Nat) :
    forall letters : List Nat,
      firstOccurrenceSequenceAux seen letters =
        (firstOccurrenceSequence letters).filter
          (fun letter => decide (letter ∉ seen))
  | [] => rfl
  | letter :: rest => by
      by_cases member : letter ∈ seen
      · rw [firstOccurrenceSequenceAux]
        simp only [member, if_pos, firstOccurrenceSequence]
        rw [firstOccurrenceSequenceAux_eq_filter seen rest]
        rw [List.filter_cons]
        simp [member]
        apply List.filter_congr
        intro tested _
        by_cases equal : tested = letter
        · subst tested
          simp [member]
        · simp [equal]
      · rw [firstOccurrenceSequenceAux]
        simp only [member, if_neg, firstOccurrenceSequence]
        rw [firstOccurrenceSequenceAux_eq_filter (letter :: seen) rest]
        rw [List.filter_cons]
        simp [member]
        apply List.filter_congr
        intro tested _
        exact Bool.and_comm _ _

theorem firstOccurrenceSequenceList_eq_firstOccurrenceSequence
    (letters : List Nat) :
    firstOccurrenceSequenceList letters =
      firstOccurrenceSequence letters := by
  unfold firstOccurrenceSequenceList
  rw [firstOccurrenceSequenceAux_eq_filter]
  apply List.filter_eq_self.mpr
  intro letter _
  simp

/-- Every valid identity preserves the left-to-right sequence of first
occurrences used by the gap signature. -/
theorem valid_firstOccurrenceSequenceList_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequenceList identity.lhs.toList =
      firstOccurrenceSequenceList identity.rhs.toList := by
  have standard :=
    S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity
      (firstOccurrenceEmbedding.pullback_identity identity valid)
  simpa [firstOccurrenceSequenceList_eq_firstOccurrenceSequence] using
    standard

/-- Every valid identity preserves every multiplicity capped at two. -/
theorem valid_capped_count_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    forall letter,
      min (identity.lhs.toList.count letter) 2 =
        min (identity.rhs.toList.count letter) 2 :=
  exponentValid_capped_count_eq identity
    (cappedMultiplicityEmbedding.pullback_identity identity valid)

private theorem min_two_eq_two_iff (count : Nat) :
    min count 2 = 2 ↔ 2 ≤ count := by
  simp only [Nat.min_def]
  split <;> omega

theorem valid_repeated_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (letter : Nat) :
    2 ≤ identity.lhs.toList.count letter ↔
      2 ≤ identity.rhs.toList.count letter := by
  have capped := valid_capped_count_eq identity valid letter
  constructor
  · intro leftRepeated
    apply (min_two_eq_two_iff _).1
    calc
      min (identity.rhs.toList.count letter) 2 =
          min (identity.lhs.toList.count letter) 2 := capped.symm
      _ = 2 := (min_two_eq_two_iff _).2 leftRepeated
  · intro rightRepeated
    apply (min_two_eq_two_iff _).1
    calc
      min (identity.lhs.toList.count letter) 2 =
          min (identity.rhs.toList.count letter) 2 := capped
      _ = 2 := (min_two_eq_two_iff _).2 rightRepeated

/-- The second signature field follows from the exponent-three embedding. -/
theorem valid_repeatFlagsList_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    repeatFlagsList identity.lhs.toList =
      repeatFlagsList identity.rhs.toList := by
  unfold repeatFlagsList
  rw [valid_firstOccurrenceSequenceList_eq identity valid]
  apply List.map_congr_left
  intro letter _
  have repeatedIff := valid_repeated_iff identity valid letter
  by_cases leftRepeated : 2 ≤ identity.lhs.toList.count letter
  · have rightRepeated := repeatedIff.mp leftRepeated
    simp [leftRepeated, rightRepeated]
  · have rightNotRepeated :
        ¬ 2 ≤ identity.rhs.toList.count letter := by
      intro rightRepeated
      exact leftRepeated (repeatedIff.mpr rightRepeated)
    simp [leftRepeated, rightNotRepeated]

/-! ## The exact set of variables seen before a second occurrence -/

/-- The same scan as `secondOccurrenceGapAux`, retaining the actual set of
first occurrences rather than only its cardinality.  The list is in reverse
first-occurrence order, exactly like the `firsts` accumulator of the gap
scan. -/
def secondOccurrenceFirstsAux
    (selected : Nat) (seenSelected : Bool) (firsts : List Nat) :
    List Nat -> Option (List Nat)
  | [] => none
  | letter :: rest =>
      let nextFirsts :=
        if letter ∈ firsts then firsts else letter :: firsts
      if letter = selected then
        if seenSelected then some firsts
        else secondOccurrenceFirstsAux selected true nextFirsts rest
      else
        secondOccurrenceFirstsAux selected seenSelected nextFirsts rest

def secondOccurrenceFirstsList
    (letters : List Nat) (selected : Nat) : Option (List Nat) :=
  secondOccurrenceFirstsAux selected false [] letters

theorem secondOccurrenceGapAux_eq_snapshotLength
    (selected : Nat) :
    forall (seenSelected : Bool) (firsts letters : List Nat),
      secondOccurrenceGapAux selected seenSelected firsts letters =
        (secondOccurrenceFirstsAux selected seenSelected firsts letters).map
          List.length
  | _, _, [] => rfl
  | seenSelected, firsts, letter :: rest => by
      by_cases equal : letter = selected
      · subst letter
        cases seenSelected <;>
          simp [secondOccurrenceGapAux, secondOccurrenceFirstsAux,
            secondOccurrenceGapAux_eq_snapshotLength]
      · simp [secondOccurrenceGapAux, secondOccurrenceFirstsAux, equal,
          secondOccurrenceGapAux_eq_snapshotLength]

theorem secondOccurrenceGapList_eq_snapshotLength
    (letters : List Nat) (selected : Nat) :
    secondOccurrenceGapList letters selected =
      (secondOccurrenceFirstsList letters selected).map List.length := by
  exact secondOccurrenceGapAux_eq_snapshotLength selected false [] letters

/-- The concrete prefix strictly before the second selected occurrence.  If
there are fewer than two selected occurrences, the available suffix is
retained; only the repeated case is used below. -/
def prefixBeforeSecond (selected : Nat) : List Nat -> List Nat
  | [] => []
  | letter :: rest =>
      if letter = selected then
        letter :: prefixBefore selected rest
      else
        letter :: prefixBeforeSecond selected rest

private theorem mem_nextFirsts_iff
    (tested letter : Nat) (firsts : List Nat) :
    tested ∈ (if letter ∈ firsts then firsts else letter :: firsts) ↔
      tested ∈ firsts ∨ tested = letter := by
  by_cases known : letter ∈ firsts
  · simp only [known, if_pos]
    constructor
    · intro member
      exact Or.inl member
    · rintro (member | equal)
      · exact member
      · simpa [equal] using known
  · simp [known, eq_comm, or_comm]

private theorem secondOccurrenceFirstsAux_true_mem_iff
    (selected tested : Nat) :
    forall (firsts letters snapshot : List Nat),
      secondOccurrenceFirstsAux selected true firsts letters =
          some snapshot ->
        (tested ∈ snapshot ↔
          tested ∈ firsts ∨
            tested ∈ prefixBefore selected letters)
  | _, [], _, equality => by
      simp [secondOccurrenceFirstsAux] at equality
  | firsts, letter :: rest, snapshot, equality => by
      by_cases equal : letter = selected
      · subst letter
        simp [secondOccurrenceFirstsAux] at equality
        subst snapshot
        simp [prefixBefore]
      · have reduced :
            secondOccurrenceFirstsAux selected true
                (if letter ∈ firsts then firsts else letter :: firsts)
                rest = some snapshot := by
          simpa [secondOccurrenceFirstsAux, equal] using equality
        rw [secondOccurrenceFirstsAux_true_mem_iff selected tested
          (if letter ∈ firsts then firsts else letter :: firsts)
          rest snapshot reduced]
        rw [mem_nextFirsts_iff]
        simp [prefixBefore, equal, or_assoc,
          or_left_comm, or_comm]

private theorem secondOccurrenceFirstsAux_false_mem_iff
    (selected tested : Nat) :
    forall (firsts letters snapshot : List Nat),
      secondOccurrenceFirstsAux selected false firsts letters =
          some snapshot ->
        (tested ∈ snapshot ↔
          tested ∈ firsts ∨ tested ∈ prefixBeforeSecond selected letters)
  | _, [], _, equality => by
      simp [secondOccurrenceFirstsAux] at equality
  | firsts, letter :: rest, snapshot, equality => by
      by_cases equal : letter = selected
      · subst letter
        have reduced :
            secondOccurrenceFirstsAux selected true
                (if selected ∈ firsts then firsts else selected :: firsts)
                rest = some snapshot := by
          simpa [secondOccurrenceFirstsAux] using equality
        rw [secondOccurrenceFirstsAux_true_mem_iff selected tested
          (if selected ∈ firsts then firsts else selected :: firsts)
          rest snapshot reduced]
        rw [mem_nextFirsts_iff]
        simp [prefixBeforeSecond, or_assoc, or_left_comm, or_comm]
      · have reduced :
            secondOccurrenceFirstsAux selected false
                (if letter ∈ firsts then firsts else letter :: firsts)
                rest = some snapshot := by
          simpa [secondOccurrenceFirstsAux, equal] using equality
        rw [secondOccurrenceFirstsAux_false_mem_iff selected tested
          (if letter ∈ firsts then firsts else letter :: firsts)
          rest snapshot reduced]
        rw [mem_nextFirsts_iff]
        simp [prefixBeforeSecond, equal, or_assoc,
          or_left_comm, or_comm]

theorem secondOccurrenceFirstsList_mem_iff
    (letters snapshot : List Nat) (selected tested : Nat)
    (snapshotEq :
      secondOccurrenceFirstsList letters selected = some snapshot) :
    tested ∈ snapshot ↔ tested ∈ prefixBeforeSecond selected letters := by
  simpa [secondOccurrenceFirstsList] using
    secondOccurrenceFirstsAux_false_mem_iff selected tested [] letters
      snapshot snapshotEq

private theorem secondOccurrenceFirstsAux_nodup
    (selected : Nat) :
    forall (seenSelected : Bool) (firsts letters snapshot : List Nat),
      firsts.Nodup ->
      secondOccurrenceFirstsAux selected seenSelected firsts letters =
          some snapshot ->
        snapshot.Nodup
  | _, _, [], _, _, equality => by
      simp [secondOccurrenceFirstsAux] at equality
  | seenSelected, firsts, letter :: rest, snapshot,
      firstsNodup, equality => by
      let nextFirsts :=
        if letter ∈ firsts then firsts else letter :: firsts
      have nextNodup : nextFirsts.Nodup := by
        by_cases known : letter ∈ firsts
        · simpa [nextFirsts, known] using firstsNodup
        · simpa [nextFirsts, known] using
            (List.nodup_cons.mpr <| And.intro known firstsNodup)
      by_cases equal : letter = selected
      · subst letter
        cases seenSelected with
        | false =>
            exact secondOccurrenceFirstsAux_nodup selected true nextFirsts
              rest snapshot nextNodup (by
                simpa [secondOccurrenceFirstsAux, nextFirsts] using equality)
        | true =>
            have optionEq : some firsts = some snapshot := by
              simpa [secondOccurrenceFirstsAux, nextFirsts] using equality
            have same : firsts = snapshot := Option.some.inj optionEq
            simpa [← same] using firstsNodup
      · exact secondOccurrenceFirstsAux_nodup selected seenSelected
          nextFirsts rest snapshot nextNodup (by
            simpa [secondOccurrenceFirstsAux, nextFirsts, equal] using equality)

theorem secondOccurrenceFirstsList_nodup
    (letters snapshot : List Nat) (selected : Nat)
    (snapshotEq :
      secondOccurrenceFirstsList letters selected = some snapshot) :
    snapshot.Nodup := by
  exact secondOccurrenceFirstsAux_nodup selected false [] letters snapshot
    List.nodup_nil snapshotEq

private theorem secondOccurrenceFirstsAux_true_none_iff
    (selected : Nat) (firsts : List Nat) :
    forall letters : List Nat,
      secondOccurrenceFirstsAux selected true firsts letters = none ↔
        selected ∉ letters
  | [] => by simp [secondOccurrenceFirstsAux]
  | letter :: rest => by
      by_cases equal : letter = selected
      · subst letter
        simp [secondOccurrenceFirstsAux]
      · simp [secondOccurrenceFirstsAux, equal,
          Ne.symm equal,
          secondOccurrenceFirstsAux_true_none_iff selected]

private theorem secondOccurrenceFirstsAux_false_none_iff
    (selected : Nat) :
    forall (firsts letters : List Nat),
      secondOccurrenceFirstsAux selected false firsts letters = none ↔
        letters.count selected ≤ 1
  | _, [] => by simp [secondOccurrenceFirstsAux]
  | firsts, letter :: rest => by
      by_cases equal : letter = selected
      · subst letter
        rw [List.count_cons_self]
        rw [show
          secondOccurrenceFirstsAux selected false firsts
              (selected :: rest) =
            secondOccurrenceFirstsAux selected true
              (if selected ∈ firsts then firsts else selected :: firsts)
              rest by
                simp [secondOccurrenceFirstsAux]]
        rw [secondOccurrenceFirstsAux_true_none_iff]
        rw [← List.count_eq_zero]
        omega
      · rw [List.count_cons_of_ne equal]
        simpa [secondOccurrenceFirstsAux, equal] using
          secondOccurrenceFirstsAux_false_none_iff selected
            (if letter ∈ firsts then firsts else letter :: firsts) rest

theorem secondOccurrenceFirstsList_none_iff
    (letters : List Nat) (selected : Nat) :
    secondOccurrenceFirstsList letters selected = none ↔
      letters.count selected ≤ 1 := by
  exact secondOccurrenceFirstsAux_false_none_iff selected [] letters

theorem selected_mem_prefixBeforeSecond
    (selected : Nat) :
    forall {letters : List Nat},
      selected ∈ letters -> selected ∈ prefixBeforeSecond selected letters
  | [], member => by simp at member
  | letter :: rest, member => by
      by_cases equal : letter = selected
      · subst letter
        simp [prefixBeforeSecond]
      · have restMember : selected ∈ rest := by
          simpa [Ne.symm equal] using member
        simp [prefixBeforeSecond, equal,
          selected_mem_prefixBeforeSecond selected restMember]

/-! ## The five-state marker automaton -/

def markerLaws :
    MarkerLaws Generated.Catalogue.S5_870.mul where
  zeroAbsorbing := by
    intro value
    revert value
    decide
  twoAbsorbing := by
    intro value
    revert value
    decide
  repeatSelected := by decide
  passOther := by decide
  seeComparator := by decide

private theorem mulThreeLeftIdentity (value : Fin 5) :
    Generated.Catalogue.S5_870.mul 3 value = value := by
  revert value
  decide

private theorem mulFourLeftAbsorbing (value : Fin 5) :
    Generated.Catalogue.S5_870.mul 4 value = 4 := by
  revert value
  decide

private theorem markerFoldFour
    (valuation : Nat -> Fin 5) :
    forall letters : List Nat,
      letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_870.mul current (valuation letter)) 4 = 4
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [mulFourLeftAbsorbing]
      exact markerFoldFour valuation rest

/-- Starting immediately after the first selected occurrence, the first of
the comparator and the second selected occurrence chooses absorbing state
`2` or `0`.  Unlike the older initial-variable bridge, the comparator need
not occur at all. -/
private theorem markerFoldFromOne
    (selected comparator : Nat)
    (different : comparator ≠ selected) :
    forall letters : List Nat,
      selected ∈ letters ->
      letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_870.mul current
              (markerValuation selected comparator letter)) 1 =
        if comparator ∈ prefixBefore selected letters then 2 else 0
  | [], selectedMember => by simp at selectedMember
  | letter :: rest, selectedMember => by
      simp only [List.foldl_cons]
      by_cases selectedHit : letter = selected
      · subst letter
        rw [show markerValuation selected comparator selected = (1 : Fin 5) by
          simp [markerValuation]]
        rw [markerLaws.repeatSelected]
        rw [MarkerLaws.foldZero markerLaws
          (markerValuation selected comparator)]
        simp [prefixBefore]
      · by_cases comparatorHit : letter = comparator
        · subst letter
          rw [show markerValuation selected comparator comparator =
              (4 : Fin 5) by
            simp [markerValuation, different]]
          rw [markerLaws.seeComparator]
          rw [MarkerLaws.foldTwo markerLaws
            (markerValuation selected comparator)]
          simp [prefixBefore, different]
        · have selectedRest : selected ∈ rest := by
            simpa [Ne.symm selectedHit] using selectedMember
          rw [show markerValuation selected comparator letter =
              (3 : Fin 5) by
            simp [markerValuation, selectedHit, comparatorHit]]
          rw [markerLaws.passOther]
          rw [markerFoldFromOne selected comparator different rest
            selectedRest]
          simp [prefixBefore, selectedHit,
            Ne.symm comparatorHit]

/-- Evaluate a list as though a virtual left-identity state `3` preceded it.
Row `3` of the exact catalogue table is the identity row, so this agrees with
ordinary semigroup evaluation for every nonempty word. -/
def markerListEval
    (selected comparator : Nat) (letters : List Nat) : Fin 5 :=
  letters.foldl
    (fun current letter =>
      Generated.Catalogue.S5_870.mul current
        (markerValuation selected comparator letter)) 3

theorem markerListEval_word
    (selected comparator : Nat) (word : Word Nat) :
    markerListEval selected comparator word.toList =
      table.semigroup.eval (markerValuation selected comparator) word := by
  cases word with
  | mk head tail =>
      change
        (head :: tail).foldl
            (fun current letter =>
              Generated.Catalogue.S5_870.mul current
                (markerValuation selected comparator letter)) 3 =
          tail.foldl
            (fun current letter =>
              Generated.Catalogue.S5_870.mul current
                (markerValuation selected comparator letter))
            (markerValuation selected comparator head)
      simp only [List.foldl_cons]
      rw [mulThreeLeftIdentity]

/-- The exact table marker law.  For a repeated selected variable and a
different comparator, state zero means precisely that the comparator is not
in the concrete prefix before the second selected occurrence. -/
theorem markerListEval_eq_zero_iff
    (selected comparator : Nat) (different : comparator ≠ selected) :
    forall letters : List Nat,
      2 ≤ letters.count selected ->
      (markerListEval selected comparator letters = 0 ↔
        comparator ∉ prefixBeforeSecond selected letters)
  | [], repeated => by simp at repeated
  | letter :: rest, repeated => by
      by_cases selectedHit : letter = selected
      · subst letter
        have selectedRest : selected ∈ rest := by
          apply List.count_pos_iff.mp
          rw [List.count_cons_self] at repeated
          omega
        unfold markerListEval
        simp only [List.foldl_cons]
        rw [mulThreeLeftIdentity]
        rw [show markerValuation selected comparator selected = (1 : Fin 5) by
          simp [markerValuation]]
        rw [markerFoldFromOne selected comparator different rest
          selectedRest]
        by_cases before :
            comparator ∈ prefixBefore selected rest
        · simp [prefixBeforeSecond, before, different]
        · simp [prefixBeforeSecond, before, different]
      · have repeatedRest : 2 ≤ rest.count selected := by
          simpa [List.count_cons_of_ne selectedHit] using repeated
        by_cases comparatorHit : letter = comparator
        · subst letter
          unfold markerListEval
          simp only [List.foldl_cons]
          rw [mulThreeLeftIdentity]
          rw [show markerValuation selected comparator comparator =
              (4 : Fin 5) by
            simp [markerValuation, different]]
          rw [markerFoldFour (markerValuation selected comparator) rest]
          simp [prefixBeforeSecond, selectedHit]
        · have induction := markerListEval_eq_zero_iff selected comparator
            different rest repeatedRest
          unfold markerListEval at induction ⊢
          simp only [List.foldl_cons]
          rw [mulThreeLeftIdentity]
          rw [show markerValuation selected comparator letter =
              (3 : Fin 5) by
            simp [markerValuation, selectedHit, comparatorHit]]
          simpa [prefixBeforeSecond, selectedHit,
            Ne.symm comparatorHit] using induction

/-- Marker zero is equivalent to absence from the exact snapshot whose
length is the second-occurrence gap. -/
theorem markerSecondOccurrenceFirstsLaw
    (letters snapshot : List Nat) (selected comparator : Nat)
    (different : comparator ≠ selected)
    (repeated : 2 ≤ letters.count selected)
    (snapshotEq :
      secondOccurrenceFirstsList letters selected = some snapshot) :
    markerListEval selected comparator letters = 0 ↔
      comparator ∉ snapshot := by
  rw [markerListEval_eq_zero_iff selected comparator different letters
    repeated]
  exact not_congr <|
    (secondOccurrenceFirstsList_mem_iff letters snapshot selected comparator
      snapshotEq).symm

/-! ## Separation of all three gap-signature fields -/

theorem valid_markerListEval_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (selected comparator : Nat) :
    markerListEval selected comparator identity.lhs.toList =
      markerListEval selected comparator identity.rhs.toList := by
  have evaluated := valid (markerValuation selected comparator)
  rw [← markerListEval_word selected comparator identity.lhs,
    ← markerListEval_word selected comparator identity.rhs] at evaluated
  exact evaluated

private theorem snapshots_perm_of_marker_equality
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (selected : Nat)
    (leftRepeated : 2 ≤ identity.lhs.toList.count selected)
    (rightRepeated : 2 ≤ identity.rhs.toList.count selected)
    (leftSnapshot rightSnapshot : List Nat)
    (leftSnapshotEq :
      secondOccurrenceFirstsList identity.lhs.toList selected =
        some leftSnapshot)
    (rightSnapshotEq :
      secondOccurrenceFirstsList identity.rhs.toList selected =
        some rightSnapshot) :
    leftSnapshot.Perm rightSnapshot := by
  have leftNodup := secondOccurrenceFirstsList_nodup
    identity.lhs.toList leftSnapshot selected leftSnapshotEq
  have rightNodup := secondOccurrenceFirstsList_nodup
    identity.rhs.toList rightSnapshot selected rightSnapshotEq
  have members : forall comparator,
      comparator ∈ leftSnapshot ↔ comparator ∈ rightSnapshot := by
    intro comparator
    by_cases same : comparator = selected
    · subst comparator
      have leftSelectedInWord : selected ∈ identity.lhs.toList :=
        List.count_pos_iff.mp (by omega)
      have rightSelectedInWord : selected ∈ identity.rhs.toList :=
        List.count_pos_iff.mp (by omega)
      have leftSelected : selected ∈ leftSnapshot :=
        (secondOccurrenceFirstsList_mem_iff identity.lhs.toList
          leftSnapshot selected selected leftSnapshotEq).2
          (selected_mem_prefixBeforeSecond selected leftSelectedInWord)
      have rightSelected : selected ∈ rightSnapshot :=
        (secondOccurrenceFirstsList_mem_iff identity.rhs.toList
          rightSnapshot selected selected rightSnapshotEq).2
          (selected_mem_prefixBeforeSecond selected rightSelectedInWord)
      exact ⟨fun _ => rightSelected, fun _ => leftSelected⟩
    · have different : comparator ≠ selected := same
      have evaluated :=
        valid_markerListEval_eq identity valid selected comparator
      have leftLaw := markerSecondOccurrenceFirstsLaw
        identity.lhs.toList leftSnapshot selected comparator different
        leftRepeated leftSnapshotEq
      have rightLaw := markerSecondOccurrenceFirstsLaw
        identity.rhs.toList rightSnapshot selected comparator different
        rightRepeated rightSnapshotEq
      constructor
      · intro leftMember
        apply Decidable.byContradiction
        intro rightAbsent
        have rightZero := rightLaw.mpr rightAbsent
        have leftZero := evaluated.trans rightZero
        exact (leftLaw.mp leftZero) leftMember
      · intro rightMember
        apply Decidable.byContradiction
        intro leftAbsent
        have leftZero := leftLaw.mpr leftAbsent
        have rightZero := evaluated.symm.trans leftZero
        exact (rightLaw.mp rightZero) rightMember
  rw [List.perm_iff_count]
  intro comparator
  rw [leftNodup.count, rightNodup.count]
  simp only [members comparator]

theorem valid_secondOccurrenceGapList_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (selected : Nat) :
    secondOccurrenceGapList identity.lhs.toList selected =
      secondOccurrenceGapList identity.rhs.toList selected := by
  have repeatedIff := valid_repeated_iff identity valid selected
  by_cases leftRepeated : 2 ≤ identity.lhs.toList.count selected
  · have rightRepeated := repeatedIff.mp leftRepeated
    cases leftSnapshotEq :
        secondOccurrenceFirstsList identity.lhs.toList selected with
    | none =>
        have atMost :=
          (secondOccurrenceFirstsList_none_iff
            identity.lhs.toList selected).1 leftSnapshotEq
        omega
    | some leftSnapshot =>
        cases rightSnapshotEq :
            secondOccurrenceFirstsList identity.rhs.toList selected with
        | none =>
            have atMost :=
              (secondOccurrenceFirstsList_none_iff
                identity.rhs.toList selected).1 rightSnapshotEq
            omega
        | some rightSnapshot =>
            have permutation := snapshots_perm_of_marker_equality
              identity valid selected leftRepeated rightRepeated
              leftSnapshot rightSnapshot leftSnapshotEq rightSnapshotEq
            rw [secondOccurrenceGapList_eq_snapshotLength,
              secondOccurrenceGapList_eq_snapshotLength,
              leftSnapshotEq, rightSnapshotEq]
            simp [permutation.length_eq]
  · have leftAtMost : identity.lhs.toList.count selected ≤ 1 := by
      omega
    have rightNotRepeated :
        ¬ 2 ≤ identity.rhs.toList.count selected := by
      intro rightRepeated
      exact leftRepeated (repeatedIff.mpr rightRepeated)
    have rightAtMost : identity.rhs.toList.count selected ≤ 1 := by
      omega
    have leftNone :=
      (secondOccurrenceFirstsList_none_iff
        identity.lhs.toList selected).2 leftAtMost
    have rightNone :=
      (secondOccurrenceFirstsList_none_iff
        identity.rhs.toList selected).2 rightAtMost
    rw [secondOccurrenceGapList_eq_snapshotLength,
      secondOccurrenceGapList_eq_snapshotLength, leftNone, rightNone]

theorem valid_secondOccurrenceGapsList_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    secondOccurrenceGapsList identity.lhs.toList =
      secondOccurrenceGapsList identity.rhs.toList := by
  unfold secondOccurrenceGapsList
  rw [valid_firstOccurrenceSequenceList_eq identity valid]
  apply List.map_congr_left
  intro selected _
  exact valid_secondOccurrenceGapList_eq identity valid selected

private theorem gapSignature_ext
    {left right : GapSignature}
    (firstOccurrences :
      left.firstOccurrences = right.firstOccurrences)
    (repeatFlags : left.repeatFlags = right.repeatFlags)
    (secondOccurrenceGaps :
      left.secondOccurrenceGaps = right.secondOccurrenceGaps) :
    left = right := by
  cases left with
  | mk leftFirsts leftRepeats leftGaps =>
      cases right with
      | mk rightFirsts rightRepeats rightGaps =>
          change leftFirsts = rightFirsts at firstOccurrences
          change leftRepeats = rightRepeats at repeatFlags
          change leftGaps = rightGaps at secondOccurrenceGaps
          subst rightFirsts
          subst rightRepeats
          subst rightGaps
          rfl

/-- The exact catalogue table separates every component of the unbounded
gap signature. -/
theorem valid_gapSignature_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    gapSignature identity.lhs = gapSignature identity.rhs := by
  apply gapSignature_ext
  · exact valid_firstOccurrenceSequenceList_eq identity valid
  · exact valid_repeatFlagsList_eq identity valid
  · exact valid_secondOccurrenceGapsList_eq identity valid

/-- Inhabited semantic-separation package for the exact catalogue table. -/
def tableGapSignatureSeparation :
    TableGapSignatureSeparationObligation where
  separate := valid_gapSignature_eq

end SemigroupBasis.CoRoots.S5_870

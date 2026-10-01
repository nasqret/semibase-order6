import SemigroupBasis.CoRoots.S5_860
import SemigroupBasis.CoRoots.S5_863Completeness
import SemigroupBasis.Examples.SimpleEndpointsFour

namespace SemigroupBasis.CoRoots.S5_860

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107

/-- The exact invariant recorded for `S5_860`: support, the globally simple
variables, and the literal initial and final variables. -/
structure SameSupportSimpleEndpointsSignature
    (left right : Word Nat) : Prop where
  support :
    ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList
  simple :
    ∀ letter,
      left.toList.count letter = 1 ↔
        right.toList.count letter = 1
  initial : left.head = right.head
  final : left.final = right.final

namespace SameSupportSimpleEndpointsSignature

theorem refl (word : Word Nat) :
    SameSupportSimpleEndpointsSignature word word :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, rfl, rfl⟩

theorem symm {left right : Word Nat}
    (same : SameSupportSimpleEndpointsSignature left right) :
    SameSupportSimpleEndpointsSignature right left :=
  ⟨fun letter => (same.support letter).symm,
    fun letter => (same.simple letter).symm,
    same.initial.symm, same.final.symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameSupportSimpleEndpointsSignature left middle)
    (second : SameSupportSimpleEndpointsSignature middle right) :
    SameSupportSimpleEndpointsSignature left right :=
  ⟨fun letter =>
      (first.support letter).trans (second.support letter),
    fun letter =>
      (first.simple letter).trans (second.simple letter),
    first.initial.trans second.initial,
    first.final.trans second.final⟩

/-- Support and simplicity determine multiplicity capped at two. -/
theorem capped {left right : Word Nat}
    (same : SameSupportSimpleEndpointsSignature left right)
    (letter : Nat) :
    cappedMultiplicity left letter =
      cappedMultiplicity right letter := by
  by_cases leftAbsent : letter ∉ left.toList
  · have rightAbsent : letter ∉ right.toList := by
      intro member
      exact leftAbsent ((same.support letter).2 member)
    have leftZero : left.toList.count letter = 0 :=
      List.count_eq_zero.mpr leftAbsent
    have rightZero : right.toList.count letter = 0 :=
      List.count_eq_zero.mpr rightAbsent
    simp [cappedMultiplicity, leftZero, rightZero]
  · by_cases leftSimple : left.toList.count letter = 1
    · have rightSimple : right.toList.count letter = 1 :=
        (same.simple letter).1 leftSimple
      simp [cappedMultiplicity, leftSimple, rightSimple]
    · have leftPresent : letter ∈ left.toList :=
        Decidable.not_not.mp leftAbsent
      have rightPresent : letter ∈ right.toList :=
        (same.support letter).1 leftPresent
      have rightNotSimple : right.toList.count letter ≠ 1 := by
        intro rightSimple
        exact leftSimple ((same.simple letter).2 rightSimple)
      have leftAtLeastTwo : 2 ≤ left.toList.count letter := by
        have positive : 0 < left.toList.count letter :=
          List.count_pos_iff.mpr leftPresent
        omega
      have rightAtLeastTwo : 2 ≤ right.toList.count letter := by
        have positive : 0 < right.toList.count letter :=
          List.count_pos_iff.mpr rightPresent
        omega
      unfold cappedMultiplicity
      simp [Nat.min_def, leftAtLeastTwo, rightAtLeastTwo]

end SameSupportSimpleEndpointsSignature

/-- Transport every derivation in the five-law `S5_863` core into the
extended eight-law `S5_860` basis. -/
theorem liftS5_863Derivation
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_863.basis left right) :
    Derives basis left right :=
  derivation.transport fun identity member =>
    Derives.fromBasis <| by
      simp [basis, sharedCore, member]

/-- The completed `S5_863` normalizer remains derivable after adjoining the
three `S5_860` interior-swap laws. -/
theorem derivesCoreCanonical (word : Word Nat) :
    Derives basis word
      (SemigroupBasis.CoRoots.S5_863.coreCanonicalWord word) :=
  liftS5_863Derivation
    (SemigroupBasis.CoRoots.S5_863.derivesCoreCanonical word)

/-- An arbitrary permutation of the interior is derivable while both
nonempty endpoint contexts remain fixed. -/
theorem derivesInteriorPermutation
    (initial final : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives basis
      (wordOfEndpoints initial left final)
      (wordOfEndpoints initial right final) := by
  induction permutation generalizing initial with
  | nil =>
      exact Derives.refl _
  | cons letter _ induction =>
      simpa [wordOfEndpoints_cons] using
        Derives.prepend (Word.singleton initial) (induction letter)
  | swap left right suffix =>
      simpa [wordOfEndpoints_eq, Word.append_assoc] using
        derivesInteriorSwap
          (Word.singleton initial)
          (Word.singleton right)
          (Word.singleton left)
          (wordOfPrefixFinal suffix final)
  | trans _ _ first second =>
      exact Derives.trans (first initial) (second initial)

private theorem dropLast_append_getLastD
    (letters : List Nat) (fallback : Nat)
    (nonempty : letters ≠ []) :
    letters.dropLast ++ [letters.getLastD fallback] = letters := by
  obtain ⟨head, tail, rfl⟩ :=
    List.exists_cons_of_ne_nil nonempty
  have reconstruction :=
    List.dropLast_concat_getLast (l := head :: tail) (by simp)
  rw [List.getLast_eq_getLastD] at reconstruction
  simpa only [List.getLastD_cons] using reconstruction

private theorem tail_perm_of_head_toList_perm
    {left right : Word Nat}
    (heads : left.head = right.head)
    (permutation : left.toList.Perm right.toList) :
    left.tail.Perm right.tail := by
  have erased := permutation.erase left.head
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simp only at heads
          subst rightHead
          simpa [Word.toList] using erased

private theorem wordOfEndpoints_dropLast
    (word : Word Nat) (tailNonempty : word.tail ≠ []) :
    wordOfEndpoints word.head word.tail.dropLast word.final = word := by
  apply Word.toList_injective
  rw [toList_wordOfEndpoints]
  simp only [Word.toList, List.cons.injEq, true_and]
  simpa [Word.final] using
    dropLast_append_getLastD word.tail word.head tailNonempty

/-- Words with equal initial and final variables and the same full multiset
are interderivable using only interior permutations. -/
theorem derivesOfHeadFinalPermutation
    {left right : Word Nat}
    (heads : left.head = right.head)
    (finals : left.final = right.final)
    (permutation : left.toList.Perm right.toList) :
    Derives basis left right := by
  have tailPermutation : left.tail.Perm right.tail :=
    tail_perm_of_head_toList_perm heads permutation
  by_cases leftTailEmpty : left.tail = []
  · have rightTailEmpty : right.tail = [] := by
      apply List.eq_nil_of_length_eq_zero
      have lengths := tailPermutation.length_eq
      simpa [leftTailEmpty] using lengths.symm
    have wordEquality : left = right := by
      apply Word.toList_injective
      simp [Word.toList, leftTailEmpty, rightTailEmpty, heads]
    rw [wordEquality]
    exact Derives.refl _
  · have rightTailNonempty : right.tail ≠ [] := by
      intro rightTailEmpty
      apply leftTailEmpty
      apply List.eq_nil_of_length_eq_zero
      have lengths := tailPermutation.length_eq
      simpa [rightTailEmpty] using lengths
    have finalValues :
        left.tail.getLastD left.head =
          right.tail.getLastD right.head := by
      simpa [Word.final] using finals
    have middlePermutation :
        left.tail.dropLast.Perm right.tail.dropLast := by
      rw [List.perm_iff_count]
      intro letter
      have tailCount :=
        (List.perm_iff_count.mp tailPermutation) letter
      have leftReconstruction :=
        dropLast_append_getLastD
          left.tail left.head leftTailEmpty
      have rightReconstruction :=
        dropLast_append_getLastD
          right.tail right.head rightTailNonempty
      rw [← leftReconstruction, ← rightReconstruction] at tailCount
      simp only [List.count_append, List.count_cons,
        List.count_nil, Nat.add_zero] at tailCount
      rw [finalValues] at tailCount
      omega
    have bridge :=
      derivesInteriorPermutation left.head left.final middlePermutation
    have leftShape :=
      wordOfEndpoints_dropLast left leftTailEmpty
    have rightShape :=
      wordOfEndpoints_dropLast right rightTailNonempty
    have targetShape :
        wordOfEndpoints left.head right.tail.dropLast left.final =
          right := by
      rw [heads, finals]
      exact rightShape
    rw [leftShape, targetShape] at bridge
    exact bridge

private theorem mem_doubleCanonicalList_iff (tested : Nat) :
    ∀ letters : List Nat,
      tested ∈ SemigroupBasis.CoRoots.S5_345.doubleCanonicalList letters ↔
        tested ∈ letters
  | [] => by
      simp [SemigroupBasis.CoRoots.S5_345.doubleCanonicalList]
  | letter :: rest => by
      have induction := mem_doubleCanonicalList_iff tested rest
      by_cases repeated :
          letter ∈
            SemigroupBasis.CoRoots.S5_345.doubleCanonicalList rest
      · by_cases equal : tested = letter
        · simp [SemigroupBasis.CoRoots.S5_345.doubleCanonicalList,
            repeated, induction, equal]
        · simp [SemigroupBasis.CoRoots.S5_345.doubleCanonicalList,
            repeated, induction, equal]
      · simp [SemigroupBasis.CoRoots.S5_345.doubleCanonicalList,
          repeated, induction]

private theorem count_filter_ne_self
    (selected : Nat) (letters : List Nat) :
    (letters.filter
        (fun letter => decide (letter ≠ selected))).count selected = 0 := by
  apply List.count_eq_zero.mpr
  intro member
  have impossible : selected ≠ selected := by
    simpa using (List.mem_filter.mp member).2
  exact impossible rfl

private theorem count_filter_ne_of_ne
    (selected tested : Nat) (different : tested ≠ selected)
    (letters : List Nat) :
    (letters.filter
        (fun letter => decide (letter ≠ selected))).count tested =
      letters.count tested :=
  List.count_filter
    (p := fun letter => decide (letter ≠ selected))
    (by simp [different])

/-- The `S5_863` first-occurrence renderer realizes multiplicity truncated
at two. -/
private theorem count_doubleCanonicalList (tested : Nat) :
    ∀ letters : List Nat,
      (SemigroupBasis.CoRoots.S5_345.doubleCanonicalList letters).count
          tested =
        Nat.min (letters.count tested) 2
  | [] => by
      simp [SemigroupBasis.CoRoots.S5_345.doubleCanonicalList]
  | letter :: rest => by
      have induction := count_doubleCanonicalList tested rest
      let reduced :=
        SemigroupBasis.CoRoots.S5_345.doubleCanonicalList rest
      by_cases repeated : letter ∈ reduced
      · have repeatedRest : letter ∈ rest :=
          (mem_doubleCanonicalList_iff letter rest).1 repeated
        by_cases equal : tested = letter
        · subst letter
          have restPositive : 0 < rest.count tested :=
            List.count_pos_iff.mpr repeatedRest
          have filteredZero := count_filter_ne_self tested reduced
          simp only [SemigroupBasis.CoRoots.S5_345.doubleCanonicalList,
            reduced, if_pos repeated, List.count_append,
            filteredZero, List.count_cons_self, List.count_nil,
            Nat.add_zero, Nat.min_def]
          split <;> omega
        · have filteredCount :=
            count_filter_ne_of_ne letter tested equal reduced
          simp [SemigroupBasis.CoRoots.S5_345.doubleCanonicalList,
            reduced, repeated, List.count_append, filteredCount,
            induction, equal, Ne.symm equal]
      · have notRest : letter ∉ rest := by
          intro member
          exact repeated
            ((mem_doubleCanonicalList_iff letter rest).2 member)
        by_cases equal : tested = letter
        · subst letter
          have reducedZero : reduced.count tested = 0 :=
            List.count_eq_zero.mpr repeated
          have restZero : rest.count tested = 0 :=
            List.count_eq_zero.mpr notRest
          simp [SemigroupBasis.CoRoots.S5_345.doubleCanonicalList,
            reduced, repeated, reducedZero, restZero]
        · simp [SemigroupBasis.CoRoots.S5_345.doubleCanonicalList,
            reduced, repeated, induction, equal, Ne.symm equal]

private theorem count_retainFirst_self_le_one (selected : Nat) :
    ∀ letters : List Nat,
      (SemigroupBasis.CoRoots.S5_345.retainFirst selected letters).count
          selected ≤ 1
  | [] => by
      simp [SemigroupBasis.CoRoots.S5_345.retainFirst]
  | letter :: rest => by
      by_cases equal : letter = selected
      · subst letter
        have filteredZero := count_filter_ne_self selected rest
        simp only [decide_not] at filteredZero
        simp [SemigroupBasis.CoRoots.S5_345.retainFirst,
          filteredZero]
      · have induction := count_retainFirst_self_le_one selected rest
        simpa [SemigroupBasis.CoRoots.S5_345.retainFirst, equal] using
          induction

private theorem coreCanonicalList_count_le_two :
    ∀ (letters : List Nat) (tested : Nat),
      (SemigroupBasis.CoRoots.S5_345.coreCanonicalList letters).count
          tested ≤ 2
  | [], tested => by
      simp [SemigroupBasis.CoRoots.S5_345.coreCanonicalList]
  | head :: tail, tested => by
      let final := tail.getLastD head
      let retained :=
        SemigroupBasis.CoRoots.S5_345.retainFirst final
          (head :: tail).dropLast
      change
        (SemigroupBasis.CoRoots.S5_345.doubleCanonicalList retained ++
            [final]).count tested ≤ 2
      rw [List.count_append, count_doubleCanonicalList tested retained]
      by_cases equal : tested = final
      · subst tested
        have retainedBound :=
          count_retainFirst_self_le_one final (head :: tail).dropLast
        change retained.count final ≤ 1 at retainedBound
        simp only [List.count_cons_self, List.count_nil, Nat.add_zero]
        simp only [Nat.min_def]
        split <;> omega
      · have finalCountZero : [final].count tested = 0 := by
          simp [equal, Ne.symm equal]
        rw [finalCountZero, Nat.add_zero]
        exact Nat.min_le_right _ _

private theorem toList_coreCanonicalWord (word : Word Nat) :
    (SemigroupBasis.CoRoots.S5_863.coreCanonicalWord word).toList =
      SemigroupBasis.CoRoots.S5_345.coreCanonicalList word.toList := by
  cases word with
  | mk head tail =>
      unfold SemigroupBasis.CoRoots.S5_863.coreCanonicalWord
      unfold SemigroupBasis.CoRoots.S5_345.coreCanonicalList
      simp only [Word.toList]
      generalize
        SemigroupBasis.CoRoots.S5_345.doubleCanonicalList
            (SemigroupBasis.CoRoots.S5_345.retainFirst
              (tail.getLastD head) (head :: tail).dropLast) = rendered
      cases rendered <;> rfl

private theorem coreCanonicalWord_count_le_two
    (word : Word Nat) (tested : Nat) :
    (SemigroupBasis.CoRoots.S5_863.coreCanonicalWord word).toList.count
        tested ≤ 2 := by
  rw [toList_coreCanonicalWord]
  exact coreCanonicalList_count_le_two word.toList tested

private theorem coreCanonical_toList_perm
    {left right : Word Nat}
    (same : SameSupportSimpleEndpointsSignature left right) :
    (SemigroupBasis.CoRoots.S5_863.coreCanonicalWord left).toList.Perm
      (SemigroupBasis.CoRoots.S5_863.coreCanonicalWord right).toList := by
  apply List.perm_iff_count.mpr
  intro letter
  have leftSignature :=
    SemigroupBasis.CoRoots.S5_863.derives_sameSignature
      (SemigroupBasis.CoRoots.S5_863.derivesCoreCanonical left)
  have rightSignature :=
    SemigroupBasis.CoRoots.S5_863.derives_sameSignature
      (SemigroupBasis.CoRoots.S5_863.derivesCoreCanonical right)
  have coreCapped :
      cappedMultiplicity
          (SemigroupBasis.CoRoots.S5_863.coreCanonicalWord left) letter =
        cappedMultiplicity
          (SemigroupBasis.CoRoots.S5_863.coreCanonicalWord right) letter :=
    (leftSignature.capped letter).symm.trans <|
      (same.capped letter).trans (rightSignature.capped letter)
  have leftBound := coreCanonicalWord_count_le_two left letter
  have rightBound := coreCanonicalWord_count_le_two right letter
  unfold cappedMultiplicity at coreCapped
  have coreCapped' :
      Nat.min
          ((SemigroupBasis.CoRoots.S5_863.coreCanonicalWord left).toList.count
            letter) 2 =
        Nat.min
          ((SemigroupBasis.CoRoots.S5_863.coreCanonicalWord right).toList.count
            letter) 2 := by
    simpa only [Nat.min_comm] using coreCapped
  simpa [Nat.min_def, leftBound, rightBound] using coreCapped'

private theorem head_eq_of_firstOccurrenceSequence_eq
    {left right : Word Nat}
    (sequence :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    left.head = right.head := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simp only [Word.toList, firstOccurrenceSequence] at sequence
          exact (List.cons.inj sequence).1

/-- Equal support, simple-variable set, initial variable, and final variable
suffice for derivability from the eight recorded `S5_860` laws. -/
theorem derivesOfSameSupportSimpleEndpointsSignature
    {left right : Word Nat}
    (same : SameSupportSimpleEndpointsSignature left right) :
    Derives basis left right := by
  let leftCore :=
    SemigroupBasis.CoRoots.S5_863.coreCanonicalWord left
  let rightCore :=
    SemigroupBasis.CoRoots.S5_863.coreCanonicalWord right
  have leftCoreSignature :
      SemigroupBasis.CoRoots.S5_863.SameInitialSimpleFinalSignature
        left leftCore :=
    SemigroupBasis.CoRoots.S5_863.derives_sameSignature
      (SemigroupBasis.CoRoots.S5_863.derivesCoreCanonical left)
  have rightCoreSignature :
      SemigroupBasis.CoRoots.S5_863.SameInitialSimpleFinalSignature
        right rightCore :=
    SemigroupBasis.CoRoots.S5_863.derives_sameSignature
      (SemigroupBasis.CoRoots.S5_863.derivesCoreCanonical right)
  have leftCoreInitial : left.head = leftCore.head :=
    head_eq_of_firstOccurrenceSequence_eq
      leftCoreSignature.firstOccurrences
  have rightCoreInitial : right.head = rightCore.head :=
    head_eq_of_firstOccurrenceSequence_eq
      rightCoreSignature.firstOccurrences
  have coreInitial : leftCore.head = rightCore.head :=
    leftCoreInitial.symm.trans <|
      same.initial.trans rightCoreInitial
  have coreFinal : leftCore.final = rightCore.final :=
    leftCoreSignature.finalLetter.symm.trans <|
      same.final.trans rightCoreSignature.finalLetter
  have corePermutation : leftCore.toList.Perm rightCore.toList := by
    simpa [leftCore, rightCore] using
      coreCanonical_toList_perm same
  have leftNormal : Derives basis left leftCore := by
    simpa [leftCore] using derivesCoreCanonical left
  have rightNormal : Derives basis right rightCore := by
    simpa [rightCore] using derivesCoreCanonical right
  have bridge : Derives basis leftCore rightCore :=
    derivesOfHeadFinalPermutation
      coreInitial coreFinal corePermutation
  exact leftNormal.trans <| bridge.trans rightNormal.symm

/-- Source-level derivational-completeness obligation for the recorded
`S5_860` signature. -/
def SupportSimpleEndpointsDerivationalCompleteness : Prop :=
  ∀ left right : Word Nat,
    SameSupportSimpleEndpointsSignature left right →
      Derives basis left right

/-- Witness for the source-level `S5_860` completeness obligation. -/
theorem supportSimpleEndpointsDerivationalCompleteness :
    SupportSimpleEndpointsDerivationalCompleteness := by
  intro left right same
  exact derivesOfSameSupportSimpleEndpointsSignature same

end SemigroupBasis.CoRoots.S5_860

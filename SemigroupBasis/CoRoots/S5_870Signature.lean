import SemigroupBasis.CoRoots.S5_870Reduction

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_870

open SemigroupBasis

/-! ## Deleting an occurrence after the first two -/

private theorem firstOccurrenceSequenceAux_delete_known
    (deleted : Nat) :
    ∀ (seen before after : List Nat),
      deleted ∈ seen ∨ deleted ∈ before →
      firstOccurrenceSequenceAux seen
          (before ++ deleted :: after) =
        firstOccurrenceSequenceAux seen (before ++ after)
  | seen, [], after, known => by
      have member : deleted ∈ seen := by
        simpa using known
      simp [firstOccurrenceSequenceAux, member]
  | seen, head :: rest, after, known => by
      by_cases headMember : head ∈ seen
      · have nextKnown : deleted ∈ seen ∨ deleted ∈ rest := by
          rcases known with seenMember | beforeMember
          · exact Or.inl seenMember
          · rcases List.mem_cons.mp beforeMember with equal | restMember
            · subst head
              exact Or.inl headMember
            · exact Or.inr restMember
        simpa [firstOccurrenceSequenceAux, headMember] using
          firstOccurrenceSequenceAux_delete_known
            deleted seen rest after nextKnown
      · have nextKnown :
            deleted ∈ head :: seen ∨ deleted ∈ rest := by
          rcases known with seenMember | beforeMember
          · exact Or.inl (by simp [seenMember])
          · rcases List.mem_cons.mp beforeMember with equal | restMember
            · subst head
              exact Or.inl (by simp)
            · exact Or.inr restMember
        simpa [firstOccurrenceSequenceAux, headMember] using
          congrArg (List.cons head)
            (firstOccurrenceSequenceAux_delete_known
              deleted (head :: seen) rest after nextKnown)

/-- Removing an occurrence preceded by two copies does not change the
first-occurrence sequence. -/
theorem firstOccurrenceSequenceList_delete_after_two
    (deleted : Nat) (before after : List Nat)
    (twoBefore : 2 ≤ before.count deleted) :
    firstOccurrenceSequenceList (before ++ deleted :: after) =
      firstOccurrenceSequenceList (before ++ after) := by
  have member : deleted ∈ before :=
    List.count_pos_iff.mp (by omega)
  simpa [firstOccurrenceSequenceList] using
    firstOccurrenceSequenceAux_delete_known
      deleted [] before after (Or.inr member)

/-- Removing an occurrence preceded by two copies preserves every repeat
flag: only the deleted letter's count changes, and both counts remain at
least two. -/
theorem repeatFlagsList_delete_after_two
    (deleted : Nat) (before after : List Nat)
    (twoBefore : 2 ≤ before.count deleted) :
    repeatFlagsList (before ++ deleted :: after) =
      repeatFlagsList (before ++ after) := by
  unfold repeatFlagsList
  rw [firstOccurrenceSequenceList_delete_after_two
    deleted before after twoBefore]
  apply List.map_congr_left
  intro tested _
  by_cases equal : tested = deleted
  · subst tested
    simp only [List.count_append, List.count_cons_self]
    have leftRepeated :
        2 ≤ before.count deleted + (after.count deleted + 1) := by
      omega
    have rightRepeated :
        2 ≤ before.count deleted + after.count deleted := by
      omega
    simp [leftRepeated, rightRepeated]
  · have different : deleted ≠ tested := Ne.symm equal
    simp [List.count_append, different]

private theorem secondOccurrenceGapAux_suffix_irrelevant
    (selected : Nat) :
    ∀ (seenSelected : Bool) (firsts before leftSuffix rightSuffix : List Nat),
      (if seenSelected then 1 else 2) ≤ before.count selected →
      secondOccurrenceGapAux selected seenSelected firsts
          (before ++ leftSuffix) =
        secondOccurrenceGapAux selected seenSelected firsts
          (before ++ rightSuffix)
  | false, firsts, [], leftSuffix, rightSuffix, enough => by
      simp at enough
  | true, firsts, [], leftSuffix, rightSuffix, enough => by
      simp at enough
  | false, firsts, head :: rest, leftSuffix, rightSuffix, enough => by
      by_cases equal : head = selected
      · subst head
        have restEnough : 1 ≤ rest.count selected := by
          have countEnough : 2 ≤ rest.count selected + 1 := by
            simpa only [Bool.false_eq_true, if_false,
              List.count_cons_self] using enough
          exact Nat.le_of_succ_le_succ countEnough
        simpa [secondOccurrenceGapAux] using
          secondOccurrenceGapAux_suffix_irrelevant
            selected true
              (if selected ∈ firsts then firsts else selected :: firsts)
              rest leftSuffix rightSuffix restEnough
      · have restEnough : 2 ≤ rest.count selected := by
          simpa [List.count_cons_of_ne equal] using enough
        simpa [secondOccurrenceGapAux, equal] using
          secondOccurrenceGapAux_suffix_irrelevant
            selected false
              (if head ∈ firsts then firsts else head :: firsts)
              rest leftSuffix rightSuffix restEnough
  | true, firsts, head :: rest, leftSuffix, rightSuffix, enough => by
      by_cases equal : head = selected
      · subst head
        simp [secondOccurrenceGapAux]
      · have restEnough : 1 ≤ rest.count selected := by
          simpa [List.count_cons_of_ne equal] using enough
        simpa [secondOccurrenceGapAux, equal] using
          secondOccurrenceGapAux_suffix_irrelevant
            selected true
              (if head ∈ firsts then firsts else head :: firsts)
              rest leftSuffix rightSuffix restEnough

private theorem member_nextFirsts_or_rest
    (deleted head : Nat) (firsts rest : List Nat)
    (known : deleted ∈ firsts ∨ deleted ∈ head :: rest) :
    deleted ∈ (if head ∈ firsts then firsts else head :: firsts) ∨
      deleted ∈ rest := by
  by_cases headMember : head ∈ firsts
  · simp only [headMember, if_true]
    rcases known with firstsMember | beforeMember
    · exact Or.inl firstsMember
    · rcases List.mem_cons.mp beforeMember with equal | restMember
      · subst deleted
        exact Or.inl headMember
      · exact Or.inr restMember
  · simp only [headMember, if_false]
    rcases known with firstsMember | beforeMember
    · exact Or.inl (by simp [firstsMember])
    · rcases List.mem_cons.mp beforeMember with equal | restMember
      · subst deleted
        exact Or.inl (by simp)
      · exact Or.inr restMember

private theorem secondOccurrenceGapAux_delete_known
    (selected deleted : Nat) (different : deleted ≠ selected) :
    ∀ (seenSelected : Bool) (firsts before after : List Nat),
      deleted ∈ firsts ∨ deleted ∈ before →
      secondOccurrenceGapAux selected seenSelected firsts
          (before ++ deleted :: after) =
        secondOccurrenceGapAux selected seenSelected firsts
          (before ++ after)
  | seenSelected, firsts, [], after, known => by
      have member : deleted ∈ firsts := by
        simpa using known
      simp [secondOccurrenceGapAux, different, member]
  | seenSelected, firsts, head :: rest, after, known => by
      have nextKnown :
          deleted ∈
              (if head ∈ firsts then firsts else head :: firsts) ∨
            deleted ∈ rest :=
        member_nextFirsts_or_rest deleted head firsts rest known
      by_cases equal : head = selected
      · subst head
        cases seenSelected with
        | false =>
            simpa [secondOccurrenceGapAux] using
              secondOccurrenceGapAux_delete_known
                selected deleted different true
                  (if selected ∈ firsts then firsts
                    else selected :: firsts)
                  rest after nextKnown
        | true =>
            simp [secondOccurrenceGapAux]
      · simpa [secondOccurrenceGapAux, equal] using
          secondOccurrenceGapAux_delete_known
            selected deleted different seenSelected
              (if head ∈ firsts then firsts else head :: firsts)
              rest after nextKnown

/-- Removing an occurrence preceded by two copies does not change the gap of
the second occurrence of any selected letter. -/
theorem secondOccurrenceGapList_delete_after_two
    (deleted selected : Nat) (before after : List Nat)
    (twoBefore : 2 ≤ before.count deleted) :
    secondOccurrenceGapList (before ++ deleted :: after) selected =
      secondOccurrenceGapList (before ++ after) selected := by
  by_cases equal : deleted = selected
  · subst selected
    simpa [secondOccurrenceGapList] using
      secondOccurrenceGapAux_suffix_irrelevant
        deleted false [] before (deleted :: after) after twoBefore
  · have member : deleted ∈ before :=
      List.count_pos_iff.mp (by omega)
    simpa [secondOccurrenceGapList] using
      secondOccurrenceGapAux_delete_known
        selected deleted equal false [] before after (Or.inr member)

/-- Removing an occurrence preceded by two copies preserves the complete
list of second-occurrence gaps. -/
theorem secondOccurrenceGapsList_delete_after_two
    (deleted : Nat) (before after : List Nat)
    (twoBefore : 2 ≤ before.count deleted) :
    secondOccurrenceGapsList (before ++ deleted :: after) =
      secondOccurrenceGapsList (before ++ after) := by
  unfold secondOccurrenceGapsList
  rw [firstOccurrenceSequenceList_delete_after_two
    deleted before after twoBefore]
  apply List.map_congr_left
  intro selected _
  exact secondOccurrenceGapList_delete_after_two
    deleted selected before after twoBefore

/-- The full gap signature ignores every occurrence after the first two. -/
theorem gapSignatureList_delete_after_two
    (deleted : Nat) (before after : List Nat)
    (twoBefore : 2 ≤ before.count deleted) :
    gapSignatureList (before ++ deleted :: after) =
      gapSignatureList (before ++ after) := by
  unfold gapSignatureList
  rw [firstOccurrenceSequenceList_delete_after_two
      deleted before after twoBefore,
    repeatFlagsList_delete_after_two deleted before after twoBefore,
    secondOccurrenceGapsList_delete_after_two
      deleted before after twoBefore]

/-! ## Full cap-scan signature preservation -/

private theorem gapSignatureList_foldl_capStep :
    ∀ (remaining kept : List Nat),
      (∀ tested, kept.count tested ≤ 2) →
      gapSignatureList (kept ++ remaining) =
        gapSignatureList (remaining.foldl capStep kept)
  | [], kept, _ => by
      simp
  | letter :: rest, kept, keptLimited => by
      by_cases room : kept.count letter < 2
      · have nextLimited :
            ∀ tested, (kept ++ [letter]).count tested ≤ 2 := by
          intro tested
          rw [List.count_append]
          by_cases equal : letter = tested
          · subst letter
            simp only [List.count_cons_self, List.count_nil]
            omega
          · have singletonZero : [letter].count tested = 0 := by
              simp [equal]
            rw [singletonZero, Nat.add_zero]
            exact keptLimited tested
        simpa [capStep, room, List.append_assoc] using
          gapSignatureList_foldl_capStep rest
            (kept ++ [letter]) nextLimited
      · have twoBefore : 2 ≤ kept.count letter := by
          have bound := keptLimited letter
          omega
        calc
          gapSignatureList (kept ++ letter :: rest) =
              gapSignatureList (kept ++ rest) :=
            gapSignatureList_delete_after_two
              letter kept rest twoBefore
          _ = gapSignatureList (rest.foldl capStep kept) :=
            gapSignatureList_foldl_capStep rest kept keptLimited
          _ = gapSignatureList
              ((letter :: rest).foldl capStep kept) := by
            simp [capStep, room]

/-- The left-to-right cap scan preserves all three fields of the gap
signature. -/
theorem gapSignatureList_capScan (letters : List Nat) :
    gapSignatureList letters = gapSignatureList (capScan letters) := by
  simpa [capScan] using
    gapSignatureList_foldl_capStep letters [] (by simp)

/-- Word-level full-signature preservation for the cap reduction. -/
theorem gapSignature_capScanWord (word : Word Nat) :
    gapSignature word = gapSignature (capScanWord word) := by
  unfold gapSignature
  rw [capScanWord_toList]
  exact gapSignatureList_capScan word.toList

/-- The cap scan now supplies the complete two-limited reduction witness. -/
def twoLimitedReduction : TwoLimitedReductionObligation where
  reduce word :=
    ⟨capScanWord word,
      capScanWord_isTwoLimited word,
      gapSignature_capScanWord word,
      derivesCapScanWord word⟩

end SemigroupBasis.CoRoots.S5_870

import SemigroupBasis.CoRoots.Order6PublishedMonoid15Syntax

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6PublishedMonoid15

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons := S5_107.listWordOfCons

/-! ## Duplicate contraction after a genuine earlier occurrence -/

private theorem listDerivesPowerContraction (letter : Nat) :
    ListDerives [letter, letter, letter] [letter, letter] := by
  simpa [Word.singleton, Word.append, Word.append_assoc] using
    (S5_107.ListDerives.ofWord (basis := basis)
      (derivesPowerExpansion (Word.singleton letter)).symm)

private theorem listDerivesFinalGapContraction
    (letter bridgeHead : Nat) (bridgeTail : List Nat) :
    ListDerives
      ([letter] ++ (bridgeHead :: bridgeTail) ++ [letter, letter])
      ([letter] ++ (bridgeHead :: bridgeTail) ++ [letter]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesFinalGapExpansion
          (Word.singleton letter)
          (listWordOfCons bridgeHead bridgeTail)).symm)

/-- Contract an adjacent duplicate in a later block. The premise is the
earlier occurrence that the invalid S5 initial/general cap laws omitted. -/
theorem listDerivesContractAdjacentAfterSeen
    (stem suffix : List Nat) (letter : Nat)
    (seen : letter ∈ stem) :
    ListDerives (stem ++ [letter, letter] ++ suffix)
      (stem ++ [letter] ++ suffix) := by
  obtain ⟨before, after, stemShape⟩ :=
    List.mem_iff_append.mp seen
  cases after with
  | nil =>
      simpa [stemShape, List.append_assoc] using
        S5_107.ListDerives.context before suffix
          (listDerivesPowerContraction letter)
  | cons bridgeHead bridgeTail =>
      simpa [stemShape, List.append_assoc] using
        S5_107.ListDerives.context before suffix
          (listDerivesFinalGapContraction
            letter bridgeHead bridgeTail)

/-! ## Support-preserving normalization behind a seen stem -/

/-- Keep the final occurrence of each displayed letter. -/
def deduplicateLater : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ rest then deduplicateLater rest
      else letter :: deduplicateLater rest

theorem deduplicateLater_mem_iff (tested : Nat) :
    ∀ letters : List Nat,
      tested ∈ deduplicateLater letters ↔ tested ∈ letters
  | [] => by simp [deduplicateLater]
  | letter :: rest => by
      by_cases present : letter ∈ rest
      · rw [deduplicateLater, if_pos present,
          deduplicateLater_mem_iff tested rest]
        constructor
        · exact List.Mem.tail letter
        · intro member
          rcases List.mem_cons.mp member with atLetter | inRest
          · simpa [atLetter] using present
          · exact inRest
      · by_cases equal : tested = letter
        · subst tested
          simp [deduplicateLater, present]
        · simp [deduplicateLater, present, equal,
            deduplicateLater_mem_iff tested rest]

theorem deduplicateLater_nodup :
    ∀ letters : List Nat, (deduplicateLater letters).Nodup
  | [] => by simp [deduplicateLater]
  | letter :: rest => by
      by_cases present : letter ∈ rest
      · simpa [deduplicateLater, present] using
          deduplicateLater_nodup rest
      · rw [deduplicateLater, if_neg present, List.nodup_cons]
        exact ⟨by
          intro member
          exact present <|
            (deduplicateLater_mem_iff letter rest).mp member,
          deduplicateLater_nodup rest⟩

private theorem perm_of_nodup_mem_iff
    {left right : List Nat}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (members : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro letter
  rw [leftNodup.count, rightNodup.count]
  simp only [members letter]

private theorem perm_append_comm (left right : List Nat) :
    (left ++ right).Perm (right ++ left) := by
  rw [List.perm_iff_count]
  intro letter
  simp only [List.count_append]
  omega

/-- Delete all duplicate copies in a later block. Every block letter must
already occur in the stem; this is precisely the gap-parser invariant. -/
theorem listDerivesDeduplicateLater
    (suffix : List Nat) :
    ∀ (stem source : List Nat),
      (∀ letter, letter ∈ source → letter ∈ stem) →
      ListDerives (stem ++ source ++ suffix)
        (stem ++ deduplicateLater source ++ suffix)
  | _, [], _ => by
      simpa using S5_107.ListDerives.refl (basis := basis) _
  | stem, letter :: rest, sourceSeen => by
      have restSeen :
          ∀ tested, tested ∈ rest → tested ∈ stem ++ [letter] := by
        intro tested member
        exact List.mem_append.mpr <| Or.inl <|
          sourceSeen tested (List.Mem.tail letter member)
      have recurse :=
        listDerivesDeduplicateLater suffix (stem ++ [letter]) rest restSeen
      have recurseShape :
          ListDerives (stem ++ (letter :: rest) ++ suffix)
            (stem ++ [letter] ++ deduplicateLater rest ++ suffix) := by
        simpa [List.append_assoc] using recurse
      by_cases present : letter ∈ rest
      · have retained : letter ∈ deduplicateLater rest :=
          (deduplicateLater_mem_iff letter rest).mpr present
        have exposePermutation :
            (letter :: deduplicateLater rest).Perm
              (letter :: letter :: (deduplicateLater rest).erase letter) :=
          List.Perm.cons letter (List.perm_cons_erase retained)
        have exposeSeen :
            ∀ tested, tested ∈ letter :: deduplicateLater rest →
              tested ∈ stem := by
          intro tested member
          rcases List.mem_cons.mp member with atLetter | inRest
          · simpa [atLetter] using
              sourceSeen letter (List.Mem.head rest)
          · exact sourceSeen tested (List.Mem.tail letter <|
              (deduplicateLater_mem_iff tested rest).mp inRest)
        have expose :
            ListDerives
              (stem ++ [letter] ++ deduplicateLater rest ++ suffix)
              (stem ++ [letter, letter] ++
                (deduplicateLater rest).erase letter ++ suffix) := by
          simpa [List.append_assoc] using
            listDerivesPermuteAfterSeen stem suffix exposeSeen
              exposePermutation
        have contract :
            ListDerives
              (stem ++ [letter, letter] ++
                (deduplicateLater rest).erase letter ++ suffix)
              (stem ++ [letter] ++
                (deduplicateLater rest).erase letter ++ suffix) := by
          simpa [List.append_assoc] using
            listDerivesContractAdjacentAfterSeen
              stem ((deduplicateLater rest).erase letter ++ suffix)
              letter (sourceSeen letter (List.Mem.head rest))
        have restoreForward :=
          listDerivesPermuteAfterSeen stem suffix
            (by
              intro tested member
              exact sourceSeen tested (List.Mem.tail letter <|
                (deduplicateLater_mem_iff tested rest).mp member))
            (List.perm_cons_erase retained)
        have restore :
            ListDerives
              (stem ++ [letter] ++
                (deduplicateLater rest).erase letter ++ suffix)
              (stem ++ deduplicateLater rest ++ suffix) := by
          simpa [List.append_assoc] using restoreForward.symm
        rw [deduplicateLater, if_pos present]
        simpa [List.append_assoc] using
          recurseShape.trans (expose.trans (contract.trans restore))
      · rw [deduplicateLater, if_neg present]
        simpa [List.append_assoc] using recurseShape

/-- Behind a stem containing every displayed letter, multiplicities and
order are immaterial; only support remains. -/
theorem listDerivesOfSameSupportAfterSeen
    (stem suffix left right : List Nat)
    (leftSeen : ∀ letter, letter ∈ left → letter ∈ stem)
    (rightSeen : ∀ letter, letter ∈ right → letter ∈ stem)
    (sameSupport : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    ListDerives (stem ++ left ++ suffix)
      (stem ++ right ++ suffix) := by
  have leftReduction :=
    listDerivesDeduplicateLater suffix stem left leftSeen
  have rightReduction :=
    listDerivesDeduplicateLater suffix stem right rightSeen
  have reducedSupport :
      ∀ letter,
        letter ∈ deduplicateLater left ↔
          letter ∈ deduplicateLater right := by
    intro letter
    rw [deduplicateLater_mem_iff, deduplicateLater_mem_iff,
      sameSupport]
  have permutation :
      (deduplicateLater left).Perm (deduplicateLater right) :=
    perm_of_nodup_mem_iff
      (deduplicateLater_nodup left)
      (deduplicateLater_nodup right) reducedSupport
  have reducedSeen :
      ∀ letter, letter ∈ deduplicateLater left → letter ∈ stem := by
    intro letter member
    exact leftSeen letter <|
      (deduplicateLater_mem_iff letter left).mp member
  exact leftReduction.trans <|
    (listDerivesPermuteAfterSeen stem suffix reducedSeen permutation).trans
      rightReduction.symm

/-- Lee--Li Lemma 15.2(i), Case 1: if the final first-occurrence gap already
contains every letter of the stem, the word derives to the square of that
stem. -/
theorem listDerivesSquareOfFullFinalGap
    (stem finalGap : List Nat)
    (finalSeen :
      ∀ letter, letter ∈ finalGap → letter ∈ stem)
    (fullSupport :
      ∀ letter, letter ∈ finalGap ↔ letter ∈ stem) :
    ListDerives (stem ++ finalGap) (stem ++ stem) := by
  simpa [List.append_assoc] using
    listDerivesOfSameSupportAfterSeen stem [] finalGap stem
      finalSeen (by simp) fullSupport

/-! ## Appending one missing final-gap letter -/

private theorem listDerivesSquareReturn
    (selected tailHead : Nat) (tailRest : List Nat) :
    ListDerives
      ([selected, selected] ++
        (tailHead :: tailRest) ++ (tailHead :: tailRest))
      ([selected, selected] ++
        (tailHead :: tailRest) ++ (tailHead :: tailRest) ++ [selected]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesSquareReturnExpansion
          (Word.singleton selected)
          (listWordOfCons tailHead tailRest)))

/-- Append a selected letter absent from the final gap. The split is at its
last stem occurrence. Every letter to its right must already occur in the
final gap, and the selected letter must also have an earlier stem occurrence.
This is the constructive Case 2 move in Lee--Li Lemma 15.2(i). -/
theorem listDerivesAppendMissingFinalGapLetter
    (beforeStem tail finalGap : List Nat) (selected : Nat)
    (selectedEarlier : selected ∈ beforeStem)
    (selectedNotTail : selected ∉ tail)
    (selectedNotFinal : selected ∉ finalGap)
    (tailInFinal : ∀ letter, letter ∈ tail → letter ∈ finalGap)
    (finalSeen :
      ∀ letter, letter ∈ finalGap →
        letter ∈ beforeStem ++ [selected] ++ tail) :
    ListDerives
      (beforeStem ++ [selected] ++ tail ++ finalGap)
      (beforeStem ++ [selected] ++ tail ++ finalGap ++ [selected]) := by
  cases tail with
  | nil =>
      have duplicate :=
        (listDerivesContractAdjacentAfterSeen
          beforeStem finalGap selected selectedEarlier).symm
      have finalSeenShort :
          ∀ letter, letter ∈ finalGap →
            letter ∈ beforeStem ++ [selected] := by
        intro letter member
        simpa using finalSeen letter member
      have move :=
        listDerivesPermuteAfterSeen
          (beforeStem ++ [selected]) []
          (source := [selected] ++ finalGap)
          (target := finalGap ++ [selected])
          (by
            intro letter member
            rcases List.mem_append.mp member with inSelected | inFinal
            · exact List.mem_append.mpr <| Or.inr inSelected
            · exact finalSeenShort letter inFinal)
          (perm_append_comm [selected] finalGap)
      have moveShape :
          ListDerives
            (beforeStem ++ [selected, selected] ++ finalGap)
            (beforeStem ++ [selected] ++ finalGap ++ [selected]) := by
        simpa [List.append_assoc] using move
      simpa [List.append_assoc] using duplicate.trans moveShape
  | cons tailHead tailRest =>
      let tail := tailHead :: tailRest
      let stem := beforeStem ++ [selected] ++ tail
      have finalSeenStem :
          ∀ letter, letter ∈ finalGap → letter ∈ stem := by
        intro letter member
        exact finalSeen letter member
      have enrichedSeen :
          ∀ letter,
            letter ∈ tail ++ tail ++ finalGap → letter ∈ stem := by
        intro letter member
        rcases List.mem_append.mp member with inDouble | inFinal
        · rcases List.mem_append.mp inDouble with inFirst | inSecond
          · exact List.mem_append.mpr <| Or.inr inFirst
          · exact List.mem_append.mpr <| Or.inr inSecond
        · exact finalSeenStem letter inFinal
      have enrichedSupport :
          ∀ letter,
            letter ∈ finalGap ↔ letter ∈ tail ++ tail ++ finalGap := by
        intro letter
        constructor
        · intro member
          exact List.mem_append.mpr <| Or.inr member
        · intro member
          rcases List.mem_append.mp member with inDouble | inFinal
          · rcases List.mem_append.mp inDouble with inFirst | inSecond
            · exact tailInFinal letter inFirst
            · exact tailInFinal letter inSecond
          · exact inFinal
      have enrich :
          ListDerives (stem ++ finalGap)
            (stem ++ (tail ++ tail ++ finalGap)) := by
        simpa [List.append_assoc] using
          listDerivesOfSameSupportAfterSeen stem []
            finalGap (tail ++ tail ++ finalGap)
            finalSeenStem enrichedSeen enrichedSupport
      have duplicate :
          ListDerives
            (beforeStem ++ [selected] ++
              (tail ++ tail ++ tail ++ finalGap))
            (beforeStem ++ [selected, selected] ++
              (tail ++ tail ++ tail ++ finalGap)) :=
        (listDerivesContractAdjacentAfterSeen beforeStem
          (tail ++ tail ++ tail ++ finalGap)
          selected selectedEarlier).symm
      have returnStep :
          ListDerives
            (beforeStem ++ [selected, selected] ++
              (tail ++ tail ++ tail ++ finalGap))
            (beforeStem ++ [selected, selected] ++
              (tail ++ tail ++ [selected] ++ tail ++ finalGap)) := by
        simpa [tail, List.append_assoc] using
          S5_107.ListDerives.context beforeStem (tail ++ finalGap)
            (listDerivesSquareReturn selected tailHead tailRest)
      let returnStem :=
        beforeStem ++ [selected, selected] ++ tail ++ tail
      have stemInReturnStem :
          ∀ letter, letter ∈ stem → letter ∈ returnStem := by
        intro letter member
        simp only [stem, returnStem, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at member ⊢
        rcases member with (inBefore | atSelected) | inTail
        · exact Or.inl <| Or.inl <| Or.inl inBefore
        · exact Or.inl <| Or.inl <| Or.inr <| Or.inl atSelected
        · exact Or.inl <| Or.inr inTail
      have returnStemContains :
          ∀ letter,
            letter ∈ [selected] ++ tail ++ finalGap →
              letter ∈ returnStem := by
        intro letter member
        rcases List.mem_append.mp member with inFirst | inFinal
        · rcases List.mem_append.mp inFirst with inSelected | inTail
          · have atSelected : letter = selected := by
              simpa using inSelected
            subst letter
            exact stemInReturnStem selected (by simp [stem])
          · exact stemInReturnStem letter (by simp [stem, inTail])
        · exact stemInReturnStem letter (finalSeenStem letter inFinal)
      have moveReturn :
          ListDerives
            (returnStem ++ ([selected] ++ tail ++ finalGap))
            (returnStem ++ (tail ++ finalGap ++ [selected])) := by
        simpa [List.append_assoc] using
          listDerivesPermuteAfterSeen returnStem []
            returnStemContains
            (perm_append_comm [selected] (tail ++ finalGap))
      have contract :
          ListDerives
            (beforeStem ++ [selected, selected] ++
              (tail ++ tail ++ tail ++ finalGap ++ [selected]))
            (beforeStem ++ [selected] ++
              (tail ++ tail ++ tail ++ finalGap ++ [selected])) :=
        listDerivesContractAdjacentAfterSeen beforeStem
          (tail ++ tail ++ tail ++ finalGap ++ [selected])
          selected selectedEarlier
      have reducedSeen :
          ∀ letter,
            letter ∈ tail ++ tail ++ finalGap → letter ∈ stem :=
        enrichedSeen
      have reduce :
          ListDerives
            (stem ++ (tail ++ tail ++ finalGap) ++ [selected])
            (stem ++ finalGap ++ [selected]) :=
        listDerivesOfSameSupportAfterSeen stem [selected]
          (tail ++ tail ++ finalGap) finalGap
          reducedSeen finalSeenStem (fun letter => (enrichedSupport letter).symm)
      have enrichShape :
          ListDerives
            (beforeStem ++ [selected] ++ tail ++ finalGap)
            (beforeStem ++ [selected] ++
              (tail ++ tail ++ tail ++ finalGap)) := by
        simpa [stem, List.append_assoc] using enrich
      have moveReturnShape :
          ListDerives
            (beforeStem ++ [selected, selected] ++
              (tail ++ tail ++ [selected] ++ tail ++ finalGap))
            (beforeStem ++ [selected, selected] ++
              (tail ++ tail ++ tail ++ finalGap ++ [selected])) := by
        simpa [returnStem, List.append_assoc] using moveReturn
      have reduceShape :
          ListDerives
            (beforeStem ++ [selected] ++
              (tail ++ tail ++ tail ++ finalGap ++ [selected]))
            (beforeStem ++ [selected] ++ tail ++
              finalGap ++ [selected]) := by
        simpa [stem, List.append_assoc] using reduce
      simpa [tail, List.append_assoc] using
        enrichShape.trans <| duplicate.trans <|
          returnStep.trans <| moveReturnShape.trans <|
            contract.trans reduceShape

/-! A finite completion plan packages repeated applications of the previous
theorem. It is a derivational object, not a completeness premise. -/

inductive FinalGapCompletionPlan (stem : List Nat) :
    List Nat → List Nat → Prop
  | done (finalGap : List Nat) :
      FinalGapCompletionPlan stem finalGap finalGap
  | append (beforeStem tail finalGap completed : List Nat) (selected : Nat)
      (stemShape : stem = beforeStem ++ [selected] ++ tail)
      (selectedEarlier : selected ∈ beforeStem)
      (selectedNotTail : selected ∉ tail)
      (selectedNotFinal : selected ∉ finalGap)
      (tailInFinal :
        ∀ letter, letter ∈ tail → letter ∈ finalGap)
      (finalSeen :
        ∀ letter, letter ∈ finalGap → letter ∈ stem)
      (next :
        FinalGapCompletionPlan stem
          (finalGap ++ [selected]) completed) :
      FinalGapCompletionPlan stem finalGap completed

theorem FinalGapCompletionPlan.derives
    {stem initial completed : List Nat}
    (plan : FinalGapCompletionPlan stem initial completed) :
    ListDerives (stem ++ initial) (stem ++ completed) := by
  induction plan with
  | done =>
      exact S5_107.ListDerives.refl _
  | append beforeStem tail finalGap completed selected stemShape
      selectedEarlier selectedNotTail selectedNotFinal tailInFinal
      finalSeen next induction =>
      have appendStep :=
        listDerivesAppendMissingFinalGapLetter
          beforeStem tail finalGap selected selectedEarlier selectedNotTail
          selectedNotFinal tailInFinal (by
            intro letter member
            simpa [stemShape] using finalSeen letter member)
      rw [stemShape] at induction ⊢
      have inductionShape :
          ListDerives
            (beforeStem ++ [selected] ++ tail ++ finalGap ++ [selected])
            (beforeStem ++ [selected] ++ tail ++ completed) := by
        simpa [List.append_assoc] using induction
      simpa [List.append_assoc] using appendStep.trans inductionShape

private def missingSupport
    (stem finalGap : List Nat) : List Nat :=
  (deduplicateLater stem).filter
    (fun letter => decide (letter ∉ finalGap))

private theorem missingSupport_mem_iff
    (stem finalGap : List Nat) (selected : Nat) :
    selected ∈ missingSupport stem finalGap ↔
      selected ∈ stem ∧ selected ∉ finalGap := by
  simp [missingSupport, deduplicateLater_mem_iff]

private theorem missingSupport_append_selected
    (stem finalGap : List Nat) (selected : Nat)
    : missingSupport stem (finalGap ++ [selected]) =
      (missingSupport stem finalGap).filter
        (fun letter => decide (letter ≠ selected)) := by
  unfold missingSupport
  rw [List.filter_filter]
  apply List.filter_congr
  intro letter _
  by_cases inFinal : letter ∈ finalGap <;>
    by_cases atSelected : letter = selected <;>
      simp [inFinal, atSelected]

private theorem filter_ne_length_lt_of_mem
    (selected : Nat) {letters : List Nat}
    (member : selected ∈ letters) :
    (letters.filter
      (fun letter => decide (letter ≠ selected))).length <
        letters.length := by
  obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp member
  rw [shape, List.filter_append]
  have selfFalse : decide (selected ≠ selected) = false := by simp
  rw [List.filter_cons, selfFalse]
  simp only [Bool.false_eq_true, if_false]
  have beforeBound :
      (before.filter
        (fun letter => decide (letter ≠ selected))).length ≤
          before.length := List.filter_sublist.length_le
  have afterBound :
      (after.filter
        (fun letter => decide (letter ≠ selected))).length ≤
          after.length := List.filter_sublist.length_le
  simp only [List.length_append, List.length_cons]
  omega

/-- Split at the rightmost stem occurrence of a letter still absent from the
final gap. Consequently every letter in the remaining tail is already in the
final gap. -/
private theorem exists_rightmost_missing_split
    (stem finalGap : List Nat)
    (missing :
      ∃ letter, letter ∈ stem ∧ letter ∉ finalGap) :
    ∃ beforeStem selected tail,
      stem = beforeStem ++ [selected] ++ tail ∧
      selected ∉ finalGap ∧
      ∀ letter, letter ∈ tail → letter ∈ finalGap := by
  induction stem with
  | nil =>
      obtain ⟨letter, member, _⟩ := missing
      simp at member
  | cons head rest induction =>
      by_cases restMissing :
          ∃ letter, letter ∈ rest ∧ letter ∉ finalGap
      · obtain ⟨beforeStem, selected, tail, restShape,
            selectedNotFinal, tailInFinal⟩ := induction restMissing
        exact ⟨head :: beforeStem, selected, tail, by
          simp [restShape], selectedNotFinal, tailInFinal⟩
      · have restInFinal :
            ∀ letter, letter ∈ rest → letter ∈ finalGap := by
          intro letter member
          by_cases inFinal : letter ∈ finalGap
          · exact inFinal
          · exact False.elim <| restMissing ⟨letter, member, inFinal⟩
        have headNotFinal : head ∉ finalGap := by
          intro headInFinal
          obtain ⟨letter, member, absent⟩ := missing
          rcases List.mem_cons.mp member with atHead | inRest
          · subst letter
            exact absent headInFinal
          · exact absent (restInFinal letter inRest)
        exact ⟨[], head, rest, by simp, headNotFinal, restInFinal⟩

private theorem exists_missing_of_not_full
    (stem finalGap : List Nat)
    (notFull : ¬∀ letter, letter ∈ stem → letter ∈ finalGap) :
    ∃ letter, letter ∈ stem ∧ letter ∉ finalGap := by
  induction stem with
  | nil =>
      exact False.elim <| notFull (by simp)
  | cons head rest induction =>
      by_cases headInFinal : head ∈ finalGap
      · by_cases restFull : ∀ letter, letter ∈ rest → letter ∈ finalGap
        · exact False.elim <| notFull (by
            intro letter member
            rcases List.mem_cons.mp member with atHead | inRest
            · simpa [atHead] using headInFinal
            · exact restFull letter inRest)
        · obtain ⟨letter, member, absent⟩ := induction restFull
          exact ⟨letter, List.Mem.tail head member, absent⟩
      · exact ⟨head, List.Mem.head rest, headInFinal⟩

private theorem completionPlan_exists_aux
    (stem : List Nat) :
    ∀ bound finalGap,
      (missingSupport stem finalGap).length = bound →
      (∀ letter, letter ∈ finalGap → letter ∈ stem) →
      (∀ letter, letter ∈ stem →
        2 ≤ (stem ++ finalGap).count letter) →
      ∃ completed,
        FinalGapCompletionPlan stem finalGap completed ∧
        ∀ letter, letter ∈ completed ↔ letter ∈ stem := by
  intro bound
  induction bound using Nat.strongRecOn
  rename_i current induction
  intro finalGap cardEq finalSeen repeated
  by_cases fullSupport :
      ∀ letter, letter ∈ stem → letter ∈ finalGap
  · exact ⟨finalGap, FinalGapCompletionPlan.done finalGap, by
      intro letter
      exact ⟨finalSeen letter, fullSupport letter⟩⟩
  · have missing :
        ∃ letter, letter ∈ stem ∧ letter ∉ finalGap :=
      exists_missing_of_not_full stem finalGap fullSupport
    obtain ⟨beforeStem, selected, tail, stemShape,
        selectedNotFinal, tailInFinal⟩ :=
      exists_rightmost_missing_split stem finalGap missing
    have selectedInStem : selected ∈ stem := by
      rw [stemShape]
      simp
    have selectedNotTail : selected ∉ tail := by
      intro inTail
      exact selectedNotFinal (tailInFinal selected inTail)
    have selectedEarlier : selected ∈ beforeStem := by
      have bound := repeated selected selectedInStem
      have tailCount : tail.count selected = 0 :=
        List.count_eq_zero.mpr selectedNotTail
      have finalCount : finalGap.count selected = 0 :=
        List.count_eq_zero.mpr selectedNotFinal
      rw [stemShape] at bound
      simp only [List.count_append, List.count_cons, List.count_nil,
        tailCount, finalCount, beq_self_eq_true, if_true] at bound
      exact List.count_pos_iff.mp (by omega)
    have nextFinalSeen :
        ∀ letter, letter ∈ finalGap ++ [selected] →
          letter ∈ stem := by
      intro letter member
      rcases List.mem_append.mp member with inFinal | atSelected
      · exact finalSeen letter inFinal
      · have equal : letter = selected := by simpa using atSelected
        simpa [equal] using selectedInStem
    have nextRepeated :
        ∀ letter, letter ∈ stem →
          2 ≤ (stem ++ (finalGap ++ [selected])).count letter := by
      intro letter inStem
      have old := repeated letter inStem
      simp only [List.count_append] at old ⊢
      omega
    have selectedMissing :
        selected ∈ missingSupport stem finalGap := by
      exact (missingSupport_mem_iff stem finalGap selected).mpr
        ⟨selectedInStem, selectedNotFinal⟩
    have decrease :
        (missingSupport stem (finalGap ++ [selected])).length < current := by
      rw [missingSupport_append_selected stem finalGap selected,
        ← cardEq]
      exact filter_ne_length_lt_of_mem selected selectedMissing
    obtain ⟨completed, next, completedSupport⟩ :=
      induction _ decrease (finalGap ++ [selected]) rfl
        nextFinalSeen nextRepeated
    exact ⟨completed,
      FinalGapCompletionPlan.append beforeStem tail finalGap completed selected
        stemShape selectedEarlier selectedNotTail selectedNotFinal
        tailInFinal finalSeen next,
      completedSupport⟩

/-- Every repeated stem can be completed to a final gap with exactly the same
support, together with the explicit sequence of Case 2 derivations. -/
theorem finalGapCompletionPlan_exists
    (stem finalGap : List Nat)
    (finalSeen :
      ∀ letter, letter ∈ finalGap → letter ∈ stem)
    (repeated :
      ∀ letter, letter ∈ stem →
        2 ≤ (stem ++ finalGap).count letter) :
    ∃ completed,
      FinalGapCompletionPlan stem finalGap completed ∧
      ∀ letter, letter ∈ completed ↔ letter ∈ stem :=
  completionPlan_exists_aux stem
    (missingSupport stem finalGap).length finalGap rfl finalSeen repeated

/-- Lee--Li Lemma 15.2(i) in list form, including both completion cases. -/
theorem listDerivesSquareOfRepeatedStem
    (stem finalGap : List Nat)
    (finalSeen :
      ∀ letter, letter ∈ finalGap → letter ∈ stem)
    (repeated :
      ∀ letter, letter ∈ stem →
        2 ≤ (stem ++ finalGap).count letter) :
    ListDerives (stem ++ finalGap) (stem ++ stem) := by
  obtain ⟨completed, plan, completedSupport⟩ :=
    finalGapCompletionPlan_exists stem finalGap finalSeen repeated
  exact plan.derives.trans <|
    listDerivesSquareOfFullFinalGap stem completed
      (fun letter member => (completedSupport letter).mp member)
      completedSupport

/-- A word in which every displayed letter occurs at least twice derives to
its square. -/
theorem listDerivesSquareOfSimpleFree
    (letters : List Nat)
    (repeated :
      ∀ letter, letter ∈ letters → 2 ≤ letters.count letter) :
    ListDerives letters (letters ++ letters) := by
  simpa using
    listDerivesSquareOfRepeatedStem letters [] (by simp) (by
      intro letter member
      simpa using repeated letter member)

/-! ## Deleting an unprotected later occurrence -/

/-- Lee--Li Lemma 15.2(ii). The factor between the displayed second and third
selected occurrences is nonempty and has no simple letter. Outer contexts and
the block between the first two selected occurrences are arbitrary. -/
theorem listDerivesDeleteAfterSimpleFree
    (before between after : List Nat)
    (selected factorHead : Nat) (factorTail : List Nat)
    (repeated :
      ∀ letter, letter ∈ factorHead :: factorTail →
        2 ≤ (factorHead :: factorTail).count letter) :
    ListDerives
      (before ++ [selected] ++ between ++ [selected] ++
        (factorHead :: factorTail) ++ [selected] ++ after)
      (before ++ [selected] ++ between ++ [selected] ++
        (factorHead :: factorTail) ++ after) := by
  let factor := factorHead :: factorTail
  let seen := [selected] ++ between
  have square : ListDerives factor (factor ++ factor) :=
    listDerivesSquareOfSimpleFree factor (by
      intro letter member
      exact repeated letter member)
  have squareInContext :
      ListDerives
        (seen ++ [selected] ++ factor ++ [selected])
        (seen ++ [selected] ++ (factor ++ factor) ++ [selected]) := by
    simpa [List.append_assoc] using
      S5_107.ListDerives.context
        (seen ++ [selected]) [selected] square
  have selectedSeen : selected ∈ seen := by
    simp [seen]
  have insertAdjacent :
      ListDerives
        (seen ++ [selected] ++ (factor ++ factor) ++ [selected])
        (seen ++ [selected, selected] ++
          (factor ++ factor) ++ [selected]) := by
    simpa [List.append_assoc] using
      (listDerivesContractAdjacentAfterSeen seen
        (factor ++ factor ++ [selected]) selected selectedSeen).symm
  have removeReturn :
      ListDerives
        (seen ++ [selected, selected] ++
          (factor ++ factor) ++ [selected])
        (seen ++ [selected, selected] ++ (factor ++ factor)) := by
    simpa [factor, List.append_assoc] using
      S5_107.ListDerives.context seen []
        (listDerivesSquareReturn selected factorHead factorTail).symm
  have contractAdjacent :
      ListDerives
        (seen ++ [selected, selected] ++ (factor ++ factor))
        (seen ++ [selected] ++ (factor ++ factor)) := by
    simpa [List.append_assoc] using
      listDerivesContractAdjacentAfterSeen seen
        (factor ++ factor) selected selectedSeen
  have unsquareInContext :
      ListDerives
        (seen ++ [selected] ++ (factor ++ factor))
        (seen ++ [selected] ++ factor) := by
    simpa [List.append_assoc] using
      S5_107.ListDerives.context
        (seen ++ [selected]) [] square.symm
  have core := squareInContext.trans <| insertAdjacent.trans <|
    removeReturn.trans <| contractAdjacent.trans unsquareInContext
  simpa [seen, factor, List.append_assoc] using
    S5_107.ListDerives.context before after core

/-! ## Deterministic first-occurrence-block normalization -/

private def sortedDistinctExcept
    (excluded : Nat) (letters : List Nat) : List Nat :=
  ((deduplicateLater letters).filter
      (fun letter => decide (letter ≠ excluded))).mergeSort
    (fun left right : Nat => decide (left ≤ right))

/-- Gather the marker's possible later copy first, then list every other
displayed letter once in ascending order. -/
def canonicalSeconds (marker : Nat) (seconds : List Nat) : List Nat :=
  (if marker ∈ seconds then [marker] else []) ++
    sortedDistinctExcept marker seconds

private theorem sortedDistinctExcept_mem_iff
    (excluded tested : Nat) (letters : List Nat) :
    tested ∈ sortedDistinctExcept excluded letters ↔
      tested ∈ letters ∧ tested ≠ excluded := by
  simp only [sortedDistinctExcept, List.mem_mergeSort, List.mem_filter,
    decide_eq_true_eq, deduplicateLater_mem_iff]

private theorem sortedDistinctExcept_nodup
    (excluded : Nat) (letters : List Nat) :
    (sortedDistinctExcept excluded letters).Nodup := by
  unfold sortedDistinctExcept
  apply (List.mergeSort_perm _ _).nodup_iff.mpr
  exact (deduplicateLater_nodup letters).filter _

private theorem sortedDistinctExcept_pairwise
    (excluded : Nat) (letters : List Nat) :
    (sortedDistinctExcept excluded letters).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right leftMiddle middleRight
    exact decide_eq_true <|
      Nat.le_trans
        (of_decide_eq_true leftMiddle)
        (of_decide_eq_true middleRight)
  have total :
      ∀ left right : Nat,
        (decide (left ≤ right) || decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with leftRight | rightLeft
    · simp [leftRight]
    · simp [rightLeft]
  exact
    (List.pairwise_mergeSort transitive total
      ((deduplicateLater letters).filter
        (fun letter => decide (letter ≠ excluded)))).imp
      (fun relation => of_decide_eq_true relation)

theorem canonicalSeconds_mem_iff
    (marker tested : Nat) (seconds : List Nat) :
    tested ∈ canonicalSeconds marker seconds ↔ tested ∈ seconds := by
  by_cases markerPresent : marker ∈ seconds
  · by_cases atMarker : tested = marker
    · subst tested
      simp [canonicalSeconds, markerPresent]
    · simp [canonicalSeconds, markerPresent,
        sortedDistinctExcept_mem_iff, atMarker]
  · by_cases atMarker : tested = marker
    · subst tested
      simp [canonicalSeconds, markerPresent,
        sortedDistinctExcept_mem_iff]
    · simp [canonicalSeconds, markerPresent,
        sortedDistinctExcept_mem_iff, atMarker]

theorem canonicalSeconds_nodup
    (marker : Nat) (seconds : List Nat) :
    (canonicalSeconds marker seconds).Nodup := by
  by_cases markerPresent : marker ∈ seconds
  · have markerAbsent :
        marker ∉ sortedDistinctExcept marker seconds := by
      simp [sortedDistinctExcept_mem_iff]
    simpa [canonicalSeconds, markerPresent] using
      List.nodup_cons.mpr
        ⟨markerAbsent, sortedDistinctExcept_nodup marker seconds⟩
  · simpa [canonicalSeconds, markerPresent] using
      sortedDistinctExcept_nodup marker seconds

theorem canonicalSeconds_eq_of_mem_iff
    (marker : Nat) {left right : List Nat}
    (sameSupport :
      ∀ letter, letter ∈ left ↔ letter ∈ right) :
    canonicalSeconds marker left = canonicalSeconds marker right := by
  have markerSame : marker ∈ left ↔ marker ∈ right :=
    sameSupport marker
  have residualMembership :
      ∀ tested,
        tested ∈ sortedDistinctExcept marker left ↔
          tested ∈ sortedDistinctExcept marker right := by
    intro tested
    rw [sortedDistinctExcept_mem_iff, sortedDistinctExcept_mem_iff,
      sameSupport tested]
  have residualPermutation :
      (sortedDistinctExcept marker left).Perm
        (sortedDistinctExcept marker right) := by
    rw [List.perm_iff_count]
    intro tested
    rw [(sortedDistinctExcept_nodup marker left).count,
      (sortedDistinctExcept_nodup marker right).count]
    simpa only [residualMembership tested]
  have residualEq :
      sortedDistinctExcept marker left =
        sortedDistinctExcept marker right :=
    List.Perm.eq_of_pairwise
      (fun _ _ _ _ leftRight rightLeft =>
        Nat.le_antisymm leftRight rightLeft)
      (sortedDistinctExcept_pairwise marker left)
      (sortedDistinctExcept_pairwise marker right)
      residualPermutation
  by_cases markerPresent : marker ∈ left
  · have rightPresent := markerSame.mp markerPresent
    simp [canonicalSeconds, markerPresent, rightPresent, residualEq]
  · have rightAbsent : marker ∉ right := by
      intro rightPresent
      exact markerPresent (markerSame.mpr rightPresent)
    simp [canonicalSeconds, markerPresent, rightAbsent, residualEq]

def normalizeGapBlock
    (block : FirstOccurrenceGapBlock) : FirstOccurrenceGapBlock where
  marker := block.marker
  seconds := canonicalSeconds block.marker block.seconds

def normalizeGapBlocks
    (blocks : List FirstOccurrenceGapBlock) :
    List FirstOccurrenceGapBlock :=
  blocks.map normalizeGapBlock

@[simp]
theorem normalizeGapBlock_marker (block : FirstOccurrenceGapBlock) :
    (normalizeGapBlock block).marker = block.marker := rfl

@[simp]
theorem normalizeGapBlock_seconds (block : FirstOccurrenceGapBlock) :
    (normalizeGapBlock block).seconds =
      canonicalSeconds block.marker block.seconds := rfl

/-- Every parsed block derives to the deterministic exponent/support form.
Only the already-seen invariant of the S5_870 parser is reused. -/
theorem listDerivesNormalizeGapBlocks
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks)
    (stem : List Nat)
    (seenInStem :
      ∀ letter, letter ∈ seen → letter ∈ stem) :
    ListDerives
      (stem ++ renderGapBlocks blocks)
      (stem ++ renderGapBlocks (normalizeGapBlocks blocks)) := by
  induction formed generalizing stem with
  | nil =>
      simpa only [S5_870.renderGapBlocks, normalizeGapBlocks,
        List.map_nil, List.append_nil] using
          S5_107.ListDerives.refl (basis := basis) stem
  | cons seen block rest markerFresh secondsSeen tail induction =>
      let nextStem := stem ++ [block.marker]
      let normalizedSeconds :=
        canonicalSeconds block.marker block.seconds
      have sourceSeen :
          ∀ letter, letter ∈ block.seconds →
            letter ∈ nextStem := by
        intro letter member
        rcases List.mem_cons.mp (secondsSeen letter member) with
          atMarker | inSeen
        · subst letter
          simp [nextStem]
        · exact List.mem_append.mpr <| Or.inl <|
            seenInStem letter inSeen
      have targetSeen :
          ∀ letter, letter ∈ normalizedSeconds →
            letter ∈ nextStem := by
        intro letter member
        exact sourceSeen letter <|
          (canonicalSeconds_mem_iff block.marker letter block.seconds).mp member
      have normalizeCurrent :
          ListDerives
            (nextStem ++ block.seconds ++ renderGapBlocks rest)
            (nextStem ++ normalizedSeconds ++ renderGapBlocks rest) :=
        listDerivesOfSameSupportAfterSeen nextStem
          (renderGapBlocks rest) block.seconds normalizedSeconds
          sourceSeen targetSeen
          (fun letter =>
            (canonicalSeconds_mem_iff
              block.marker letter block.seconds).symm)
      have nextSeenInStem :
          ∀ letter, letter ∈ block.marker :: seen →
            letter ∈ nextStem ++ normalizedSeconds := by
        intro letter member
        rcases List.mem_cons.mp member with atMarker | inSeen
        · subst letter
          exact List.mem_append.mpr <| Or.inl <| by simp [nextStem]
        · exact List.mem_append.mpr <| Or.inl <|
            List.mem_append.mpr <| Or.inl <|
              seenInStem letter inSeen
      have normalizeRest :=
        induction (nextStem ++ normalizedSeconds) nextSeenInStem
      simpa [nextStem, normalizedSeconds, renderGapBlocks,
        normalizeGapBlocks, List.append_assoc] using
          normalizeCurrent.trans normalizeRest

def blockNormalList (letters : List Nat) : List Nat :=
  renderGapBlocks (normalizeGapBlocks (gapBlocksList letters))

theorem listDerivesBlockNormal (letters : List Nat) :
    ListDerives letters (blockNormalList letters) := by
  have normalized :=
    listDerivesNormalizeGapBlocks
      (S5_870.gapBlocksList_wellFormed letters) [] (by simp)
  simpa [blockNormalList, S5_870.render_gapBlocksList] using normalized

/-! ## Condition-(IV) protected-occurrence pruning -/

theorem refinedGapSignatureList_eq_of_listDerives
    {left right : List Nat}
    (derivation : ListDerives left right) :
    refinedGapSignatureList left = refinedGapSignatureList right := by
  cases derivation with
  | empty => rfl
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      simpa using refinedGapSignature_eq_of_derives wordDerivation

private theorem normalizeGapBlocks_wellFormed
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks) :
    GapBlocksWellFormed seen (normalizeGapBlocks blocks) := by
  induction formed with
  | nil =>
      simpa only [normalizeGapBlocks, List.map_nil] using
        S5_870.GapBlocksWellFormed.nil _
  | cons seen block rest markerFresh secondsSeen tail induction =>
      exact S5_870.GapBlocksWellFormed.cons seen (normalizeGapBlock block)
        (normalizeGapBlocks rest) markerFresh (by
          intro letter member
          exact secondsSeen letter <|
            (canonicalSeconds_mem_iff
              block.marker letter block.seconds).mp member)
        induction

private theorem normalizeGapBlock_idempotent
    (block : FirstOccurrenceGapBlock) :
    normalizeGapBlock (normalizeGapBlock block) = normalizeGapBlock block := by
  cases block with
  | mk marker seconds =>
      have secondsEq :
          canonicalSeconds marker (canonicalSeconds marker seconds) =
            canonicalSeconds marker seconds :=
        canonicalSeconds_eq_of_mem_iff marker (by
          intro letter
          exact canonicalSeconds_mem_iff marker letter seconds)
      exact congrArg
        (fun normalized =>
          S5_870.FirstOccurrenceGapBlock.mk marker normalized)
        secondsEq

private theorem normalizeGapBlocks_idempotent
    (blocks : List FirstOccurrenceGapBlock) :
    normalizeGapBlocks (normalizeGapBlocks blocks) =
      normalizeGapBlocks blocks := by
  induction blocks with
  | nil => rfl
  | cons block rest induction =>
      simp [normalizeGapBlocks, normalizeGapBlock_idempotent, induction]

private def doubleGapBlock
    (block : FirstOccurrenceGapBlock) : FirstOccurrenceGapBlock where
  marker := block.marker
  seconds := block.seconds ++ block.seconds

private def doubleGapBlocks
    (blocks : List FirstOccurrenceGapBlock) :
    List FirstOccurrenceGapBlock :=
  blocks.map doubleGapBlock

private theorem listDerivesDoubleGapBlocks
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks)
    (stem suffix : List Nat)
    (seenInStem : ∀ letter, letter ∈ seen → letter ∈ stem) :
    ListDerives
      (stem ++ renderGapBlocks blocks ++ suffix)
      (stem ++ renderGapBlocks (doubleGapBlocks blocks) ++ suffix) := by
  induction formed generalizing stem with
  | nil =>
      simpa only [S5_870.renderGapBlocks, doubleGapBlocks,
        List.map_nil, List.append_nil] using
          S5_107.ListDerives.refl (basis := basis) (stem ++ suffix)
  | cons seen block rest markerFresh secondsSeen tail induction =>
      let nextStem := stem ++ [block.marker]
      let doubled := block.seconds ++ block.seconds
      have sourceSeen :
          ∀ letter, letter ∈ block.seconds → letter ∈ nextStem := by
        intro letter member
        rcases List.mem_cons.mp (secondsSeen letter member) with
          atMarker | inSeen
        · subst letter
          simp [nextStem]
        · exact List.mem_append.mpr <| Or.inl <| seenInStem letter inSeen
      have doubledSeen :
          ∀ letter, letter ∈ doubled → letter ∈ nextStem := by
        intro letter member
        rcases List.mem_append.mp member with first | second
        · exact sourceSeen letter first
        · exact sourceSeen letter second
      have doubleCurrent :
          ListDerives
            (nextStem ++ block.seconds ++ renderGapBlocks rest ++ suffix)
            (nextStem ++ doubled ++ renderGapBlocks rest ++ suffix) := by
        simpa [List.append_assoc] using
          listDerivesOfSameSupportAfterSeen nextStem
            (renderGapBlocks rest ++ suffix) block.seconds doubled
            sourceSeen doubledSeen (by simp [doubled])
      have nextSeenInStem :
          ∀ letter, letter ∈ block.marker :: seen →
            letter ∈ nextStem ++ doubled := by
        intro letter member
        rcases List.mem_cons.mp member with atMarker | inSeen
        · subst letter
          exact List.mem_append.mpr <| Or.inl <| by simp [nextStem]
        · exact List.mem_append.mpr <| Or.inl <|
            List.mem_append.mpr <| Or.inl <| seenInStem letter inSeen
      have doubleRest :
          ListDerives
            (nextStem ++ doubled ++ renderGapBlocks rest ++ suffix)
            (nextStem ++ doubled ++
              renderGapBlocks (doubleGapBlocks rest) ++ suffix) := by
        simpa [List.append_assoc] using
          induction (nextStem ++ doubled) nextSeenInStem
      simpa [nextStem, doubled, doubleGapBlocks, doubleGapBlock,
        S5_870.renderGapBlocks, List.append_assoc] using
          doubleCurrent.trans doubleRest

private theorem gapBlockMarkers_doubleGapBlocks
    (blocks : List FirstOccurrenceGapBlock) :
    S5_870.gapBlockMarkers (doubleGapBlocks blocks) =
      S5_870.gapBlockMarkers blocks := by
  induction blocks with
  | nil => rfl
  | cons block rest induction =>
      simp [doubleGapBlocks, doubleGapBlock,
        S5_870.gapBlockMarkers, induction]

private theorem count_gapBlockSeconds_doubleGapBlocks
    (tested : Nat) (blocks : List FirstOccurrenceGapBlock) :
    (S5_870.gapBlockSeconds (doubleGapBlocks blocks)).count tested =
      2 * (S5_870.gapBlockSeconds blocks).count tested := by
  induction blocks with
  | nil => simp [doubleGapBlocks, S5_870.gapBlockSeconds]
  | cons block rest induction =>
      change
        ((block.seconds ++ block.seconds) ++
          S5_870.gapBlockSeconds (doubleGapBlocks rest)).count tested =
        2 * (block.seconds ++
          S5_870.gapBlockSeconds rest).count tested
      rw [List.count_append, List.count_append, List.count_append,
        induction]
      omega

private theorem count_render_doubleGapBlocks
    (tested : Nat) (blocks : List FirstOccurrenceGapBlock) :
    (S5_870.renderGapBlocks (doubleGapBlocks blocks)).count tested =
      (S5_870.gapBlockMarkers blocks).count tested +
        2 * (S5_870.gapBlockSeconds blocks).count tested := by
  rw [S5_870.count_renderGapBlocks, gapBlockMarkers_doubleGapBlocks,
    count_gapBlockSeconds_doubleGapBlocks]

private theorem takeSeen_renderGapBlocks_gapBlocksAux
    (stem factor : List Nat) :
    S5_870.takeSeen stem factor ++
        S5_870.renderGapBlocks
          (S5_870.gapBlocksAux stem (S5_870.dropSeen stem factor)) =
      factor := by
  calc
    S5_870.takeSeen stem factor ++
        S5_870.renderGapBlocks
          (S5_870.gapBlocksAux stem (S5_870.dropSeen stem factor)) =
        S5_870.takeSeen stem factor ++ S5_870.dropSeen stem factor := by
      exact congrArg (S5_870.takeSeen stem factor ++ ·)
        (S5_870.render_gapBlocksAux stem (S5_870.dropSeen stem factor))
    _ = factor := S5_870.takeSeen_append_dropSeen stem factor

private def expandedFactor (stem factor : List Nat) : List Nat :=
  let initial := S5_870.takeSeen stem factor
  let blocks := S5_870.gapBlocksAux stem (S5_870.dropSeen stem factor)
  initial ++ initial ++ renderGapBlocks (doubleGapBlocks blocks)

private theorem listDerivesExpandedFactor
    (stem factor suffix : List Nat) :
    ListDerives (stem ++ factor ++ suffix)
      (stem ++ expandedFactor stem factor ++ suffix) := by
  let initial := S5_870.takeSeen stem factor
  let blocks := S5_870.gapBlocksAux stem (S5_870.dropSeen stem factor)
  have formed : GapBlocksWellFormed stem blocks := by
    exact S5_870.gapBlocksAux_dropSeen_wellFormed stem factor
  have initialSeen :
      ∀ letter, letter ∈ initial → letter ∈ stem := by
    intro letter member
    exact S5_870.mem_takeSeen member
  have initialDoubledSeen :
      ∀ letter, letter ∈ initial ++ initial → letter ∈ stem := by
    intro letter member
    rcases List.mem_append.mp member with first | second
    · exact initialSeen letter first
    · exact initialSeen letter second
  have initialStep :
      ListDerives
        (stem ++ initial ++ renderGapBlocks blocks ++ suffix)
        (stem ++ (initial ++ initial) ++ renderGapBlocks blocks ++ suffix) := by
    simpa [List.append_assoc] using
      listDerivesOfSameSupportAfterSeen stem
        (renderGapBlocks blocks ++ suffix) initial (initial ++ initial)
        initialSeen initialDoubledSeen (by simp)
  have blockStep :
      ListDerives
        (stem ++ (initial ++ initial) ++ renderGapBlocks blocks ++ suffix)
        (stem ++ (initial ++ initial) ++
          renderGapBlocks (doubleGapBlocks blocks) ++ suffix) := by
    simpa [List.append_assoc] using
      listDerivesDoubleGapBlocks formed (stem ++ initial ++ initial) suffix
        (by
          intro letter member
          exact List.mem_append.mpr <| Or.inl <|
            List.mem_append.mpr <| Or.inl member)
  have factorShape : initial ++ renderGapBlocks blocks = factor := by
    exact takeSeen_renderGapBlocks_gapBlocksAux stem factor
  simpa [expandedFactor, initial, blocks, factorShape, List.append_assoc] using
    initialStep.trans blockStep

private theorem expandedFactor_count_ge_two
    (stem factor : List Nat)
    (noFreshSingleton :
      ∀ letter, letter ∈ factor → letter ∉ stem →
        factor.count letter ≠ 1) :
    ∀ letter, letter ∈ expandedFactor stem factor →
      2 ≤ (expandedFactor stem factor).count letter := by
  intro tested testedIn
  let initial := S5_870.takeSeen stem factor
  let blocks := S5_870.gapBlocksAux stem (S5_870.dropSeen stem factor)
  have formed : GapBlocksWellFormed stem blocks :=
    S5_870.gapBlocksAux_dropSeen_wellFormed stem factor
  have factorShape : initial ++ renderGapBlocks blocks = factor := by
    exact takeSeen_renderGapBlocks_gapBlocksAux stem factor
  have originalCount :
      factor.count tested = initial.count tested +
        (S5_870.gapBlockMarkers blocks).count tested +
          (S5_870.gapBlockSeconds blocks).count tested := by
    rw [← factorShape, List.count_append,
      S5_870.count_renderGapBlocks]
    omega
  have expandedCount :
      (expandedFactor stem factor).count tested =
        2 * initial.count tested +
          (S5_870.gapBlockMarkers blocks).count tested +
            2 * (S5_870.gapBlockSeconds blocks).count tested := by
    simp only [expandedFactor, initial, blocks, List.count_append,
      count_render_doubleGapBlocks]
    omega
  have expandedPositive :
      0 < (expandedFactor stem factor).count tested :=
    List.count_pos_iff.mpr testedIn
  have markersAtMostOne :
      (S5_870.gapBlockMarkers blocks).count tested ≤ 1 := by
    rw [formed.markersNodup.count]
    split <;> omega
  by_cases testedSeen : tested ∈ stem
  · have markerAbsent : tested ∉ S5_870.gapBlockMarkers blocks :=
      formed.markersAvoidSeen tested testedSeen
    have markerCountZero :
        (S5_870.gapBlockMarkers blocks).count tested = 0 :=
      List.count_eq_zero.mpr markerAbsent
    rw [markerCountZero] at expandedCount
    omega
  · have initialAbsent : tested ∉ initial := by
      intro member
      exact testedSeen (S5_870.mem_takeSeen member)
    have initialCountZero : initial.count tested = 0 :=
      List.count_eq_zero.mpr initialAbsent
    rw [initialCountZero] at originalCount expandedCount
    have originalPositive : 0 < factor.count tested := by
      rw [originalCount]
      omega
    have originalMember : tested ∈ factor :=
      List.count_pos_iff.mp originalPositive
    have notOne := noFreshSingleton tested originalMember testedSeen
    omega

private theorem expandedFactor_mem_iff
    (stem factor : List Nat) (tested : Nat) :
    tested ∈ expandedFactor stem factor ↔ tested ∈ factor := by
  let initial := S5_870.takeSeen stem factor
  let blocks := S5_870.gapBlocksAux stem (S5_870.dropSeen stem factor)
  have factorShape : initial ++ renderGapBlocks blocks = factor := by
    exact takeSeen_renderGapBlocks_gapBlocksAux stem factor
  have doubledSupport :
      tested ∈ renderGapBlocks (doubleGapBlocks blocks) ↔
        tested ∈ renderGapBlocks blocks := by
    constructor
    · intro member
      have positive :
          0 < (S5_870.renderGapBlocks
            (doubleGapBlocks blocks)).count tested :=
        List.count_pos_iff.mpr member
      rw [count_render_doubleGapBlocks] at positive
      apply List.count_pos_iff.mp
      rw [S5_870.count_renderGapBlocks]
      omega
    · intro member
      have positive :
          0 < (S5_870.renderGapBlocks blocks).count tested :=
        List.count_pos_iff.mpr member
      rw [S5_870.count_renderGapBlocks] at positive
      apply List.count_pos_iff.mp
      rw [count_render_doubleGapBlocks]
      omega
  change tested ∈ initial ++ initial ++
      renderGapBlocks (doubleGapBlocks blocks) ↔ tested ∈ factor
  rw [← factorShape]
  simp only [List.mem_append, doubledSupport]
  constructor
  · intro member
    rcases member with inInitial | inBlocks
    · rcases inInitial with first | second
      · exact Or.inl first
      · exact Or.inl second
    · exact Or.inr inBlocks
  · intro member
    rcases member with inInitial | inBlocks
    · exact Or.inl <| Or.inl inInitial
    · exact Or.inr inBlocks

private theorem exists_rightmost_split
    {value : Nat} {letters : List Nat}
    (member : value ∈ letters) :
    ∃ before after,
      letters = before ++ value :: after ∧ value ∉ after := by
  induction letters with
  | nil => simp at member
  | cons head tail induction =>
      by_cases inTail : value ∈ tail
      · obtain ⟨before, after, shape, notAfter⟩ := induction inTail
        exact ⟨head :: before, after, by simp [shape], notAfter⟩
      · have equal : value = head := by
          simpa [inTail] using member
        subst head
        exact ⟨[], tail, by simp, inTail⟩

/-! ### Canonical block conditions -/

def HasBlockProtector
    (blocks : List FirstOccurrenceGapBlock) : Prop :=
  ∃ protector,
    protector ∈ gapBlockMarkers blocks ∧
      protector ∉ gapBlockSeconds blocks

def HasUnprotectedGapOccurrence
    (blocks : List FirstOccurrenceGapBlock) : Prop :=
  ∃ beforeBlocks firstBlock middle lastBlock afterBlocks selected,
    blocks = beforeBlocks ++ [firstBlock] ++ middle ++
        [lastBlock] ++ afterBlocks ∧
      selected ∈ firstBlock.seconds ∧
      selected ∈ lastBlock.seconds ∧
      selected ∉ gapBlockSeconds middle ∧
      ¬HasBlockProtector (middle ++ [lastBlock])

def ProtectedGapOccurrences
    (blocks : List FirstOccurrenceGapBlock) : Prop :=
  ¬HasUnprotectedGapOccurrence blocks

def GapBlocksNormal
    (blocks : List FirstOccurrenceGapBlock) : Prop :=
  ∀ block, block ∈ blocks → normalizeGapBlock block = block

structure CanonicalGapBlocks
    (blocks : List FirstOccurrenceGapBlock) : Prop where
  wellFormed : GapBlocksWellFormed [] blocks
  normal : GapBlocksNormal blocks
  occurrencesProtected : ProtectedGapOccurrences blocks

def IsProtectedCanonicalList (letters : List Nat) : Prop :=
  ∃ blocks,
    letters = renderGapBlocks blocks ∧ CanonicalGapBlocks blocks

private theorem normalizeGapBlocks_normal
    (blocks : List FirstOccurrenceGapBlock) :
    GapBlocksNormal (normalizeGapBlocks blocks) := by
  intro block member
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
  exact normalizeGapBlock_idempotent source

private theorem renderGapBlocks_append
    (left right : List FirstOccurrenceGapBlock) :
    renderGapBlocks (left ++ right) =
      renderGapBlocks left ++ renderGapBlocks right := by
  induction left with
  | nil => rfl
  | cons block rest induction =>
      simp [S5_870.renderGapBlocks, induction, List.append_assoc]

private theorem gapBlockMarkers_append
    (left right : List FirstOccurrenceGapBlock) :
    gapBlockMarkers (left ++ right) =
      gapBlockMarkers left ++ gapBlockMarkers right := by
  exact List.map_append

private theorem gapBlockSeconds_append
    (left right : List FirstOccurrenceGapBlock) :
    gapBlockSeconds (left ++ right) =
      gapBlockSeconds left ++ gapBlockSeconds right := by
  exact List.flatMap_append

private def seenAfter
    (seen : List Nat) (blocks : List FirstOccurrenceGapBlock) : List Nat :=
  (gapBlockMarkers blocks).reverse ++ seen

private theorem gapBlocksWellFormed_append
    {seen : List Nat} {left right : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen (left ++ right)) :
    GapBlocksWellFormed seen left ∧
      GapBlocksWellFormed (seenAfter seen left) right := by
  induction left generalizing seen with
  | nil =>
      exact ⟨S5_870.GapBlocksWellFormed.nil seen, by
        simpa [seenAfter] using formed⟩
  | cons block rest induction =>
      cases formed with
      | cons _ _ _ markerFresh secondsSeen tailFormed =>
          obtain ⟨restFormed, rightFormed⟩ := induction tailFormed
          refine ⟨S5_870.GapBlocksWellFormed.cons seen block rest
            markerFresh secondsSeen restFormed, ?_⟩
          simpa [seenAfter, S5_870.gapBlockMarkers,
            List.append_assoc] using rightFormed

private theorem marker_mem_renderGapBlocks
    {blocks : List FirstOccurrenceGapBlock} {marker : Nat}
    (member : marker ∈ gapBlockMarkers blocks) :
    marker ∈ renderGapBlocks blocks := by
  induction blocks with
  | nil => simp [S5_870.gapBlockMarkers] at member
  | cons block rest induction =>
      simp only [S5_870.gapBlockMarkers, List.map_cons,
        List.mem_cons] at member
      rcases member with atMarker | inRest
      · subst marker
        simp [S5_870.renderGapBlocks]
      · simp [S5_870.renderGapBlocks, induction inRest]

private theorem seenAfter_mem_renderGapBlocks
    {seen stem : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (seenInStem : ∀ letter, letter ∈ seen → letter ∈ stem) :
    ∀ letter, letter ∈ seenAfter seen blocks →
      letter ∈ stem ++ renderGapBlocks blocks := by
  intro letter member
  simp only [seenAfter, List.mem_append, List.mem_reverse] at member
  rcases member with inMarkers | inSeen
  · exact List.mem_append.mpr <| Or.inr <|
      marker_mem_renderGapBlocks inMarkers
  · exact List.mem_append.mpr <| Or.inl <| seenInStem letter inSeen

private theorem nodup_length_le_of_subset
    {source target : List Nat}
    (nodup : source.Nodup)
    (subset : ∀ value, value ∈ source → value ∈ target) :
    source.length ≤ target.length := by
  induction source generalizing target with
  | nil => simp
  | cons head tail induction =>
      have nodupParts := List.pairwise_cons.mp nodup
      have headNotTail : head ∉ tail := by
        intro member
        exact (nodupParts.1 head member) rfl
      have headTarget : head ∈ target :=
        subset head (List.Mem.head tail)
      have tailSubset :
          ∀ value, value ∈ tail → value ∈ target.erase head := by
        intro value member
        have different : value ≠ head := by
          intro equal
          subst value
          exact headNotTail member
        exact (List.mem_erase_of_ne different).mpr
          (subset value (List.Mem.tail head member))
      have lengthBound := induction nodupParts.2 tailSubset
      rw [List.length_erase_of_mem headTarget] at lengthBound
      have targetPositive : 1 ≤ target.length := by
        exact List.length_pos_iff.mpr (by
          intro empty
          subst target
          simp at headTarget)
      simp only [List.length_cons]
      omega

private theorem canonicalSeconds_length_le
    (marker : Nat) (seconds : List Nat) :
    (canonicalSeconds marker seconds).length ≤ seconds.length :=
  nodup_length_le_of_subset
    (canonicalSeconds_nodup marker seconds)
    (by
      intro letter member
      exact (canonicalSeconds_mem_iff marker letter seconds).mp member)

private theorem render_normalizeGapBlocks_length_le
    (blocks : List FirstOccurrenceGapBlock) :
    (renderGapBlocks (normalizeGapBlocks blocks)).length ≤
      (renderGapBlocks blocks).length := by
  induction blocks with
  | nil => simp [normalizeGapBlocks, S5_870.renderGapBlocks]
  | cons block rest induction =>
      have current := canonicalSeconds_length_le
        block.marker block.seconds
      have restBound :
          (S5_870.renderGapBlocks (normalizeGapBlocks rest)).length ≤
            (S5_870.renderGapBlocks rest).length := induction
      change
        (S5_870.renderGapBlocks
          (normalizeGapBlock block :: normalizeGapBlocks rest)).length ≤
        (S5_870.renderGapBlocks (block :: rest)).length
      simp only [S5_870.renderGapBlocks, normalizeGapBlock_seconds,
        List.length_cons, List.length_append]
      omega

/-! ### One protected-occurrence deletion -/

private def eraseBlockSecond
    (block : FirstOccurrenceGapBlock) (selected : Nat) :
    FirstOccurrenceGapBlock where
  marker := block.marker
  seconds := block.seconds.erase selected

private theorem gapBlocksWellFormed_erase_last
    {seen : List Nat} {middle : List FirstOccurrenceGapBlock}
    {block : FirstOccurrenceGapBlock} (selected : Nat)
    (formed : GapBlocksWellFormed seen (middle ++ [block])) :
    GapBlocksWellFormed seen
      (middle ++ [eraseBlockSecond block selected]) := by
  induction middle generalizing seen with
  | nil =>
      simp only [List.nil_append] at formed ⊢
      cases formed with
      | cons _ _ _ markerFresh secondsSeen tailFormed =>
          exact S5_870.GapBlocksWellFormed.cons seen
            (eraseBlockSecond block selected) [] markerFresh (by
              intro letter member
              exact secondsSeen letter <|
                List.mem_of_mem_erase member)
            (S5_870.GapBlocksWellFormed.nil _)
  | cons head rest induction =>
      simp only [List.cons_append] at formed ⊢
      cases formed with
      | cons _ _ _ markerFresh secondsSeen tailFormed =>
          exact S5_870.GapBlocksWellFormed.cons seen head
            (rest ++ [eraseBlockSecond block selected])
            markerFresh secondsSeen (induction tailFormed)

private theorem gapBlockMarkers_erase_last
    (middle : List FirstOccurrenceGapBlock)
    (block : FirstOccurrenceGapBlock) (selected : Nat) :
    gapBlockMarkers (middle ++ [eraseBlockSecond block selected]) =
      gapBlockMarkers (middle ++ [block]) := by
  simp [gapBlockMarkers_append, S5_870.gapBlockMarkers,
    eraseBlockSecond]

private theorem mem_gapBlockSeconds_erase_last_of_ne
    (middle : List FirstOccurrenceGapBlock)
    (block : FirstOccurrenceGapBlock) {selected tested : Nat}
    (different : tested ≠ selected)
    (member : tested ∈ gapBlockSeconds (middle ++ [block])) :
    tested ∈ gapBlockSeconds
      (middle ++ [eraseBlockSecond block selected]) := by
  induction middle with
  | nil =>
      simpa [S5_870.gapBlockSeconds, eraseBlockSecond] using
        (List.mem_erase_of_ne different).mpr member
  | cons head rest induction =>
      simp only [List.cons_append, S5_870.gapBlockSeconds,
        List.flatMap_cons, List.mem_append] at member ⊢
      rcases member with inHead | inRest
      · exact Or.inl inHead
      · exact Or.inr (induction inRest)

private theorem noBlockProtector_erase_last
    {seen : List Nat} {middle : List FirstOccurrenceGapBlock}
    {block : FirstOccurrenceGapBlock} {selected : Nat}
    (formed : GapBlocksWellFormed seen (middle ++ [block]))
    (selectedInSeen : selected ∈ seen)
    (noProtector : ¬HasBlockProtector (middle ++ [block])) :
    ¬HasBlockProtector
      (middle ++ [eraseBlockSecond block selected]) := by
  intro reducedProtector
  obtain ⟨protector, markerMember, secondsAbsent⟩ := reducedProtector
  have originalMarker :
      protector ∈ gapBlockMarkers (middle ++ [block]) := by
    rw [← gapBlockMarkers_erase_last middle block selected]
    exact markerMember
  have protectorNe : protector ≠ selected := by
    intro equal
    subst protector
    exact (formed.markersAvoidSeen selected selectedInSeen) originalMarker
  have originalSeconds :
      protector ∈ gapBlockSeconds (middle ++ [block]) := by
    by_cases member : protector ∈ gapBlockSeconds (middle ++ [block])
    · exact member
    · exact False.elim <|
        noProtector ⟨protector, originalMarker, member⟩
  exact secondsAbsent <|
    mem_gapBlockSeconds_erase_last_of_ne middle block protectorNe
      originalSeconds

private theorem render_noFreshSingleton_of_noProtector
    {seen stem : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks)
    (seenInStem : ∀ letter, letter ∈ seen → letter ∈ stem)
    (noProtector : ¬HasBlockProtector blocks) :
    ∀ tested, tested ∈ renderGapBlocks blocks → tested ∉ stem →
      (renderGapBlocks blocks).count tested ≠ 1 := by
  intro tested rendered testedNotStem
  have renderedPositive :
      0 < (S5_870.renderGapBlocks blocks).count tested :=
    List.count_pos_iff.mpr rendered
  have countFormula := S5_870.count_renderGapBlocks tested blocks
  have markerOrSecond :
      tested ∈ S5_870.gapBlockMarkers blocks ∨
        tested ∈ S5_870.gapBlockSeconds blocks := by
    by_cases inMarkers : tested ∈ S5_870.gapBlockMarkers blocks
    · exact Or.inl inMarkers
    · have markerZero :
          (S5_870.gapBlockMarkers blocks).count tested = 0 :=
        List.count_eq_zero.mpr inMarkers
      have secondsPositive :
          0 < (S5_870.gapBlockSeconds blocks).count tested := by
        rw [countFormula, markerZero] at renderedPositive
        omega
      exact Or.inr <| List.count_pos_iff.mp secondsPositive
  have markerMember : tested ∈ S5_870.gapBlockMarkers blocks := by
    rcases markerOrSecond with inMarkers | inSeconds
    · exact inMarkers
    · rcases formed.secondsInSeenOrMarkers tested inSeconds with
        inSeen | inMarkers
      · exact False.elim <| testedNotStem (seenInStem tested inSeen)
      · exact inMarkers
  have secondsMember : tested ∈ S5_870.gapBlockSeconds blocks := by
    by_cases inSeconds : tested ∈ S5_870.gapBlockSeconds blocks
    · exact inSeconds
    · exact False.elim <|
        noProtector ⟨tested, markerMember, inSeconds⟩
  have markerPositive :
      0 < (S5_870.gapBlockMarkers blocks).count tested :=
    List.count_pos_iff.mpr markerMember
  have secondsPositive :
      0 < (S5_870.gapBlockSeconds blocks).count tested :=
    List.count_pos_iff.mpr secondsMember
  intro countOne
  rw [countFormula] at countOne
  omega

private theorem selected_mem_seenAfter_of_last_second
    {seen : List Nat} {beforeBlocks : List FirstOccurrenceGapBlock}
    {block : FirstOccurrenceGapBlock} {selected : Nat}
    (formed : GapBlocksWellFormed seen (beforeBlocks ++ [block]))
    (member : selected ∈ block.seconds) :
    selected ∈ seenAfter seen (beforeBlocks ++ [block]) := by
  obtain ⟨_, lastFormed⟩ :=
    gapBlocksWellFormed_append
      (seen := seen) (left := beforeBlocks) (right := [block]) formed
  cases lastFormed with
  | cons _ _ _ markerFresh secondsSeen tailFormed =>
      have known := secondsSeen selected member
      simpa [seenAfter, gapBlockMarkers_append,
        S5_870.gapBlockMarkers, List.append_assoc] using known

theorem listDerivesDeleteUnprotectedGap
    {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed [] blocks)
    (unprotected : HasUnprotectedGapOccurrence blocks) :
    ∃ reducedBlocks,
      ListDerives (renderGapBlocks blocks)
        (renderGapBlocks reducedBlocks) ∧
      (renderGapBlocks reducedBlocks).length <
        (renderGapBlocks blocks).length := by
  obtain ⟨beforeBlocks, firstBlock, middle, lastBlock, afterBlocks,
      selected, blockShape, selectedInFirst, selectedInLast,
      selectedNotMiddle, noProtector⟩ := unprotected
  let leadingBlocks := beforeBlocks ++ [firstBlock]
  let segment := middle ++ [lastBlock]
  let segmentSeen := seenAfter [] leadingBlocks
  have formedShape :
      GapBlocksWellFormed [] (leadingBlocks ++ (segment ++ afterBlocks)) := by
    have originalFormed := formed
    rw [blockShape] at originalFormed
    simpa [leadingBlocks, segment, List.append_assoc] using
      originalFormed
  obtain ⟨leadingFormed, tailFormed⟩ :=
    gapBlocksWellFormed_append formedShape
  obtain ⟨segmentFormed, afterFormed⟩ :=
    gapBlocksWellFormed_append tailFormed
  have selectedInSegmentSeen : selected ∈ segmentSeen := by
    exact selected_mem_seenAfter_of_last_second leadingFormed
      selectedInFirst
  let reducedLast := eraseBlockSecond lastBlock selected
  let reducedSegment := middle ++ [reducedLast]
  have reducedSegmentFormed :
      GapBlocksWellFormed segmentSeen reducedSegment := by
    exact gapBlocksWellFormed_erase_last selected segmentFormed
  have reducedNoProtector :
      ¬HasBlockProtector reducedSegment := by
    exact noBlockProtector_erase_last segmentFormed
      selectedInSegmentSeen noProtector
  obtain ⟨secondBefore, secondAfter, firstSecondsShape,
      selectedNotSecondAfter⟩ :=
    exists_rightmost_split selectedInFirst
  let markerStem := renderGapBlocks beforeBlocks ++ [firstBlock.marker]
  let deletionStem := markerStem ++ secondBefore ++ [selected]
  have leadingSeenInMarkerStem :
      ∀ letter, letter ∈ segmentSeen → letter ∈ markerStem := by
    intro letter member
    have markerMember : letter ∈ gapBlockMarkers leadingBlocks := by
      simpa [segmentSeen, seenAfter] using member
    change letter ∈ gapBlockMarkers (beforeBlocks ++ [firstBlock]) at markerMember
    rw [gapBlockMarkers_append] at markerMember
    simp only [S5_870.gapBlockMarkers, List.map_singleton,
      List.mem_append, List.mem_singleton] at markerMember
    rcases markerMember with inBefore | atFirst
    · exact List.mem_append.mpr <| Or.inl <|
        marker_mem_renderGapBlocks inBefore
    · subst letter
      simp [markerStem]
  have segmentSeenInDeletionStem :
      ∀ letter, letter ∈ segmentSeen → letter ∈ deletionStem := by
    intro letter member
    exact List.mem_append.mpr <| Or.inl <|
      List.mem_append.mpr <| Or.inl <|
        leadingSeenInMarkerStem letter member
  have secondAfterInDeletionStem :
      ∀ letter, letter ∈ secondAfter → letter ∈ deletionStem := by
    intro letter member
    obtain ⟨beforeFormed, firstFormed⟩ :=
      gapBlocksWellFormed_append
        (seen := []) (left := beforeBlocks) (right := [firstBlock])
        leadingFormed
    cases firstFormed with
    | cons _ _ _ markerFresh secondsSeen tail =>
        have known := secondsSeen letter <| by
          rw [firstSecondsShape]
          exact List.mem_append.mpr <| Or.inr <|
            List.Mem.tail selected member
        rcases List.mem_cons.mp known with atMarker | inSeen
        · subst letter
          exact List.mem_append.mpr <| Or.inl <|
            List.mem_append.mpr <| Or.inl <| by simp [markerStem]
        · have seenRendered :=
            seenAfter_mem_renderGapBlocks
              (seen := []) (stem := []) (blocks := beforeBlocks)
              (by simp) letter inSeen
          exact List.mem_append.mpr <| Or.inl <|
            List.mem_append.mpr <| Or.inl <| by
              exact List.mem_append.mpr <| Or.inl <| by
                simpa using seenRendered
  let factor := secondAfter ++ renderGapBlocks reducedSegment
  have noFreshSingleton :
      ∀ letter, letter ∈ factor → letter ∉ deletionStem →
        factor.count letter ≠ 1 := by
    intro letter factorMember letterFresh
    have secondAfterAbsent : letter ∉ secondAfter := by
      intro member
      exact letterFresh (secondAfterInDeletionStem letter member)
    have renderedMember : letter ∈ renderGapBlocks reducedSegment := by
      rcases List.mem_append.mp factorMember with inSecondAfter | inRendered
      · exact False.elim (secondAfterAbsent inSecondAfter)
      · exact inRendered
    have renderedNotOne :=
      render_noFreshSingleton_of_noProtector reducedSegmentFormed
        segmentSeenInDeletionStem reducedNoProtector letter
        renderedMember letterFresh
    have secondAfterCount : secondAfter.count letter = 0 :=
      List.count_eq_zero.mpr secondAfterAbsent
    simpa [factor, List.count_append, secondAfterCount] using renderedNotOne
  have factorRepeated :=
    expandedFactor_count_ge_two deletionStem factor noFreshSingleton
  have lastSplit :
      lastBlock.seconds.Perm
        (lastBlock.seconds.erase selected ++ [selected]) :=
    (List.perm_cons_erase selectedInLast).trans <|
      perm_append_comm [selected] (lastBlock.seconds.erase selected)
  obtain ⟨middleFormed, lastFormed⟩ :=
    gapBlocksWellFormed_append
      (seen := segmentSeen) (left := middle) (right := [lastBlock])
      segmentFormed
  let leadingRendered := renderGapBlocks leadingBlocks
  let middleStem := leadingRendered ++ renderGapBlocks middle
  let lastStem := middleStem ++ [lastBlock.marker]
  have segmentSeenInLeading :
      ∀ letter, letter ∈ segmentSeen → letter ∈ leadingRendered := by
    intro letter member
    have rendered :=
      seenAfter_mem_renderGapBlocks
        (seen := []) (stem := []) (blocks := leadingBlocks)
        (by simp) letter member
    simpa [leadingRendered] using rendered
  have lastSeenInStem :
      ∀ letter, letter ∈ lastBlock.seconds → letter ∈ lastStem := by
    cases lastFormed with
    | cons _ _ _ markerFresh secondsSeen tail =>
        intro letter member
        rcases List.mem_cons.mp (secondsSeen letter member) with
          atMarker | inSeen
        · subst letter
          exact List.mem_append.mpr <| Or.inr <| by simp [lastStem]
        · have inMiddleStem :=
            seenAfter_mem_renderGapBlocks
              (seen := segmentSeen) (stem := leadingRendered)
              (blocks := middle) segmentSeenInLeading letter inSeen
          exact List.mem_append.mpr <| Or.inl <| by
            simpa [middleStem] using inMiddleStem
  have moveLast :
      ListDerives
        (renderGapBlocks blocks)
        (lastStem ++ (lastBlock.seconds.erase selected ++ [selected]) ++
          renderGapBlocks afterBlocks) := by
    have moved := listDerivesPermuteAfterSeen lastStem
      (renderGapBlocks afterBlocks) lastSeenInStem lastSplit
    simpa [blockShape, leadingBlocks, leadingRendered, middleStem,
      lastStem, renderGapBlocks_append, S5_870.renderGapBlocks,
      List.append_assoc] using moved
  have movedShape :
      lastStem ++ (lastBlock.seconds.erase selected ++ [selected]) ++
          renderGapBlocks afterBlocks =
        deletionStem ++ factor ++ [selected] ++
          renderGapBlocks afterBlocks := by
    simp [lastStem, middleStem, leadingRendered, leadingBlocks,
      deletionStem, markerStem, factor, reducedSegment, reducedLast,
      eraseBlockSecond, firstSecondsShape, renderGapBlocks_append,
      S5_870.renderGapBlocks, List.append_assoc]
  rw [movedShape] at moveLast
  have expand :
      ListDerives
        (deletionStem ++ factor ++ [selected] ++
          renderGapBlocks afterBlocks)
        (deletionStem ++ expandedFactor deletionStem factor ++
          [selected] ++ renderGapBlocks afterBlocks) := by
    simpa [List.append_assoc] using
      listDerivesExpandedFactor deletionStem factor
        ([selected] ++ renderGapBlocks afterBlocks)
  have factorNe : factor ≠ [] := by
    intro empty
    have markerInFactor : lastBlock.marker ∈ factor := by
      exact List.mem_append.mpr <| Or.inr <|
        marker_mem_renderGapBlocks <| by
          simp [reducedSegment, reducedLast, eraseBlockSecond,
            S5_870.gapBlockMarkers]
    rw [empty] at markerInFactor
    simp at markerInFactor
  have expandedNe : expandedFactor deletionStem factor ≠ [] := by
    intro empty
    have factorMember : lastBlock.marker ∈ factor := by
      exact List.mem_append.mpr <| Or.inr <|
        marker_mem_renderGapBlocks <| by
          simp [reducedSegment, reducedLast, eraseBlockSecond,
            S5_870.gapBlockMarkers]
    have expandedMember :
        lastBlock.marker ∈ expandedFactor deletionStem factor :=
      (expandedFactor_mem_iff deletionStem factor lastBlock.marker).mpr
        factorMember
    rw [empty] at expandedMember
    simp at expandedMember
  cases expandedShape : expandedFactor deletionStem factor with
  | nil => exact False.elim (expandedNe expandedShape)
  | cons factorHead factorTail =>
      obtain ⟨firstBefore, firstBetween, markerStemShape⟩ :=
        List.mem_iff_append.mp <| by
          have selectedKnown : selected ∈ markerStem := by
            obtain ⟨beforeFormed, firstFormed⟩ :=
              gapBlocksWellFormed_append
                (seen := []) (left := beforeBlocks)
                (right := [firstBlock]) leadingFormed
            cases firstFormed with
            | cons _ _ _ markerFresh secondsSeen tail =>
                rcases List.mem_cons.mp
                    (secondsSeen selected selectedInFirst) with
                  atMarker | inSeen
                · subst selected
                  simp [markerStem]
                · have rendered :=
                    seenAfter_mem_renderGapBlocks
                      (seen := []) (stem := []) (blocks := beforeBlocks)
                      (by simp) selected inSeen
                  exact List.mem_append.mpr <| Or.inl <| by
                    simpa [markerStem] using rendered
          exact selectedKnown
      have deletionStemShape :
          deletionStem = firstBefore ++ [selected] ++
            (firstBetween ++ secondBefore) ++ [selected] := by
        simp [deletionStem, markerStemShape, List.append_assoc]
      have deleteExpanded :
          ListDerives
            (deletionStem ++ (factorHead :: factorTail) ++ [selected] ++
                renderGapBlocks afterBlocks)
            (deletionStem ++ (factorHead :: factorTail) ++
                renderGapBlocks afterBlocks) := by
        simpa [deletionStemShape, List.append_assoc] using
          listDerivesDeleteAfterSimpleFree firstBefore
            (firstBetween ++ secondBefore)
            (renderGapBlocks afterBlocks) selected factorHead factorTail
            (by
              intro letter member
              have repeated := factorRepeated letter <| by
                simpa [expandedShape] using member
              simpa [expandedShape] using repeated)
      have contractFactor :
          ListDerives
            (deletionStem ++ (factorHead :: factorTail) ++
              renderGapBlocks afterBlocks)
            (deletionStem ++ factor ++
              renderGapBlocks afterBlocks) := by
        simpa [expandedShape] using
          (listDerivesExpandedFactor deletionStem factor
            (renderGapBlocks afterBlocks)).symm
      let reducedBlocks := beforeBlocks ++ [firstBlock] ++ middle ++
        [reducedLast] ++ afterBlocks
      have reducedShape :
          deletionStem ++ factor ++
              renderGapBlocks afterBlocks =
            renderGapBlocks reducedBlocks := by
        simp [reducedBlocks, deletionStem, markerStem, factor,
          firstSecondsShape, reducedSegment, reducedLast,
          eraseBlockSecond, renderGapBlocks_append,
          S5_870.renderGapBlocks, List.append_assoc]
      have derivation :
          ListDerives (renderGapBlocks blocks)
            (renderGapBlocks reducedBlocks) := by
        rw [← reducedShape]
        exact moveLast.trans <| expand.trans <| by
          simpa [expandedShape] using
            deleteExpanded.trans contractFactor
      have shorter :
          (renderGapBlocks reducedBlocks).length <
            (renderGapBlocks blocks).length := by
        rw [blockShape]
        simp [reducedBlocks, reducedLast, eraseBlockSecond,
          renderGapBlocks_append, S5_870.renderGapBlocks,
          List.length_erase_of_mem selectedInLast,
          List.append_assoc]
        have positive : 0 < lastBlock.seconds.length :=
          List.length_pos_iff.mpr (List.ne_nil_of_mem selectedInLast)
        omega
      exact ⟨reducedBlocks, derivation, shorter⟩

private theorem exists_protectedCanonicalList_aux :
    ∀ bound letters,
      letters.length = bound →
        ∃ canonical,
          ListDerives letters canonical ∧
            IsProtectedCanonicalList canonical := by
  classical
  intro bound
  induction bound using Nat.strongRecOn
  rename_i current induction
  intro letters lengthEq
  let normalBlocks := normalizeGapBlocks (gapBlocksList letters)
  let normalList := renderGapBlocks normalBlocks
  have normalizeDerives : ListDerives letters normalList := by
    simpa [normalList, normalBlocks, blockNormalList] using
      listDerivesBlockNormal letters
  have normalFormed : GapBlocksWellFormed [] normalBlocks := by
    exact normalizeGapBlocks_wellFormed
      (S5_870.gapBlocksList_wellFormed letters)
  have normalNormal : GapBlocksNormal normalBlocks :=
    normalizeGapBlocks_normal (gapBlocksList letters)
  have normalLength : normalList.length ≤ letters.length := by
    simpa [normalList, normalBlocks, S5_870.render_gapBlocksList] using
      render_normalizeGapBlocks_length_le (gapBlocksList letters)
  by_cases occurrencesProtected : ProtectedGapOccurrences normalBlocks
  · exact ⟨normalList, normalizeDerives, normalBlocks, rfl,
      ⟨normalFormed, normalNormal, occurrencesProtected⟩⟩
  · have unprotected : HasUnprotectedGapOccurrence normalBlocks := by
      exact Classical.byContradiction (fun absent =>
        occurrencesProtected absent)
    obtain ⟨reducedBlocks, deleteDerives, reducedShorter⟩ :=
      listDerivesDeleteUnprotectedGap normalFormed unprotected
    have reducedBound :
        (renderGapBlocks reducedBlocks).length < current := by
      rw [← lengthEq]
      change (renderGapBlocks normalBlocks).length ≤ letters.length at normalLength
      omega
    obtain ⟨canonical, reducedDerives, canonicalForm⟩ :=
      induction (renderGapBlocks reducedBlocks).length reducedBound
        (renderGapBlocks reducedBlocks) rfl
    exact ⟨canonical,
      normalizeDerives.trans (deleteDerives.trans reducedDerives),
      canonicalForm⟩

/-- Every list derives to a block-normal representative satisfying Lee--Li
condition (IV). -/
theorem exists_protectedCanonicalList (letters : List Nat) :
    ∃ canonical,
      ListDerives letters canonical ∧
        IsProtectedCanonicalList canonical :=
  exists_protectedCanonicalList_aux letters.length letters rfl

/-! ### Signature reconstruction on well-formed block renderings -/

private theorem firstOccurrenceSequenceAux_append_known
    (seen suffix : List Nat) :
    ∀ (known : List Nat),
      (∀ letter, letter ∈ known → letter ∈ seen) →
        S5_870.firstOccurrenceSequenceAux seen (known ++ suffix) =
          S5_870.firstOccurrenceSequenceAux seen suffix
  | [], _ => rfl
  | head :: tail, allKnown => by
      have headKnown : head ∈ seen :=
        allKnown head (List.Mem.head tail)
      have tailKnown : ∀ letter, letter ∈ tail → letter ∈ seen := by
        intro letter member
        exact allKnown letter (List.Mem.tail head member)
      simp [S5_870.firstOccurrenceSequenceAux, headKnown,
        firstOccurrenceSequenceAux_append_known seen suffix tail tailKnown]

private theorem firstOccurrenceSequenceAux_renderGapBlocks
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks) :
    S5_870.firstOccurrenceSequenceAux seen (renderGapBlocks blocks) =
      gapBlockMarkers blocks := by
  induction formed with
  | nil =>
      simp [S5_870.renderGapBlocks, S5_870.gapBlockMarkers,
        S5_870.firstOccurrenceSequenceAux]
  | cons seen block rest markerFresh secondsSeen tail induction =>
      change
        S5_870.firstOccurrenceSequenceAux seen
            (block.marker :: (block.seconds ++ renderGapBlocks rest)) =
          block.marker :: gapBlockMarkers rest
      rw [S5_870.firstOccurrenceSequenceAux]
      simp only [markerFresh, if_neg, S5_870.gapBlockMarkers,
        List.map_cons]
      rw [firstOccurrenceSequenceAux_append_known
        (block.marker :: seen) (renderGapBlocks rest)
        block.seconds secondsSeen]
      exact congrArg (List.cons block.marker) induction

private theorem firstOccurrenceSequenceList_renderGapBlocks
    {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed [] blocks) :
    S5_870.firstOccurrenceSequenceList (renderGapBlocks blocks) =
      gapBlockMarkers blocks := by
  exact firstOccurrenceSequenceAux_renderGapBlocks formed

private theorem secondOccurrenceGapList_renderGapBlocks
    (selected : Nat) {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed [] blocks) :
    S5_870.secondOccurrenceGapList (renderGapBlocks blocks) selected =
      S5_870.blockSecondGapAux selected [] blocks := by
  exact S5_870.secondOccurrenceGapAux_renderGapBlocks selected formed

private theorem pointwise_of_map_eq
    {alpha beta : Type} (left right : alpha → beta) :
    ∀ {keys : List alpha},
      keys.map left = keys.map right →
        ∀ key, key ∈ keys → left key = right key
  | [], _, _, member => by simp at member
  | head :: tail, equality, key, member => by
      simp only [List.map_cons] at equality
      injection equality with headEq tailEq
      rcases List.mem_cons.mp member with atHead | inTail
      · simpa [atHead] using headEq
      · exact pointwise_of_map_eq left right tailEq key inTail

private theorem blockSignatureData_of_refined_eq
    {left right : List FirstOccurrenceGapBlock}
    (leftFormed : GapBlocksWellFormed [] left)
    (rightFormed : GapBlocksWellFormed [] right)
    (same :
      refinedGapSignatureList (renderGapBlocks left) =
        refinedGapSignatureList (renderGapBlocks right)) :
    gapBlockMarkers left = gapBlockMarkers right ∧
      ∀ selected, selected ∈ gapBlockMarkers left →
        S5_870.blockSecondGapAux selected [] left =
          S5_870.blockSecondGapAux selected [] right := by
  have sameGap :
      S5_870.gapSignatureList (renderGapBlocks left) =
        S5_870.gapSignatureList (renderGapBlocks right) :=
    congrArg RefinedGapSignature.gap same
  have markers : gapBlockMarkers left = gapBlockMarkers right := by
    have firsts := congrArg S5_870.GapSignature.firstOccurrences sameGap
    change
      S5_870.firstOccurrenceSequenceList (renderGapBlocks left) =
        S5_870.firstOccurrenceSequenceList (renderGapBlocks right) at firsts
    rw [firstOccurrenceSequenceList_renderGapBlocks leftFormed,
      firstOccurrenceSequenceList_renderGapBlocks rightFormed] at firsts
    exact firsts
  refine ⟨markers, ?_⟩
  have secondGaps :=
    congrArg S5_870.GapSignature.secondOccurrenceGaps sameGap
  change
    S5_870.secondOccurrenceGapsList (renderGapBlocks left) =
      S5_870.secondOccurrenceGapsList (renderGapBlocks right) at secondGaps
  unfold S5_870.secondOccurrenceGapsList at secondGaps
  rw [firstOccurrenceSequenceList_renderGapBlocks leftFormed,
    firstOccurrenceSequenceList_renderGapBlocks rightFormed,
    ← markers] at secondGaps
  intro selected member
  have pointwise := pointwise_of_map_eq
    (S5_870.secondOccurrenceGapList (renderGapBlocks left))
    (S5_870.secondOccurrenceGapList (renderGapBlocks right))
    secondGaps selected member
  simpa [secondOccurrenceGapList_renderGapBlocks selected leftFormed,
    secondOccurrenceGapList_renderGapBlocks selected rightFormed] using
      pointwise

private theorem blockSecondGapAux_skip_prefix
    (selected : Nat) :
    ∀ (seen : List Nat) (priorBlocks suffix : List FirstOccurrenceGapBlock),
      selected ∉ gapBlockSeconds priorBlocks →
        S5_870.blockSecondGapAux selected seen (priorBlocks ++ suffix) =
          S5_870.blockSecondGapAux selected (seenAfter seen priorBlocks) suffix
  | _, [], _, _ => by simp [seenAfter, S5_870.gapBlockMarkers]
  | seen, block :: rest, suffix, absent => by
      change selected ∉ block.seconds ++ gapBlockSeconds rest at absent
      have currentAbsent : selected ∉ block.seconds := by
        intro member
        exact absent (List.mem_append.mpr <| Or.inl member)
      have restAbsent : selected ∉ gapBlockSeconds rest := by
        intro member
        exact absent (List.mem_append.mpr <| Or.inr member)
      simp only [List.cons_append, S5_870.blockSecondGapAux,
        currentAbsent, if_neg]
      rw [blockSecondGapAux_skip_prefix selected
        (block.marker :: seen) rest suffix restAbsent]
      congr 2
      simp [seenAfter, S5_870.gapBlockMarkers, List.append_assoc]

private theorem currentSeconds_mem_iff_of_no_prior
    {priorBlocks : List FirstOccurrenceGapBlock}
    {leftBlock rightBlock : FirstOccurrenceGapBlock}
    {leftRest rightRest : List FirstOccurrenceGapBlock}
    {selected : Nat}
    (markerEq : leftBlock.marker = rightBlock.marker)
    (priorAbsent : selected ∉ gapBlockSeconds priorBlocks)
    (gapEq :
      S5_870.blockSecondGapAux selected []
          (priorBlocks ++ leftBlock :: leftRest) =
        S5_870.blockSecondGapAux selected []
          (priorBlocks ++ rightBlock :: rightRest)) :
    selected ∈ leftBlock.seconds ↔ selected ∈ rightBlock.seconds := by
  rw [blockSecondGapAux_skip_prefix selected [] priorBlocks
      (leftBlock :: leftRest) priorAbsent,
    blockSecondGapAux_skip_prefix selected [] priorBlocks
      (rightBlock :: rightRest) priorAbsent] at gapEq
  constructor
  · intro member
    apply (S5_870.blockSecondGapAux_eq_current_iff selected
      (seenAfter [] priorBlocks) rightBlock rightRest).1
    calc
      S5_870.blockSecondGapAux selected (seenAfter [] priorBlocks)
          (rightBlock :: rightRest) =
          S5_870.blockSecondGapAux selected (seenAfter [] priorBlocks)
            (leftBlock :: leftRest) := gapEq.symm
      _ = some (leftBlock.marker :: seenAfter [] priorBlocks).length :=
        (S5_870.blockSecondGapAux_eq_current_iff selected
          (seenAfter [] priorBlocks) leftBlock leftRest).2 member
      _ = some (rightBlock.marker :: seenAfter [] priorBlocks).length := by
        simp [markerEq]
  · intro member
    apply (S5_870.blockSecondGapAux_eq_current_iff selected
      (seenAfter [] priorBlocks) leftBlock leftRest).1
    calc
      S5_870.blockSecondGapAux selected (seenAfter [] priorBlocks)
          (leftBlock :: leftRest) =
          S5_870.blockSecondGapAux selected (seenAfter [] priorBlocks)
            (rightBlock :: rightRest) := gapEq
      _ = some (rightBlock.marker :: seenAfter [] priorBlocks).length :=
        (S5_870.blockSecondGapAux_eq_current_iff selected
          (seenAfter [] priorBlocks) rightBlock rightRest).2 member
      _ = some (leftBlock.marker :: seenAfter [] priorBlocks).length := by
        simp [markerEq]

private theorem mem_renderGapBlocks_iff
    (tested : Nat) (blocks : List FirstOccurrenceGapBlock) :
    tested ∈ renderGapBlocks blocks ↔
      tested ∈ gapBlockMarkers blocks ∨
        tested ∈ gapBlockSeconds blocks := by
  induction blocks with
  | nil =>
      simp [S5_870.renderGapBlocks, S5_870.gapBlockMarkers,
        S5_870.gapBlockSeconds]
  | cons block rest induction =>
      change
        tested ∈ block.marker :: (block.seconds ++ renderGapBlocks rest) ↔
          tested ∈ block.marker :: gapBlockMarkers rest ∨
            tested ∈ block.seconds ++ gapBlockSeconds rest
      simp only [List.mem_cons, List.mem_append, induction]
      constructor
      · intro member
        rcases member with atMarker | remainder
        · exact Or.inl (Or.inl atMarker)
        · rcases remainder with inSeconds | remainder
          · exact Or.inr (Or.inl inSeconds)
          · rcases remainder with inMarkers | inRest
            · exact Or.inl (Or.inr inMarkers)
            · exact Or.inr (Or.inr inRest)
      · intro member
        rcases member with inMarkers | remainder
        · rcases inMarkers with atMarker | inRestMarkers
          · exact Or.inl atMarker
          · exact Or.inr (Or.inr (Or.inl inRestMarkers))
        · rcases remainder with inSeconds | inRestSeconds
          · exact Or.inr (Or.inl inSeconds)
          · exact Or.inr (Or.inr (Or.inr inRestSeconds))

private theorem futureMarker_not_mem_renderGapBlocks
    {priorBlocks : List FirstOccurrenceGapBlock}
    {nextBlock : FirstOccurrenceGapBlock}
    {rest : List FirstOccurrenceGapBlock}
    (formed :
      GapBlocksWellFormed [] (priorBlocks ++ nextBlock :: rest)) :
    nextBlock.marker ∉ renderGapBlocks priorBlocks := by
  obtain ⟨priorFormed, nextFormed⟩ := gapBlocksWellFormed_append formed
  cases nextFormed with
  | cons _ _ _ markerFresh secondsSeen tail =>
      have markerAbsent :
          nextBlock.marker ∉ gapBlockMarkers priorBlocks := by
        simpa [seenAfter] using markerFresh
      have secondsAbsent :
          nextBlock.marker ∉ gapBlockSeconds priorBlocks := by
        intro member
        rcases priorFormed.secondsInSeenOrMarkers nextBlock.marker member with
          inSeen | inMarkers
        · simp at inSeen
        · exact markerAbsent inMarkers
      intro rendered
      rcases (mem_renderGapBlocks_iff nextBlock.marker priorBlocks).mp
          rendered with inMarkers | inSeconds
      · exact markerAbsent inMarkers
      · exact secondsAbsent inSeconds

private theorem tailMarker_not_mem_renderGapBlocks
    {priorBlocks tailBlocks : List FirstOccurrenceGapBlock}
    {marker : Nat}
    (formed : GapBlocksWellFormed [] (priorBlocks ++ tailBlocks))
    (markerInTail : marker ∈ gapBlockMarkers tailBlocks) :
    marker ∉ renderGapBlocks priorBlocks := by
  obtain ⟨priorFormed, tailFormed⟩ := gapBlocksWellFormed_append formed
  have markerNotSeen : marker ∉ seenAfter [] priorBlocks := by
    intro inSeen
    exact tailFormed.markersAvoidSeen marker inSeen markerInTail
  have markerNotPriorMarkers : marker ∉ gapBlockMarkers priorBlocks := by
    simpa [seenAfter] using markerNotSeen
  have markerNotPriorSeconds : marker ∉ gapBlockSeconds priorBlocks := by
    intro inSeconds
    rcases priorFormed.secondsInSeenOrMarkers marker inSeconds with
      inSeen | inMarkers
    · simp at inSeen
    · exact markerNotPriorMarkers inMarkers
  intro rendered
  rcases (mem_renderGapBlocks_iff marker priorBlocks).mp rendered with
    inMarkers | inSeconds
  · exact markerNotPriorMarkers inMarkers
  · exact markerNotPriorSeconds inSeconds

private theorem exists_rightmost_block_second
    {selected : Nat} {blocks : List FirstOccurrenceGapBlock}
    (member : selected ∈ gapBlockSeconds blocks) :
    ∃ beforeBlocks firstBlock middle,
      blocks = beforeBlocks ++ [firstBlock] ++ middle ∧
        selected ∈ firstBlock.seconds ∧
        selected ∉ gapBlockSeconds middle := by
  induction blocks with
  | nil => simp [S5_870.gapBlockSeconds] at member
  | cons block rest induction =>
      change selected ∈ block.seconds ++ gapBlockSeconds rest at member
      by_cases inRest : selected ∈ gapBlockSeconds rest
      · obtain ⟨beforeBlocks, firstBlock, middle, shape,
            inFirst, notMiddle⟩ := induction inRest
        exact ⟨block :: beforeBlocks, firstBlock, middle, by simp [shape],
          inFirst, notMiddle⟩
      · have inBlock : selected ∈ block.seconds :=
          (List.mem_append.mp member).resolve_right inRest
        exact ⟨[], block, rest, by simp, inBlock, inRest⟩

private theorem markerLetter_eq_neutral
    {selected protector letter : Nat} {terminator : Option Nat}
    (notSelected : letter ≠ selected)
    (notProtector : letter ≠ protector)
    (notTerminator :
      ∀ final, terminator = some final → letter ≠ final) :
    markerLetter selected protector terminator letter = .neutral := by
  cases terminator with
  | none => simp [markerLetter, notSelected, notProtector]
  | some final =>
      simp [markerLetter, notSelected, notProtector,
        notTerminator final rfl]

private theorem foldl_step_avoiding
    (selected protector : Nat) (terminator : Option Nat)
    (state : PostSecondState) :
    ∀ letters : List Nat,
      selected ∉ letters → protector ∉ letters →
        (∀ final, terminator = some final → final ∉ letters) →
          letters.foldl
              (fun (current : PostSecondState) (letter : Nat) =>
                PostSecondState.step current
                  (markerLetter selected protector terminator letter)) state =
            state
  | [], _, _, _ => rfl
  | head :: tail, selectedAbsent, protectorAbsent, terminatorAbsent => by
      have headNotSelected : head ≠ selected := by
        intro equal
        subst head
        exact selectedAbsent (List.Mem.head tail)
      have headNotProtector : head ≠ protector := by
        intro equal
        subst head
        exact protectorAbsent (List.Mem.head tail)
      have headNotTerminator :
          ∀ final, terminator = some final → head ≠ final := by
        intro final finalEq equal
        subst head
        exact terminatorAbsent final finalEq (List.Mem.head tail)
      have tailSelected : selected ∉ tail := by
        intro member
        exact selectedAbsent (List.Mem.tail head member)
      have tailProtector : protector ∉ tail := by
        intro member
        exact protectorAbsent (List.Mem.tail head member)
      have tailTerminator :
          ∀ final, terminator = some final → final ∉ tail := by
        intro final finalEq member
        exact terminatorAbsent final finalEq (List.Mem.tail head member)
      simp only [List.foldl_cons,
        markerLetter_eq_neutral headNotSelected headNotProtector
          headNotTerminator]
      cases state <;>
        exact foldl_step_avoiding selected protector terminator _ tail
          tailSelected tailProtector tailTerminator

private theorem foldl_step_selected
    (selected protector : Nat) (terminator : Option Nat) :
    ∀ letters : List Nat,
      protector ∉ letters →
        (∀ final, terminator = some final → final ∉ letters) →
          letters.foldl
              (fun (current : PostSecondState) (letter : Nat) =>
                PostSecondState.step current
                  (markerLetter selected protector terminator letter))
              PostSecondState.selected =
            PostSecondState.selected
  | [], _, _ => rfl
  | head :: tail, protectorAbsent, terminatorAbsent => by
      have headNotProtector : head ≠ protector := by
        intro equal
        subst head
        exact protectorAbsent (List.Mem.head tail)
      have headNotTerminator :
          ∀ final, terminator = some final → head ≠ final := by
        intro final finalEq equal
        subst head
        exact terminatorAbsent final finalEq (List.Mem.head tail)
      have tailProtector : protector ∉ tail := by
        intro member
        exact protectorAbsent (List.Mem.tail head member)
      have tailTerminator :
          ∀ final, terminator = some final → final ∉ tail := by
        intro final finalEq member
        exact terminatorAbsent final finalEq (List.Mem.tail head member)
      by_cases atSelected : head = selected
      · subst head
        simp only [List.foldl_cons, markerLetter, if_pos,
          PostSecondState.step]
        exact foldl_step_selected selected protector terminator tail
          tailProtector tailTerminator
      · simp only [List.foldl_cons,
          markerLetter_eq_neutral atSelected headNotProtector
            headNotTerminator, PostSecondState.step]
        exact foldl_step_selected selected protector terminator tail
          tailProtector tailTerminator

private theorem foldl_step_selected_of_mem
    (selected protector : Nat) (terminator : Option Nat) :
    ∀ letters : List Nat,
      selected ∈ letters → protector ∉ letters →
        (∀ final, terminator = some final → final ∉ letters) →
          letters.foldl
              (fun (current : PostSecondState) (letter : Nat) =>
                PostSecondState.step current
                  (markerLetter selected protector terminator letter))
              PostSecondState.neutral =
            PostSecondState.selected
  | [], member, _, _ => by simp at member
  | head :: tail, selectedMember, protectorAbsent, terminatorAbsent => by
      have headNotProtector : head ≠ protector := by
        intro equal
        subst head
        exact protectorAbsent (List.Mem.head tail)
      have headNotTerminator :
          ∀ final, terminator = some final → head ≠ final := by
        intro final finalEq equal
        subst head
        exact terminatorAbsent final finalEq (List.Mem.head tail)
      have tailProtector : protector ∉ tail := by
        intro member
        exact protectorAbsent (List.Mem.tail head member)
      have tailTerminator :
          ∀ final, terminator = some final → final ∉ tail := by
        intro final finalEq member
        exact terminatorAbsent final finalEq (List.Mem.tail head member)
      by_cases atSelected : head = selected
      · subst head
        simp only [List.foldl_cons, markerLetter, if_pos,
          PostSecondState.step]
        exact foldl_step_selected selected protector terminator tail
          tailProtector tailTerminator
      · have selectedTail : selected ∈ tail := by
          rcases List.mem_cons.mp selectedMember with atHead | inTail
          · exact False.elim (atSelected atHead.symm)
          · exact inTail
        simp only [List.foldl_cons,
          markerLetter_eq_neutral atSelected headNotProtector
            headNotTerminator, PostSecondState.step]
        exact foldl_step_selected_of_mem selected protector terminator tail
          selectedTail tailProtector tailTerminator

private theorem foldl_step_zero
    (selected protector : Nat) (terminator : Option Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun (current : PostSecondState) (letter : Nat) =>
            PostSecondState.step current
              (markerLetter selected protector terminator letter))
          PostSecondState.zero =
        PostSecondState.zero
  | [] => rfl
  | _ :: rest => by
      simp only [List.foldl_cons, PostSecondState.step]
      exact foldl_step_zero selected protector terminator rest

private theorem foldl_step_two
    (selected protector : Nat) (terminator : Option Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun (current : PostSecondState) (letter : Nat) =>
            PostSecondState.step current
              (markerLetter selected protector terminator letter))
          PostSecondState.two =
        PostSecondState.two
  | [] => rfl
  | _ :: rest => by
      simp only [List.foldl_cons, PostSecondState.step]
      exact foldl_step_two selected protector terminator rest

private theorem postSecondStateList_eq_zero_of_split
    (stem middle suffix : List Nat) (selected protector : Nat)
    (terminator : Option Nat)
    (selectedInStem : selected ∈ stem)
    (protectorNotStem : protector ∉ stem)
    (terminatorNotStem :
      ∀ final, terminator = some final → final ∉ stem)
    (selectedNotMiddle : selected ∉ middle)
    (protectorNotMiddle : protector ∉ middle)
    (terminatorNotMiddle :
      ∀ final, terminator = some final → final ∉ middle) :
    postSecondStateList
        (stem ++ [protector] ++ middle ++ [selected] ++ suffix)
        selected protector terminator = .zero := by
  have selectedNeProtector : selected ≠ protector := by
    intro equal
    subst protector
    exact protectorNotStem selectedInStem
  unfold postSecondStateList
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [foldl_step_selected_of_mem selected protector terminator stem
    selectedInStem protectorNotStem terminatorNotStem]
  have seesProtector :
      PostSecondState.step PostSecondState.selected
          (markerLetter selected protector terminator protector) =
        PostSecondState.protector := by
    simp [markerLetter, Ne.symm selectedNeProtector,
      PostSecondState.step]
  rw [seesProtector]
  rw [foldl_step_avoiding selected protector terminator .protector middle
    selectedNotMiddle protectorNotMiddle terminatorNotMiddle]
  have seesSelected :
      PostSecondState.step PostSecondState.protector
          (markerLetter selected protector terminator selected) =
        PostSecondState.zero := by
    simp [markerLetter, PostSecondState.step]
  rw [seesSelected]
  exact foldl_step_zero selected protector terminator suffix

private theorem postSecondStateList_eq_two_of_split
    (stem middle suffix : List Nat) (selected protector terminator : Nat)
    (selectedInStem : selected ∈ stem)
    (protectorNotStem : protector ∉ stem)
    (terminatorNotStem : terminator ∉ stem)
    (selectedNotMiddle : selected ∉ middle)
    (protectorNotMiddle : protector ∉ middle)
    (terminatorNotMiddle : terminator ∉ middle)
    (terminatorNeSelected : terminator ≠ selected)
    (terminatorNeProtector : terminator ≠ protector) :
    postSecondStateList
        (stem ++ [protector] ++ middle ++ [terminator] ++ suffix)
        selected protector (some terminator) = .two := by
  have selectedNeProtector : selected ≠ protector := by
    intro equal
    subst protector
    exact protectorNotStem selectedInStem
  unfold postSecondStateList
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [foldl_step_selected_of_mem selected protector (some terminator) stem
    selectedInStem protectorNotStem (by
      intro final equality
      injection equality with finalEq
      simpa [finalEq] using terminatorNotStem)]
  have seesProtector :
      PostSecondState.step PostSecondState.selected
          (markerLetter selected protector (some terminator) protector) =
        PostSecondState.protector := by
    simp [markerLetter, Ne.symm selectedNeProtector,
      PostSecondState.step]
  rw [seesProtector]
  rw [foldl_step_avoiding selected protector (some terminator) .protector
    middle selectedNotMiddle protectorNotMiddle (by
      intro final equality
      injection equality with finalEq
      simpa [finalEq] using terminatorNotMiddle)]
  have seesTerminator :
      PostSecondState.step PostSecondState.protector
          (markerLetter selected protector (some terminator) terminator) =
        PostSecondState.two := by
    simp [markerLetter, terminatorNeSelected, terminatorNeProtector,
      PostSecondState.step]
  rw [seesTerminator]
  exact foldl_step_two selected protector (some terminator) suffix

private theorem postSecondStateList_eq_protector_of_split
    (stem middle : List Nat) (selected protector : Nat)
    (selectedInStem : selected ∈ stem)
    (protectorNotStem : protector ∉ stem)
    (selectedNotMiddle : selected ∉ middle)
    (protectorNotMiddle : protector ∉ middle) :
    postSecondStateList (stem ++ [protector] ++ middle)
        selected protector none = .protector := by
  have selectedNeProtector : selected ≠ protector := by
    intro equal
    subst protector
    exact protectorNotStem selectedInStem
  unfold postSecondStateList
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [foldl_step_selected_of_mem selected protector none stem
    selectedInStem protectorNotStem (by simp)]
  have seesProtector :
      PostSecondState.step PostSecondState.selected
          (markerLetter selected protector none protector) =
        PostSecondState.protector := by
    simp [markerLetter, Ne.symm selectedNeProtector,
      PostSecondState.step]
  rw [seesProtector]
  exact foldl_step_avoiding selected protector none .protector middle
    selectedNotMiddle protectorNotMiddle (by simp)

private theorem exists_leftmost_split
    {value : Nat} {letters : List Nat}
    (member : value ∈ letters) :
    ∃ before after,
      letters = before ++ value :: after ∧ value ∉ before := by
  induction letters with
  | nil => simp at member
  | cons head tail induction =>
      by_cases equal : head = value
      · subst head
        exact ⟨[], tail, by simp⟩
      · have inTail : value ∈ tail := by
          rcases List.mem_cons.mp member with atHead | inTail
          · exact False.elim (equal atHead.symm)
          · exact inTail
        obtain ⟨before, after, shape, absent⟩ := induction inTail
        exact ⟨head :: before, after, by simp [shape], by
          simp [Ne.symm equal, absent]⟩

private theorem exists_block_marker_split
    {marker : Nat} {blocks : List FirstOccurrenceGapBlock}
    (member : marker ∈ gapBlockMarkers blocks) :
    ∃ beforeBlocks markerBlock afterBlocks,
      blocks = beforeBlocks ++ markerBlock :: afterBlocks ∧
        markerBlock.marker = marker := by
  obtain ⟨markerBlock, blockMember, markerEq⟩ := List.mem_map.mp member
  obtain ⟨beforeBlocks, afterBlocks, shape⟩ :=
    List.mem_iff_append.mp blockMember
  exact ⟨beforeBlocks, markerBlock, afterBlocks, shape, markerEq⟩

private theorem seen_not_mem_renderGapBlocks
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    {selected : Nat}
    (formed : GapBlocksWellFormed seen blocks)
    (selectedSeen : selected ∈ seen)
    (secondsAbsent : selected ∉ gapBlockSeconds blocks) :
    selected ∉ renderGapBlocks blocks := by
  intro rendered
  rcases (mem_renderGapBlocks_iff selected blocks).mp rendered with
    inMarkers | inSeconds
  · exact formed.markersAvoidSeen selected selectedSeen inMarkers
  · exact secondsAbsent inSeconds

private theorem ownMarker_not_mem_afterMarker
    {seen : List Nat} {block : FirstOccurrenceGapBlock}
    {rest : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen (block :: rest))
    (secondsAbsent :
      block.marker ∉ gapBlockSeconds (block :: rest)) :
    block.marker ∉ block.seconds ++ renderGapBlocks rest := by
  cases formed with
  | cons _ _ _ markerFresh secondsSeen tailFormed =>
      have currentSecondsAbsent : block.marker ∉ block.seconds := by
        intro member
        exact secondsAbsent <| by
          change block.marker ∈ block.seconds ++ gapBlockSeconds rest
          exact List.mem_append.mpr (Or.inl member)
      have restSecondsAbsent : block.marker ∉ gapBlockSeconds rest := by
        intro member
        exact secondsAbsent <| by
          change block.marker ∈ block.seconds ++ gapBlockSeconds rest
          exact List.mem_append.mpr (Or.inr member)
      have restMarkersAbsent : block.marker ∉ gapBlockMarkers rest :=
        tailFormed.markersAvoidSeen block.marker (List.Mem.head seen)
      intro member
      rcases List.mem_append.mp member with inCurrent | inRest
      · exact currentSecondsAbsent inCurrent
      · rcases (mem_renderGapBlocks_iff block.marker rest).mp inRest with
          inMarkers | inSeconds
        · exact restMarkersAbsent inMarkers
        · exact restSecondsAbsent inSeconds

private theorem postSecondProfiles_ne_of_split
    (left right stem leftMiddle leftSuffix rightMiddle : List Nat)
    (selected protector : Nat)
    (leftShape :
      left = stem ++ [protector] ++ leftMiddle ++ [selected] ++ leftSuffix)
    (selectedInStem : selected ∈ stem)
    (protectorNotStem : protector ∉ stem)
    (selectedNotLeftMiddle : selected ∉ leftMiddle)
    (protectorNotLeftMiddle : protector ∉ leftMiddle)
    (selectedNotRightMiddle : selected ∉ rightMiddle)
    (protectorNotRightMiddle : protector ∉ rightMiddle)
    (rightEnding :
      right = stem ++ [protector] ++ rightMiddle ∨
        ∃ terminator suffix,
          right = stem ++ [protector] ++ rightMiddle ++
              [terminator] ++ suffix ∧
            terminator ∉ stem ∧
            terminator ∉ leftMiddle ∧
            terminator ∉ rightMiddle ∧
            terminator ≠ selected ∧ terminator ≠ protector) :
    postSecondProfileList left ≠ postSecondProfileList right := by
  intro sameProfile
  rcases rightEnding with final | final
  · have stateEq := congrFun (congrFun (congrFun sameProfile selected)
        protector) none
    change postSecondStateList left selected protector none =
      postSecondStateList right selected protector none at stateEq
    have leftState := postSecondStateList_eq_zero_of_split
      stem leftMiddle leftSuffix selected protector none selectedInStem
      protectorNotStem (by simp) selectedNotLeftMiddle
      protectorNotLeftMiddle (by simp)
    have rightState := postSecondStateList_eq_protector_of_split
      stem rightMiddle selected protector selectedInStem protectorNotStem
      selectedNotRightMiddle protectorNotRightMiddle
    rw [leftShape, leftState, final, rightState] at stateEq
    cases stateEq
  · obtain ⟨terminator, suffix, rightShape, terminatorNotStem,
        terminatorNotLeft, terminatorNotRight, terminatorNeSelected,
        terminatorNeProtector⟩ := final
    have stateEq := congrFun (congrFun (congrFun sameProfile selected)
        protector) (some terminator)
    change postSecondStateList left selected protector (some terminator) =
      postSecondStateList right selected protector (some terminator) at stateEq
    have leftState := postSecondStateList_eq_zero_of_split
      stem leftMiddle leftSuffix selected protector (some terminator)
      selectedInStem protectorNotStem (by
        intro final equality
        injection equality with finalEq
        simpa [finalEq] using terminatorNotStem)
      selectedNotLeftMiddle protectorNotLeftMiddle (by
        intro final equality
        injection equality with finalEq
        simpa [finalEq] using terminatorNotLeft)
    have rightState := postSecondStateList_eq_two_of_split
      stem rightMiddle suffix selected protector terminator selectedInStem
      protectorNotStem terminatorNotStem selectedNotRightMiddle
      protectorNotRightMiddle terminatorNotRight terminatorNeSelected
      terminatorNeProtector
    rw [leftShape, leftState, rightShape, rightState] at stateEq
    cases stateEq

private theorem postSecondProfiles_ne_of_block_prefixes
    {priorBlocks : List FirstOccurrenceGapBlock}
    {leftBlock rightBlock : FirstOccurrenceGapBlock}
    {leftRest rightRest : List FirstOccurrenceGapBlock}
    (stem leftMiddle leftAfter rightMiddle : List Nat)
    (selected protector : Nat)
    (leftFormed :
      GapBlocksWellFormed [] (priorBlocks ++ leftBlock :: leftRest))
    (rightFormed :
      GapBlocksWellFormed [] (priorBlocks ++ rightBlock :: rightRest))
    (restMarkersEq :
      gapBlockMarkers leftRest = gapBlockMarkers rightRest)
    (leftPrefixShape :
      renderGapBlocks (priorBlocks ++ [leftBlock]) =
        stem ++ [protector] ++ leftMiddle ++ [selected] ++ leftAfter)
    (rightPrefixShape :
      renderGapBlocks (priorBlocks ++ [rightBlock]) =
        stem ++ [protector] ++ rightMiddle)
    (selectedInStem : selected ∈ stem)
    (protectorNotStem : protector ∉ stem)
    (selectedNotLeftMiddle : selected ∉ leftMiddle)
    (protectorNotLeftMiddle : protector ∉ leftMiddle)
    (selectedNotRightMiddle : selected ∉ rightMiddle)
    (protectorNotRightMiddle : protector ∉ rightMiddle) :
    postSecondProfileList
        (renderGapBlocks (priorBlocks ++ leftBlock :: leftRest)) ≠
      postSecondProfileList
        (renderGapBlocks (priorBlocks ++ rightBlock :: rightRest)) := by
  have leftWholeShape :
      renderGapBlocks (priorBlocks ++ leftBlock :: leftRest) =
        stem ++ [protector] ++ leftMiddle ++ [selected] ++
          (leftAfter ++ renderGapBlocks leftRest) := by
    rw [show priorBlocks ++ leftBlock :: leftRest =
        (priorBlocks ++ [leftBlock]) ++ leftRest by simp,
      renderGapBlocks_append, leftPrefixShape]
    simp [List.append_assoc]
  apply postSecondProfiles_ne_of_split
    (renderGapBlocks (priorBlocks ++ leftBlock :: leftRest))
    (renderGapBlocks (priorBlocks ++ rightBlock :: rightRest))
    stem leftMiddle (leftAfter ++ renderGapBlocks leftRest) rightMiddle
    selected protector leftWholeShape selectedInStem protectorNotStem
    selectedNotLeftMiddle protectorNotLeftMiddle selectedNotRightMiddle
    protectorNotRightMiddle
  cases leftRest with
  | nil =>
      cases rightRest with
      | nil =>
          exact Or.inl <| by
            simpa using rightPrefixShape
      | cons rightNext rightTail =>
          simp [S5_870.gapBlockMarkers] at restMarkersEq
  | cons leftNext leftTail =>
      cases rightRest with
      | nil =>
          simp [S5_870.gapBlockMarkers] at restMarkersEq
      | cons rightNext rightTail =>
          change
            leftNext.marker :: gapBlockMarkers leftTail =
              rightNext.marker :: gapBlockMarkers rightTail at restMarkersEq
          injection restMarkersEq with nextMarkerEq tailMarkersEq
          let terminator := leftNext.marker
          have leftNextFresh :
              terminator ∉
                renderGapBlocks (priorBlocks ++ [leftBlock]) := by
            exact futureMarker_not_mem_renderGapBlocks
              (priorBlocks := priorBlocks ++ [leftBlock])
              (nextBlock := leftNext) (rest := leftTail) <| by
                simpa [List.append_assoc] using leftFormed
          have rightNextFreshRaw :
              rightNext.marker ∉
                renderGapBlocks (priorBlocks ++ [rightBlock]) := by
            exact futureMarker_not_mem_renderGapBlocks
              (priorBlocks := priorBlocks ++ [rightBlock])
              (nextBlock := rightNext) (rest := rightTail) <| by
                simpa [List.append_assoc] using rightFormed
          have rightNextFresh :
              terminator ∉
                renderGapBlocks (priorBlocks ++ [rightBlock]) := by
            simpa [terminator, nextMarkerEq] using rightNextFreshRaw
          have terminatorNotStem : terminator ∉ stem := by
            intro member
            apply leftNextFresh
            rw [leftPrefixShape]
            simp [member]
          have terminatorNotLeft : terminator ∉ leftMiddle := by
            intro member
            apply leftNextFresh
            rw [leftPrefixShape]
            simp [member]
          have terminatorNotRight : terminator ∉ rightMiddle := by
            intro member
            apply rightNextFresh
            rw [rightPrefixShape]
            simp [member]
          have terminatorNeSelected : terminator ≠ selected := by
            intro equal
            exact terminatorNotStem <| by
              simpa [equal] using selectedInStem
          have terminatorNeProtector : terminator ≠ protector := by
            intro equal
            apply leftNextFresh
            have protectorInPrefix :
                protector ∈ renderGapBlocks
                  (priorBlocks ++ [leftBlock]) := by
              rw [leftPrefixShape]
              simp
            simpa [equal] using protectorInPrefix
          refine Or.inr ⟨terminator,
            rightNext.seconds ++ renderGapBlocks rightTail, ?_,
            terminatorNotStem, terminatorNotLeft, terminatorNotRight,
            terminatorNeSelected, terminatorNeProtector⟩
          rw [show priorBlocks ++ rightBlock :: rightNext :: rightTail =
              (priorBlocks ++ [rightBlock]) ++ rightNext :: rightTail by simp,
            renderGapBlocks_append, rightPrefixShape]
          simp [S5_870.renderGapBlocks, terminator, nextMarkerEq,
            List.append_assoc]

private theorem exists_protector_for_current_difference
    {priorBlocks : List FirstOccurrenceGapBlock}
    {leftBlock rightBlock : FirstOccurrenceGapBlock}
    {leftRest rightRest : List FirstOccurrenceGapBlock}
    {selected : Nat}
    (leftCanonical :
      CanonicalGapBlocks (priorBlocks ++ leftBlock :: leftRest))
    (rightCanonical :
      CanonicalGapBlocks (priorBlocks ++ rightBlock :: rightRest))
    (markerEq : leftBlock.marker = rightBlock.marker)
    (same :
      refinedGapSignatureList
          (renderGapBlocks (priorBlocks ++ leftBlock :: leftRest)) =
        refinedGapSignatureList
          (renderGapBlocks (priorBlocks ++ rightBlock :: rightRest)))
    (selectedInLeft : selected ∈ leftBlock.seconds)
    (selectedNotRight : selected ∉ rightBlock.seconds) :
    ∃ beforeBlocks firstBlock middle protector,
      priorBlocks = beforeBlocks ++ [firstBlock] ++ middle ∧
        selected ∈ firstBlock.seconds ∧
        selected ∉ gapBlockSeconds middle ∧
        protector ∈ gapBlockMarkers (middle ++ [leftBlock]) ∧
        protector ∉ gapBlockSeconds (middle ++ [leftBlock]) := by
  classical
  obtain ⟨markersEq, gapEq⟩ :=
    blockSignatureData_of_refined_eq leftCanonical.wellFormed
      rightCanonical.wellFormed same
  have selectedInSeconds :
      selected ∈ gapBlockSeconds
        (priorBlocks ++ leftBlock :: leftRest) := by
    rw [gapBlockSeconds_append]
    exact List.mem_append.mpr <| Or.inr <| by
      change selected ∈ leftBlock.seconds ++ gapBlockSeconds leftRest
      exact List.mem_append.mpr (Or.inl selectedInLeft)
  have selectedMarker :
      selected ∈ gapBlockMarkers
        (priorBlocks ++ leftBlock :: leftRest) := by
    rcases leftCanonical.wellFormed.secondsInSeenOrMarkers selected
        selectedInSeconds with inSeen | inMarkers
    · simp at inSeen
    · exact inMarkers
  have selectedGapEq := gapEq selected selectedMarker
  have selectedInPrior : selected ∈ gapBlockSeconds priorBlocks := by
    exact Classical.byContradiction (fun priorAbsent =>
      selectedNotRight <|
        (currentSeconds_mem_iff_of_no_prior markerEq priorAbsent
          selectedGapEq).mp selectedInLeft)
  obtain ⟨beforeBlocks, firstBlock, middle, priorShape,
      selectedInFirst, selectedNotMiddle⟩ :=
    exists_rightmost_block_second selectedInPrior
  have protectorExists :
      HasBlockProtector (middle ++ [leftBlock]) := by
    exact Classical.byContradiction (fun noProtector =>
      leftCanonical.occurrencesProtected ⟨beforeBlocks, firstBlock,
        middle, leftBlock, leftRest, selected, by
          rw [priorShape]
          simp [List.append_assoc], selectedInFirst, selectedInLeft,
        selectedNotMiddle, noProtector⟩)
  obtain ⟨protector, protectorMarker, protectorSeconds⟩ :=
    protectorExists
  exact ⟨beforeBlocks, firstBlock, middle, protector, priorShape,
    selectedInFirst, selectedNotMiddle, protectorMarker,
    protectorSeconds⟩

private theorem currentSeconds_mem_of_refined_eq
    {priorBlocks : List FirstOccurrenceGapBlock}
    {leftBlock rightBlock : FirstOccurrenceGapBlock}
    {leftRest rightRest : List FirstOccurrenceGapBlock}
    {selected : Nat}
    (leftCanonical :
      CanonicalGapBlocks (priorBlocks ++ leftBlock :: leftRest))
    (rightCanonical :
      CanonicalGapBlocks (priorBlocks ++ rightBlock :: rightRest))
    (markerEq : leftBlock.marker = rightBlock.marker)
    (same :
      refinedGapSignatureList
          (renderGapBlocks (priorBlocks ++ leftBlock :: leftRest)) =
        refinedGapSignatureList
          (renderGapBlocks (priorBlocks ++ rightBlock :: rightRest)))
    (selectedInLeft : selected ∈ leftBlock.seconds) :
    selected ∈ rightBlock.seconds := by
  classical
  apply Classical.byContradiction
  intro selectedNotRight
  obtain ⟨beforeBlocks, firstBlock, middle, protector, priorShape,
      selectedInFirst, selectedNotMiddle, protectorMarker,
      protectorSeconds⟩ :=
    exists_protector_for_current_difference leftCanonical rightCanonical
      markerEq same selectedInLeft selectedNotRight
  let leadingBlocks := beforeBlocks ++ [firstBlock]
  have leftFormedShape :
      GapBlocksWellFormed []
        (leadingBlocks ++ ((middle ++ [leftBlock]) ++ leftRest)) := by
    simpa [leadingBlocks, priorShape, List.append_assoc] using
      leftCanonical.wellFormed
  obtain ⟨leadingFormed, tailFormed⟩ :=
    gapBlocksWellFormed_append leftFormedShape
  obtain ⟨segmentFormed, leftRestFormed⟩ :=
    gapBlocksWellFormed_append tailFormed
  obtain ⟨middleFormed, currentFormed⟩ :=
    gapBlocksWellFormed_append segmentFormed
  have selectedSeen : selected ∈ seenAfter [] leadingBlocks :=
    selected_mem_seenAfter_of_last_second leadingFormed selectedInFirst
  have selectedNotRenderMiddle :
      selected ∉ renderGapBlocks middle :=
    seen_not_mem_renderGapBlocks middleFormed selectedSeen
      selectedNotMiddle
  have selectedNotSegmentMarkers :
      selected ∉ gapBlockMarkers (middle ++ [leftBlock]) :=
    segmentFormed.markersAvoidSeen selected selectedSeen
  have selectedNeCurrentMarker : selected ≠ leftBlock.marker := by
    intro equal
    subst selected
    exact selectedNotSegmentMarkers <| by
      simp [gapBlockMarkers_append, S5_870.gapBlockMarkers]
  obtain ⟨markersEq, gapEq⟩ :=
    blockSignatureData_of_refined_eq leftCanonical.wellFormed
      rightCanonical.wellFormed same
  have restMarkersEq :
      gapBlockMarkers leftRest = gapBlockMarkers rightRest := by
    rw [gapBlockMarkers_append, gapBlockMarkers_append] at markersEq
    simp only [S5_870.gapBlockMarkers, List.map_cons] at markersEq
    have tailsEq := List.append_cancel_left markersEq
    rw [markerEq] at tailsEq
    injection tailsEq
  have protectorNotLeading :
      protector ∉ renderGapBlocks leadingBlocks := by
    apply tailMarker_not_mem_renderGapBlocks leftFormedShape
    rw [gapBlockMarkers_append]
    exact List.mem_append.mpr (Or.inl protectorMarker)
  have protectorNotLeadingSeconds :
      protector ∉ gapBlockSeconds leadingBlocks := by
    intro member
    exact protectorNotLeading <|
      (mem_renderGapBlocks_iff protector leadingBlocks).mpr
        (Or.inr member)
  have protectorNotMiddleSeconds :
      protector ∉ gapBlockSeconds middle := by
    intro member
    exact protectorSeconds <| by
      rw [gapBlockSeconds_append]
      exact List.mem_append.mpr (Or.inl member)
  have protectorNotPriorSeconds :
      protector ∉ gapBlockSeconds priorBlocks := by
    rw [priorShape, gapBlockSeconds_append]
    intro member
    rcases List.mem_append.mp member with inLeading | inMiddle
    · exact protectorNotLeadingSeconds inLeading
    · exact protectorNotMiddleSeconds inMiddle
  have protectorNotLeftSeconds : protector ∉ leftBlock.seconds := by
    intro member
    exact protectorSeconds <| by
      rw [gapBlockSeconds_append]
      exact List.mem_append.mpr <| Or.inr <| by
        simpa [S5_870.gapBlockSeconds] using member
  have protectorMarkerWhole :
      protector ∈ gapBlockMarkers
        (priorBlocks ++ leftBlock :: leftRest) := by
    rw [show priorBlocks ++ leftBlock :: leftRest =
        leadingBlocks ++ ((middle ++ [leftBlock]) ++ leftRest) by
      simp [leadingBlocks, priorShape, List.append_assoc]]
    rw [gapBlockMarkers_append]
    apply List.mem_append.mpr
    apply Or.inr
    rw [gapBlockMarkers_append]
    exact List.mem_append.mpr (Or.inl protectorMarker)
  have protectorGapEq := gapEq protector protectorMarkerWhole
  have protectorNotRightSeconds :
      protector ∉ rightBlock.seconds := by
    intro member
    have inLeft :=
      (currentSeconds_mem_iff_of_no_prior markerEq
        protectorNotPriorSeconds protectorGapEq).mpr member
    exact protectorNotLeftSeconds inLeft
  have sameProfile :
      postSecondProfileList
          (renderGapBlocks (priorBlocks ++ leftBlock :: leftRest)) =
        postSecondProfileList
          (renderGapBlocks (priorBlocks ++ rightBlock :: rightRest)) :=
    congrArg RefinedGapSignature.postSecond same
  obtain ⟨secondBefore, secondAfter, leftSecondsShape,
      selectedNotSecondBefore⟩ :=
    exists_leftmost_split selectedInLeft
  by_cases protectorInMiddle : protector ∈ gapBlockMarkers middle
  · obtain ⟨blocksBeforeProtector, protectorBlock,
        blocksAfterProtector, middleShape, protectorBlockMarker⟩ :=
      exists_block_marker_split protectorInMiddle
    let stemBlocks := leadingBlocks ++ blocksBeforeProtector
    let stem := renderGapBlocks stemBlocks
    let commonMiddle := protectorBlock.seconds ++
      renderGapBlocks blocksAfterProtector ++ [leftBlock.marker]
    let leftMiddle := commonMiddle ++ secondBefore
    let rightMiddle :=
      (protectorBlock.seconds ++ renderGapBlocks blocksAfterProtector ++
        [rightBlock.marker]) ++ rightBlock.seconds
    have stemFormedShape :
        GapBlocksWellFormed []
          (stemBlocks ++ protectorBlock ::
            (blocksAfterProtector ++ leftBlock :: leftRest)) := by
      simpa [stemBlocks, leadingBlocks, priorShape, middleShape,
        List.append_assoc] using leftCanonical.wellFormed
    have selectedInStem : selected ∈ stem := by
      apply (mem_renderGapBlocks_iff selected stemBlocks).mpr
      apply Or.inr
      simp [stemBlocks, leadingBlocks, gapBlockSeconds_append,
        S5_870.gapBlockSeconds, selectedInFirst]
    have protectorNotStem : protector ∉ stem := by
      have absent := futureMarker_not_mem_renderGapBlocks stemFormedShape
      simpa [stem, protectorBlockMarker] using absent
    have selectedNotCommonMiddle : selected ∉ commonMiddle := by
      intro member
      rcases List.mem_append.mp member with inMiddleTail | atCurrentMarker
      · apply selectedNotRenderMiddle
        rw [middleShape, renderGapBlocks_append]
        exact List.mem_append.mpr <| Or.inr <| by
          change selected ∈ protectorBlock.marker ::
            (protectorBlock.seconds ++
              renderGapBlocks blocksAfterProtector)
          exact List.Mem.tail protectorBlock.marker inMiddleTail
      · have equal : selected = leftBlock.marker := by
          simpa using atCurrentMarker
        exact selectedNeCurrentMarker equal
    have selectedNotLeftMiddle : selected ∉ leftMiddle := by
      intro member
      rcases List.mem_append.mp member with inCommon | inBefore
      · exact selectedNotCommonMiddle inCommon
      · exact selectedNotSecondBefore inBefore
    have selectedNotRightMiddle : selected ∉ rightMiddle := by
      intro member
      rcases List.mem_append.mp member with inCommon | inRightSeconds
      · apply selectedNotCommonMiddle
        simpa [commonMiddle, markerEq, List.append_assoc] using inCommon
      · exact selectedNotRight inRightSeconds
    have throughCurrentFormed :
        GapBlocksWellFormed []
          (stemBlocks ++ protectorBlock ::
            (blocksAfterProtector ++ [leftBlock])) := by
      obtain ⟨formedPrefix, _⟩ := gapBlocksWellFormed_append
        (show GapBlocksWellFormed []
            ((stemBlocks ++ protectorBlock ::
                (blocksAfterProtector ++ [leftBlock])) ++ leftRest) by
          simpa [List.append_assoc] using stemFormedShape)
      exact formedPrefix
    obtain ⟨_, protectorTailFormed⟩ :=
      gapBlocksWellFormed_append throughCurrentFormed
    have protectorTailSecondsAbsent :
        protector ∉ gapBlockSeconds
          (protectorBlock :: (blocksAfterProtector ++ [leftBlock])) := by
      intro member
      apply protectorSeconds
      rw [middleShape]
      rw [show
        (blocksBeforeProtector ++
            protectorBlock :: blocksAfterProtector) ++ [leftBlock] =
          blocksBeforeProtector ++
            (protectorBlock :: (blocksAfterProtector ++ [leftBlock])) by
        simp [List.append_assoc]]
      rw [gapBlockSeconds_append]
      exact List.mem_append.mpr (Or.inr member)
    have protectorNotAfterMarkerRaw :=
      ownMarker_not_mem_afterMarker protectorTailFormed
        (by simpa [protectorBlockMarker] using protectorTailSecondsAbsent)
    have protectorNotAfterMarker :
        protector ∉
          protectorBlock.seconds ++ renderGapBlocks blocksAfterProtector ++
            [leftBlock.marker] ++ leftBlock.seconds := by
      simpa [protectorBlockMarker, renderGapBlocks_append,
        S5_870.renderGapBlocks, List.append_assoc] using
          protectorNotAfterMarkerRaw
    have protectorNotLeftMiddle : protector ∉ leftMiddle := by
      intro member
      apply protectorNotAfterMarker
      rcases List.mem_append.mp member with inCommon | inBefore
      · exact List.mem_append.mpr <| Or.inl <| by
          simpa [commonMiddle, List.append_assoc] using inCommon
      · apply List.mem_append.mpr
        apply Or.inr
        rw [leftSecondsShape]
        exact List.mem_append.mpr (Or.inl inBefore)
    have protectorNotRightMiddle : protector ∉ rightMiddle := by
      intro member
      rcases List.mem_append.mp member with inCommon | inRightSeconds
      · apply protectorNotAfterMarker
        exact List.mem_append.mpr <| Or.inl <| by
          simpa [markerEq, List.append_assoc] using inCommon
      · exact protectorNotRightSeconds inRightSeconds
    have leftPrefixShape :
        renderGapBlocks (priorBlocks ++ [leftBlock]) =
          stem ++ [protector] ++ leftMiddle ++ [selected] ++ secondAfter := by
      simp [priorShape, middleShape, leadingBlocks, stemBlocks, stem,
        commonMiddle, leftMiddle, leftSecondsShape,
        renderGapBlocks_append, S5_870.renderGapBlocks,
        protectorBlockMarker, List.append_assoc]
    have rightPrefixShape :
        renderGapBlocks (priorBlocks ++ [rightBlock]) =
          stem ++ [protector] ++ rightMiddle := by
      simp [priorShape, middleShape, leadingBlocks, stemBlocks, stem,
        rightMiddle, renderGapBlocks_append, S5_870.renderGapBlocks,
        protectorBlockMarker, markerEq, List.append_assoc]
    exact (postSecondProfiles_ne_of_block_prefixes stem leftMiddle
      secondAfter rightMiddle selected protector leftCanonical.wellFormed
      rightCanonical.wellFormed restMarkersEq leftPrefixShape
      rightPrefixShape selectedInStem protectorNotStem
      selectedNotLeftMiddle protectorNotLeftMiddle
      selectedNotRightMiddle protectorNotRightMiddle) sameProfile
  · have protectorAtCurrent : protector = leftBlock.marker := by
      rw [gapBlockMarkers_append] at protectorMarker
      rcases List.mem_append.mp protectorMarker with inMiddle | inCurrent
      · exact False.elim (protectorInMiddle inMiddle)
      · simpa [S5_870.gapBlockMarkers] using inCurrent
    let stem := renderGapBlocks priorBlocks
    let leftMiddle := secondBefore
    let rightMiddle := rightBlock.seconds
    have selectedInStem : selected ∈ stem := by
      apply (mem_renderGapBlocks_iff selected priorBlocks).mpr
      exact Or.inr <| by
        rw [priorShape, gapBlockSeconds_append]
        exact List.mem_append.mpr <| Or.inl <| by
          simp [leadingBlocks, gapBlockSeconds_append,
            S5_870.gapBlockSeconds, selectedInFirst]
    have protectorNotStem : protector ∉ stem := by
      have absent := futureMarker_not_mem_renderGapBlocks
        (priorBlocks := priorBlocks) (nextBlock := leftBlock)
        (rest := leftRest) leftCanonical.wellFormed
      simpa [stem, protectorAtCurrent] using absent
    have selectedNotLeftMiddle : selected ∉ leftMiddle :=
      selectedNotSecondBefore
    have protectorNotLeftMiddle : protector ∉ leftMiddle := by
      intro member
      exact protectorNotLeftSeconds <| by
        rw [leftSecondsShape]
        exact List.mem_append.mpr (Or.inl member)
    have selectedNotRightMiddle : selected ∉ rightMiddle :=
      selectedNotRight
    have protectorNotRightMiddle : protector ∉ rightMiddle :=
      protectorNotRightSeconds
    have leftPrefixShape :
        renderGapBlocks (priorBlocks ++ [leftBlock]) =
          stem ++ [protector] ++ leftMiddle ++ [selected] ++ secondAfter := by
      simp [stem, leftMiddle, leftSecondsShape, renderGapBlocks_append,
        S5_870.renderGapBlocks, protectorAtCurrent, List.append_assoc]
    have rightPrefixShape :
        renderGapBlocks (priorBlocks ++ [rightBlock]) =
          stem ++ [protector] ++ rightMiddle := by
      simp [stem, rightMiddle, renderGapBlocks_append,
        S5_870.renderGapBlocks, protectorAtCurrent, markerEq,
        List.append_assoc]
    exact (postSecondProfiles_ne_of_block_prefixes stem leftMiddle
      secondAfter rightMiddle selected protector leftCanonical.wellFormed
      rightCanonical.wellFormed restMarkersEq leftPrefixShape
      rightPrefixShape selectedInStem protectorNotStem
      selectedNotLeftMiddle protectorNotLeftMiddle
      selectedNotRightMiddle protectorNotRightMiddle) sameProfile

private theorem normalGapBlock_eq_of_support
    {left right : FirstOccurrenceGapBlock}
    (leftNormal : normalizeGapBlock left = left)
    (rightNormal : normalizeGapBlock right = right)
    (markerEq : left.marker = right.marker)
    (sameSupport :
      ∀ selected, selected ∈ left.seconds ↔ selected ∈ right.seconds) :
    left = right := by
  cases left with
  | mk leftMarker leftSeconds =>
      cases right with
      | mk rightMarker rightSeconds =>
          simp only [S5_870.FirstOccurrenceGapBlock.marker] at markerEq
          subst rightMarker
          have canonicalEq :=
            canonicalSeconds_eq_of_mem_iff leftMarker sameSupport
          have leftSecondsEq := congrArg
            S5_870.FirstOccurrenceGapBlock.seconds leftNormal
          have rightSecondsEq := congrArg
            S5_870.FirstOccurrenceGapBlock.seconds rightNormal
          change canonicalSeconds leftMarker leftSeconds = leftSeconds at leftSecondsEq
          change canonicalSeconds leftMarker rightSeconds = rightSeconds at rightSecondsEq
          exact congrArg
            (S5_870.FirstOccurrenceGapBlock.mk leftMarker)
            (leftSecondsEq.symm.trans (canonicalEq.trans rightSecondsEq))

private theorem canonicalGapBlocks_suffix_eq :
    ∀ (left priorBlocks right : List FirstOccurrenceGapBlock),
      CanonicalGapBlocks (priorBlocks ++ left) →
        CanonicalGapBlocks (priorBlocks ++ right) →
          refinedGapSignatureList
              (renderGapBlocks (priorBlocks ++ left)) =
            refinedGapSignatureList
              (renderGapBlocks (priorBlocks ++ right)) →
            left = right := by
  intro left
  induction left with
  | nil =>
      intro priorBlocks right leftCanonical rightCanonical same
      cases right with
      | nil => rfl
      | cons rightBlock rightRest =>
          obtain ⟨markersEq, _⟩ :=
            blockSignatureData_of_refined_eq leftCanonical.wellFormed
              rightCanonical.wellFormed same
          rw [gapBlockMarkers_append, gapBlockMarkers_append] at markersEq
          simp only [S5_870.gapBlockMarkers, List.map_nil, List.map_cons,
            List.append_nil] at markersEq
          have lengths := congrArg List.length markersEq
          simp only [List.length_map, List.length_append,
            List.length_cons] at lengths
          omega
  | cons leftBlock leftRest induction =>
      intro priorBlocks right leftCanonical rightCanonical same
      cases right with
      | nil =>
          obtain ⟨markersEq, _⟩ :=
            blockSignatureData_of_refined_eq leftCanonical.wellFormed
              rightCanonical.wellFormed same
          rw [gapBlockMarkers_append, gapBlockMarkers_append] at markersEq
          simp only [S5_870.gapBlockMarkers, List.map_nil, List.map_cons,
            List.append_nil] at markersEq
          have lengths := congrArg List.length markersEq
          simp only [List.length_map, List.length_append,
            List.length_cons] at lengths
          omega
      | cons rightBlock rightRest =>
          obtain ⟨markersEq, _⟩ :=
            blockSignatureData_of_refined_eq leftCanonical.wellFormed
              rightCanonical.wellFormed same
          rw [gapBlockMarkers_append, gapBlockMarkers_append] at markersEq
          simp only [S5_870.gapBlockMarkers, List.map_cons] at markersEq
          have currentAndRest := List.append_cancel_left markersEq
          injection currentAndRest with markerEq restMarkersEq
          have sameSupport :
              ∀ selected,
                selected ∈ leftBlock.seconds ↔
                  selected ∈ rightBlock.seconds := by
            intro selected
            constructor
            · exact currentSeconds_mem_of_refined_eq leftCanonical
                rightCanonical markerEq same
            · exact currentSeconds_mem_of_refined_eq rightCanonical
                leftCanonical markerEq.symm same.symm
          have leftNormal := leftCanonical.normal leftBlock <| by
            exact List.mem_append.mpr <| Or.inr <|
              List.Mem.head leftRest
          have rightNormal := rightCanonical.normal rightBlock <| by
            exact List.mem_append.mpr <| Or.inr <|
              List.Mem.head rightRest
          have currentEq := normalGapBlock_eq_of_support leftNormal
            rightNormal markerEq sameSupport
          subst rightBlock
          have leftTailCanonical :
              CanonicalGapBlocks
                ((priorBlocks ++ [leftBlock]) ++ leftRest) := by
            simpa [List.append_assoc] using leftCanonical
          have rightTailCanonical :
              CanonicalGapBlocks
                ((priorBlocks ++ [leftBlock]) ++ rightRest) := by
            simpa [List.append_assoc] using rightCanonical
          have tailSame :
              refinedGapSignatureList
                  (renderGapBlocks
                    ((priorBlocks ++ [leftBlock]) ++ leftRest)) =
                refinedGapSignatureList
                  (renderGapBlocks
                    ((priorBlocks ++ [leftBlock]) ++ rightRest)) := by
            simpa [List.append_assoc] using same
          exact congrArg (List.cons leftBlock) <|
            induction (priorBlocks ++ [leftBlock]) rightRest
              leftTailCanonical rightTailCanonical tailSame

/-- The refined signature is injective on canonical condition-(IV) block
lists. -/
theorem canonicalGapBlocks_eq_of_refinedGapSignatureList_eq
    {left right : List FirstOccurrenceGapBlock}
    (leftCanonical : CanonicalGapBlocks left)
    (rightCanonical : CanonicalGapBlocks right)
    (same :
      refinedGapSignatureList (renderGapBlocks left) =
        refinedGapSignatureList (renderGapBlocks right)) :
    left = right := by
  exact canonicalGapBlocks_suffix_eq left [] right (by
    simpa using leftCanonical) (by simpa using rightCanonical) (by
      simpa using same)

/-- Canonical condition-(IV) representatives with the same refined signature
are literally equal. -/
theorem protectedCanonicalList_eq_of_refinedGapSignatureList_eq
    {left right : List Nat}
    (leftCanonical : IsProtectedCanonicalList left)
    (rightCanonical : IsProtectedCanonicalList right)
    (same : refinedGapSignatureList left = refinedGapSignatureList right) :
    left = right := by
  obtain ⟨leftBlocks, leftShape, leftBlocksCanonical⟩ := leftCanonical
  obtain ⟨rightBlocks, rightShape, rightBlocksCanonical⟩ := rightCanonical
  subst left
  subst right
  exact congrArg renderGapBlocks <|
    canonicalGapBlocks_eq_of_refinedGapSignatureList_eq
      leftBlocksCanonical rightBlocksCanonical same

/-- Equality of the refined signature is sufficient for list-level
derivability from the published seven-law basis. -/
theorem listDerives_of_refinedGapSignatureList_eq
    {left right : List Nat}
    (same : refinedGapSignatureList left = refinedGapSignatureList right) :
    S5_107.ListDerives basis left right := by
  obtain ⟨leftCanonical, leftDerives, leftForm⟩ :=
    exists_protectedCanonicalList left
  obtain ⟨rightCanonical, rightDerives, rightForm⟩ :=
    exists_protectedCanonicalList right
  have canonicalSame :
      refinedGapSignatureList leftCanonical =
        refinedGapSignatureList rightCanonical :=
    (refinedGapSignatureList_eq_of_listDerives leftDerives).symm.trans <|
      same.trans <|
        refinedGapSignatureList_eq_of_listDerives rightDerives
  have canonicalEq :=
    protectedCanonicalList_eq_of_refinedGapSignatureList_eq
      leftForm rightForm canonicalSame
  subst rightCanonical
  exact leftDerives.trans rightDerives.symm

/-- Converse to refined-signature soundness: the refined gap signature is a
complete invariant for the published seven-law basis. -/
theorem derives_of_refinedGapSignature_eq
    {left right : Word Nat}
    (same : refinedGapSignature left = refinedGapSignature right) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          have listSame :
              refinedGapSignatureList (leftHead :: leftTail) =
                refinedGapSignatureList (rightHead :: rightTail) := by
            simpa using same
          simpa [S5_107.listWordOfCons] using
            S5_107.ListDerives.toWord
              (listDerives_of_refinedGapSignatureList_eq listSame)

end SemigroupBasis.CoRoots.Order6PublishedMonoid15

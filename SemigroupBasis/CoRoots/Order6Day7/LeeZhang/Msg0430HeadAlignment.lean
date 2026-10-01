import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0430FixedHead

/-! The pair's additional unrestricted move: any repeated initial letter can
be replaced by another repeated letter. The proof separates the two terminal
coincidences, so it never duplicates a letter whose second occurrence is the
observable final occurrence. Only the approved expansion, interior swap and
five-letter head move are used. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0430

open SemigroupBasis Examples

def frame (head : Nat) (middle : List Nat) (final : Nat) : Word Nat :=
  wordOfPrefixFinal (head :: middle) final

theorem frame_toList (head : Nat) (middle : List Nat) (final : Nat) :
    (frame head middle final).toList = head :: (middle ++ [final]) := by
  exact toList_wordOfPrefixFinal (head :: middle) final

theorem frame_head (head : Nat) (middle : List Nat) (final : Nat) :
    (frame head middle final).head = head := rfl

theorem frame_eq (head : Nat) (middle : List Nat) (final : Nat) :
    frame head middle final = Word.mk head middle ++ Word.singleton final := by
  apply Word.toList_injective
  rw [frame_toList, Word.toList_append, Word.toList_singleton]
  rfl

theorem exposeOne (middle : List Nat) (letter : Nat) (present : letter ∈ middle) :
    ∃ rest, middle.Perm (letter :: rest) :=
  ⟨middle.erase letter, List.perm_cons_erase present⟩

theorem exposeTwo (middle : List Nat) (letter : Nat) (repeated : 2 ≤ middle.count letter) :
    ∃ rest, middle.Perm (letter :: letter :: rest) := by
  obtain ⟨afterFirst, first⟩ := exposeOne middle letter (List.count_pos_iff.mp (by omega))
  have countFirst := first.count_eq letter
  simp only [List.count_cons_self] at countFirst
  obtain ⟨rest, second⟩ := exposeOne afterFirst letter (List.count_pos_iff.mp (by omega))
  exact ⟨rest, first.trans (List.Perm.cons letter second)⟩

/-- If the old head is also final, the new repeated letter is wholly in the
middle. A temporary third new-letter copy supplies the nonempty shift block. -/
theorem align_last_is_head (head next : Nat) (middle : List Nat)
    (repeated : 2 ≤ middle.count next) :
    ∃ target : Word Nat, target.head = next ∧ Derives pairBasis (frame head middle head) target := by
  obtain ⟨rest, expose⟩ := exposeTwo middle next repeated
  have arrange := pairFixedHeadRules.middlePermutation head head expose
  have expand : Derives pairBasis (frame head (next :: next :: rest) head)
      (frame head (next :: next :: next :: rest) head) := by
    simpa only [frame, wordOfPrefixFinal_cons, Word.append_assoc] using
      Derives.prepend (Word.singleton head)
        (pairExpansion (Word.singleton next) (wordOfPrefixFinal rest head))
  have permutation : (next :: next :: next :: rest).Perm (next :: (rest ++ [next, next])) := by
    simpa only [List.cons_append, List.nil_append] using
      (List.perm_append_comm (l₁ := [next, next]) (l₂ := next :: rest))
  have move := pairFixedHeadRules.middlePermutation head head permutation
  let target := Word.singleton next ++ Word.singleton next ++ Word.singleton head ++ Word.mk next rest ++ Word.singleton head
  have shift : Derives pairBasis (frame head (next :: (rest ++ [next, next])) head) target := by
    have shape : frame head (next :: (rest ++ [next, next])) head =
        Word.singleton head ++ Word.mk next rest ++ Word.singleton next ++ Word.singleton next ++ Word.singleton head := by
      apply Word.toList_injective
      rw [frame_toList]
      simp only [Word.toList_append, Word.toList_singleton]
      simp [Word.toList, List.append_assoc]
    rw [shape]
    exact pairHeadShift (Word.singleton head) (Word.mk next rest) (Word.singleton next)
  exact ⟨target, rfl, arrange.trans (expand.trans (move.trans shift))⟩

/-- If the new head is final, its single middle occurrence is retained.
Only the old repeated head is temporarily duplicated. -/
theorem align_last_is_new (head next : Nat) (middle : List Nat)
    (different : head ≠ next) (headPresent : head ∈ middle) (nextPresent : next ∈ middle) :
    ∃ target : Word Nat, target.head = next ∧ Derives pairBasis (frame head middle next) target := by
  obtain ⟨afterNext, first⟩ := exposeOne middle next nextPresent
  have oldPresent : head ∈ afterNext := by
    have transferred := first.mem_iff.mp headPresent
    simpa only [List.mem_cons, different, false_or] using transferred
  obtain ⟨rest, second⟩ := exposeOne afterNext head oldPresent
  have expose := first.trans (List.Perm.cons next second)
  have arrange := pairFixedHeadRules.middlePermutation head next expose
  have duplicate := pairFixedHeadRules.duplicateInitial head next (next :: head :: rest) (by simp)
  let target := Word.singleton next ++ Word.mk head rest ++ Word.singleton head ++ Word.singleton head ++ Word.singleton next
  have shift : Derives pairBasis (frame head (head :: next :: head :: rest) next) target := by
    simpa [target, frame_eq, Word.singleton, Word.append, List.append_assoc] using
      (pairHeadShift (Word.singleton next) (Word.mk head rest) (Word.singleton head)).symm
  exact ⟨target, rfl, arrange.trans (duplicate.trans shift)⟩

/-- When neither head equals the final letter, expose the short head-move
pattern before a genuine nonempty suffix; the terminal is untouched. -/
theorem align_last_is_other (head next final : Nat) (middle : List Nat)
    (different : head ≠ next) (headPresent : head ∈ middle) (nextRepeated : 2 ≤ middle.count next) :
    ∃ target : Word Nat, target.head = next ∧ Derives pairBasis (frame head middle final) target := by
  obtain ⟨afterNext, first⟩ := exposeTwo middle next nextRepeated
  have oldPresent : head ∈ afterNext := by
    have transferred := first.mem_iff.mp headPresent
    simpa only [List.mem_cons, different, false_or] using transferred
  obtain ⟨rest, second⟩ := exposeOne afterNext head oldPresent
  have expose := first.trans (List.Perm.cons next (List.Perm.cons next second))
  have arrange := pairFixedHeadRules.middlePermutation head final expose
  have duplicate := pairFixedHeadRules.duplicateInitial head final (next :: next :: head :: rest) (by simp)
  have shift : Derives pairBasis (frame head (head :: next :: next :: head :: rest) final)
      (frame next (next :: head :: head :: head :: rest) final) := by
    simpa only [frame, wordOfPrefixFinal_cons, Word.append_assoc] using
      (pairHeadShift (Word.singleton head) (Word.singleton head) (Word.singleton next)).appendRight
        (wordOfPrefixFinal rest final)
  exact ⟨frame next (next :: head :: head :: head :: rest) final, rfl,
    arrange.trans (duplicate.trans shift)⟩

theorem retarget_frame (head next final : Nat) (middle : List Nat)
    (headRepeated : 2 ≤ (frame head middle final).toList.count head)
    (nextRepeated : 2 ≤ (frame head middle final).toList.count next) :
    ∃ target : Word Nat, target.head = next ∧ Derives pairBasis (frame head middle final) target := by
  by_cases equal : head = next
  · subst next
    exact ⟨frame head middle final, rfl, Derives.refl _⟩
  by_cases lastIsHead : final = head
  · subst final
    have count : 2 ≤ middle.count next := by
      simpa [frame_toList, equal, Ne.symm equal, List.count_append] using nextRepeated
    exact align_last_is_head head next middle count
  have oldPresent : head ∈ middle := by
    have bound : 2 ≤ middle.count head + 1 := by
      simpa [frame_toList, List.count_append, lastIsHead] using headRepeated
    exact List.count_pos_iff.mp (by omega)
  by_cases lastIsNext : final = next
  · subst final
    have newPresent : next ∈ middle := by
      have bound : 2 ≤ middle.count next + 1 := by
        simpa [frame_toList, equal, List.count_append] using nextRepeated
      exact List.count_pos_iff.mp (by omega)
    exact align_last_is_new head next middle equal oldPresent newPresent
  · have count : 2 ≤ middle.count next := by
      simpa [frame_toList, equal, List.count_append, lastIsNext] using nextRepeated
    exact align_last_is_other head next final middle equal oldPresent count

/-- The unrestricted word form of repeated-head alignment. -/
theorem retargetRepeatedHead (word : Word Nat) (next : Nat)
    (headRepeated : 2 ≤ word.toList.count word.head)
    (nextRepeated : 2 ≤ word.toList.count next) :
    ∃ target : Word Nat, target.head = next ∧ Derives pairBasis word target := by
  rcases word with ⟨head, tail⟩
  cases tail with
  | nil => simp [Word.toList] at headRepeated
  | cons following rest =>
      let suffix := Word.mk following rest
      have shape : Word.mk head (following :: rest) =
          frame head (splitPrefixFinal suffix).1 (splitPrefixFinal suffix).2 := by
        rw [frame, wordOfPrefixFinal_cons, wordOfPrefixFinal_split]
        rfl
      rw [shape] at headRepeated nextRepeated ⊢
      exact retarget_frame head next (splitPrefixFinal suffix).2 (splitPrefixFinal suffix).1
        headRepeated nextRepeated

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0430

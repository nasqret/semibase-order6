import SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section02.Section02Replay

/-! Explicit repeated-final append moves. Only letters occurring in the tail
may be appended: a globally simple initial letter is never duplicated. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section02.Section02FinalMoves

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section02.Section02Replay

abbrev basis := Section02Replay.basis

private theorem bind_singleton (word : Word Nat) : word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

theorem replayLower {left right : Word Nat} (derivation : Derives lowerBasis left right)
    (guard : Word Nat) : Derives basis (left ++ guard) (right ++ guard) := by
  simpa only [bind_singleton] using liftLower derivation guard Word.singleton

theorem duplicateRepeatedFinal (pre : List Nat) (t : Nat) (member : t ∈ pre) :
    D (pre ++ [t]) ((pre ++ [t]) ++ [t]) := by
  obtain ⟨before, middle, rfl⟩ := List.mem_iff_append.mp member
  cases middle with
  | nil =>
      simpa [Word.toList, Word.singleton, Word.append, List.append_assoc] using
        (ListDerives.ofWord (rawPower (Word.singleton t))).prepend before
  | cons q qs =>
      simpa [Word.toList, Word.singleton, Word.append, List.append_assoc] using
        (ListDerives.ofWord (rawReturnDuplicate (Word.singleton t) (Word.mk q qs))).prepend before

theorem appendFromTwoTailMembers (word : Word Nat) (t m : Nat)
    (tMember : t ∈ word.tail) (mMember : m ∈ word.tail) :
    Derives basis (word ++ Word.singleton t)
      ((word ++ Word.singleton t) ++ Word.singleton m) := by
  let tm := Word.singleton t
  let mm := Word.singleton m
  have absorbM : Derives lowerBasis (word ++ mm) word := lowerAbsorbTailMember word m mMember
  have absorbT : Derives lowerBasis (word ++ tm) word := lowerAbsorbTailMember word t tMember
  have two : Derives lowerBasis ((word ++ mm) ++ mm) word :=
    (Derives.appendRight absorbM mm).trans absorbM
  have keepT : Derives lowerBasis (((word ++ mm) ++ mm) ++ tm) (word ++ tm) :=
    Derives.appendRight two tm
  have drop : Derives lowerBasis (((word ++ mm) ++ mm) ++ tm) word := keepT.trans absorbT
  have first : Derives basis (word ++ tm) ((((word ++ mm) ++ mm) ++ tm) ++ tm) :=
    replayLower drop.symm tm
  have second : Derives basis ((((word ++ mm) ++ mm) ++ tm) ++ tm)
      ((((word ++ mm) ++ mm) ++ tm) ++ mm) := by
    simpa [Word.append_assoc] using Derives.prepend word (rawSquareFinalSwitch mm tm)
  have third : Derives basis ((((word ++ mm) ++ mm) ++ tm) ++ mm) ((word ++ tm) ++ mm) :=
    replayLower keepT mm
  exact first.trans (second.trans third)

/-- Expose a selected letter in the interior of a return to the head. The
initial extension ends at that letter; its preceding block is then absorbed
only in the lower calculus and replayed before the retained selected letter. -/
theorem returnInteriorAppend (head m : Nat) (before after : List Nat) :
    Derives basis (Word.mk head (before ++ m :: (after ++ [head])))
      (Word.mk head (before ++ m :: (after ++ [head])) ++ Word.singleton m) := by
  let word := Word.mk head (before ++ m :: (after ++ [head]))
  let selected := wordOfPrefixFinal before m
  have first : Derives basis word (word ++ selected) := by
    cases after with
    | nil =>
        have raw := rawReturnRepeat (Word.singleton head) selected
        have shape : (Word.singleton head ++ selected) ++ Word.singleton head = word := by
          apply Word.toList_injective
          simp only [Word.toList_append, Word.toList_singleton, selected, toList_wordOfPrefixFinal, word]
          simp [Word.toList, List.append_assoc]
        simpa only [shape] using raw
    | cons q qs =>
        have raw := rawReturnPrefixExtension (Word.singleton head) selected (Word.mk q qs)
        have shape : ((Word.singleton head ++ selected) ++ Word.mk q qs) ++ Word.singleton head = word := by
          apply Word.toList_injective
          simp only [Word.toList_append, Word.toList_singleton, selected, toList_wordOfPrefixFinal, word]
          simp [Word.toList, List.append_assoc]
        simpa only [shape] using raw
  cases before with
  | nil =>
      simpa [word, selected] using first
  | cons p ps =>
      have absorb : Derives lowerBasis (word ++ Word.mk p ps) word := by
        have shape : (Word.singleton head ++ Word.mk p ps) ++ Word.mk m (after ++ [head]) = word := by
          apply Word.toList_injective
          simp [word, Word.toList]
        simpa only [shape] using CoRoots.S5_869.derivesNoninitialRepeatDeletion
          (Word.singleton head) (Word.mk p ps) (Word.mk m (after ++ [head]))
      have selectedShape : selected = Word.mk p ps ++ Word.singleton m := by
        apply Word.toList_injective
        simp only [selected, toList_wordOfPrefixFinal, Word.toList_append, Word.toList_singleton]
        rfl
      have second : Derives basis (word ++ selected) (word ++ Word.singleton m) := by
        simpa only [selectedShape, Word.append_assoc] using replayLower absorb (Word.singleton m)
      exact first.trans second

theorem repeatedFinalAppend (head : Nat) (stem : List Nat) (t m : Nat)
    (lastMember : t ∈ head :: stem) (tailMember : m ∈ stem ++ [t]) :
    D ((head :: stem) ++ [t]) (((head :: stem) ++ [t]) ++ [m]) := by
  by_cases same : m = t
  · subst m
    exact duplicateRepeatedFinal (head :: stem) t lastMember
  have mMember : m ∈ stem := by simpa [same] using tailMember
  by_cases initial : t = head
  · subst t
    obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp mMember
    simpa [Word.toList, Word.append, Word.singleton, List.append_assoc] using
      ListDerives.ofWord (returnInteriorAppend head m before after)
  · have tMember : t ∈ stem := by simpa [initial] using lastMember
    simpa [Word.toList, Word.append, Word.singleton, List.append_assoc] using
      ListDerives.ofWord (appendFromTwoTailMembers (Word.mk head stem) t m tMember mMember)

theorem derivesAppendRepeatedFinal (word : Word Nat) (m : Nat)
    (repeated : (splitPrefixFinal word).2 ∈ (splitPrefixFinal word).1)
    (tailMember : m ∈ word.tail) :
    Derives basis word (word ++ Word.singleton m) := by
  let final := (splitPrefixFinal word).2
  cases prefixShape : (splitPrefixFinal word).1 with
  | nil => simp [prefixShape] at repeated
  | cons head stem =>
      have shape : Word.mk head (stem ++ [final]) = word := by
        apply Word.toList_injective
        rw [← wordOfPrefixFinal_split word, toList_wordOfPrefixFinal, prefixShape]
        rfl
      have repeatedStem : final ∈ head :: stem := by simpa [final, prefixShape] using repeated
      have member : m ∈ stem ++ [final] := by
        rw [← shape] at tailMember
        exact tailMember
      have listDerived := repeatedFinalAppend head stem final m repeatedStem member
      have derived : Derives basis (Word.mk head (stem ++ [final]))
          (Word.mk head (stem ++ [final]) ++ Word.singleton m) := listDerived.toWord
      simpa only [shape] using derived

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section02.Section02FinalMoves

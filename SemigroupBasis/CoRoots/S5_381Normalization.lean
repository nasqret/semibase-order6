import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_381Invariant

namespace SemigroupBasis.CoRoots.S5_381

open SemigroupBasis

private theorem s4_71Models :
    Models Generated.S4_71.table.semigroup basis :=
  models_of_finite_checks Generated.S4_71.table (by decide)

private theorem listDerivesGatherPair
    (pre : List Nat) (preNonempty : pre ≠ [])
    (letter : Nat) (middle suffix : List Nat) :
    S5_107.ListDerives basis
      (pre ++ [letter] ++ middle ++ [letter] ++ suffix)
      (pre ++ middle ++ [letter, letter] ++ suffix) := by
  cases middle with
  | nil =>
      simpa [List.append_assoc] using
        S5_107.ListDerives.refl
          (basis := basis) (pre ++ [letter, letter] ++ suffix)
  | cons middleHead middleTail =>
      obtain ⟨prefixHead, prefixTail, rfl⟩ :=
        List.exists_cons_of_ne_nil preNonempty
      have gathered :=
        S5_107.ListDerives.ofWord <|
          derivesPrefixedGather
            (S5_107.listWordOfCons prefixHead prefixTail)
            (Word.singleton letter)
            (S5_107.listWordOfCons middleHead middleTail)
      simpa [S5_107.listWordOfCons, Word.singleton,
        Word.append, List.append_assoc] using
        gathered.append suffix

private theorem listDerivesInitialSwitch
    (old new : Nat) (first second suffix : List Nat) :
    S5_107.ListDerives basis
      ([old] ++ first ++ [old] ++ second ++ [new, new] ++ suffix)
      ([new] ++ first ++ [old, old] ++ second ++ [new] ++ suffix) := by
  cases first with
  | nil =>
      cases second with
      | nil =>
          have switched :=
            S5_107.ListDerives.ofWord <|
              derivesInitialSwitchBothEmpty
                (Word.singleton old) (Word.singleton new)
          simpa [Word.singleton, Word.append, List.append_assoc] using
            switched.append suffix
      | cons secondHead secondTail =>
          have switched :=
            S5_107.ListDerives.ofWord <|
              derivesInitialSwitchFirstEmpty
                (Word.singleton old) (Word.singleton new)
                (S5_107.listWordOfCons secondHead secondTail)
          simpa [S5_107.listWordOfCons, Word.singleton,
            Word.append, List.append_assoc] using
            switched.append suffix
  | cons firstHead firstTail =>
      cases second with
      | nil =>
          have switched :=
            S5_107.ListDerives.ofWord <|
              derivesInitialSwitchSecondEmpty
                (Word.singleton old) (Word.singleton new)
                (S5_107.listWordOfCons firstHead firstTail)
          simpa [S5_107.listWordOfCons, Word.singleton,
            Word.append, List.append_assoc] using
            switched.append suffix
      | cons secondHead secondTail =>
          have switched :=
            S5_107.ListDerives.ofWord <|
              derivesInitialSwitchBoth
                (Word.singleton old) (Word.singleton new)
                (S5_107.listWordOfCons firstHead firstTail)
                (S5_107.listWordOfCons secondHead secondTail)
          simpa [S5_107.listWordOfCons, Word.singleton,
            Word.append, List.append_assoc] using
            switched.append suffix

private theorem split_two_occurrences (letter : Nat) :
    ∀ letters : List Nat,
      2 ≤ letters.count letter →
      ∃ before middle after,
        letters = before ++ letter :: middle ++ letter :: after
  | [], count => by
      simp at count
  | head :: tail, count => by
      by_cases headEq : head = letter
      · subst head
        have tailMember : letter ∈ tail := by
          apply List.count_pos_iff.mp
          simp only [List.count_cons_self] at count
          omega
        rcases List.append_of_mem tailMember with
          ⟨middle, after, tailShape⟩
        exact ⟨[], middle, after, by simp [tailShape]⟩
      · have tailCount : 2 ≤ tail.count letter := by
          rw [List.count_cons_of_ne headEq] at count
          exact count
        rcases split_two_occurrences letter tail tailCount with
          ⟨before, middle, after, tailShape⟩
        exact
          ⟨head :: before, middle, after, by
            simp [tailShape, List.append_assoc]⟩

/-- Replace a repeated initial variable by any other multiple variable.
The proof is constructive and uses only the seven advertised local chains:
gather the new variable at its second selected occurrence, then switch in
the direction determined by the remaining old-head occurrence. -/
theorem derivesRetargetMultipleHead
    (word : Word Nat) (new : Nat)
    (different : word.head ≠ new)
    (headRepeated : word.head ∈ word.tail)
    (newMultiple : 2 ≤ word.toList.count new) :
    ∃ switchedTail,
      Derives basis word (Word.mk new switchedTail) := by
  cases word with
  | mk old tail =>
      have tailNewCount : 2 ≤ tail.count new := by
        simpa only [Word.toList,
          List.count_cons_of_ne different] using
          newMultiple
      rcases split_two_occurrences new tail tailNewCount with
        ⟨before, middle, after, tailShape⟩
      let front := before ++ middle
      have gatherCore :=
        listDerivesGatherPair
          (old :: before) (by simp) new middle after
      have gathered :
          S5_107.ListDerives basis
            (old :: tail)
            (old :: front ++ [new, new] ++ after) := by
        rw [tailShape]
        simpa [front, List.append_assoc] using gatherCore
      by_cases oldInFront : old ∈ front
      · rcases List.append_of_mem oldInFront with
          ⟨first, second, frontShape⟩
        have switchCore :=
          listDerivesInitialSwitch old new first second after
        have switched :
            S5_107.ListDerives basis
              (old :: front ++ [new, new] ++ after)
              (new :: first ++ [old, old] ++ second ++ [new] ++ after) := by
          rw [frontShape]
          simpa [List.append_assoc] using switchCore
        let switchedTail :=
          first ++ [old, old] ++ second ++ [new] ++ after
        have complete :
            S5_107.ListDerives basis
              (old :: tail) (new :: switchedTail) := by
          simpa [switchedTail, List.append_assoc] using
            gathered.trans switched
        refine ⟨switchedTail, ?_⟩
        simpa [S5_107.listWordOfCons] using
          S5_107.ListDerives.toWord complete
      · have oldNotBefore : old ∉ before := by
          intro member
          exact oldInFront <|
            List.mem_append_left middle member
        have oldNotMiddle : old ∉ middle := by
          intro member
          exact oldInFront <|
            List.mem_append_right before member
        have oldInAfter : old ∈ after := by
          rw [tailShape] at headRepeated
          simp [oldNotBefore, oldNotMiddle, different] at headRepeated
          exact headRepeated
        rcases List.append_of_mem oldInAfter with
          ⟨second, suffix, afterShape⟩
        have switchCore :=
          (listDerivesInitialSwitch
            new old front second suffix).symm
        have switched :
            S5_107.ListDerives basis
              (old :: front ++ [new, new] ++ after)
              (new :: front ++ [new] ++ second ++ [old, old] ++ suffix) := by
          rw [afterShape]
          simpa [List.append_assoc] using switchCore
        let switchedTail :=
          front ++ [new] ++ second ++ [old, old] ++ suffix
        have complete :
            S5_107.ListDerives basis
              (old :: tail) (new :: switchedTail) := by
          simpa [switchedTail, List.append_assoc] using
            gathered.trans switched
        refine ⟨switchedTail, ?_⟩
        simpa [S5_107.listWordOfCons] using
          S5_107.ListDerives.toWord complete

private theorem head_mem_tail_of_count_ne_one
    (word : Word Nat)
    (countNotOne : word.toList.count word.head ≠ 1) :
    word.head ∈ word.tail := by
  apply Decidable.byContradiction
  intro absent
  apply countNotOne
  cases word with
  | mk head tail =>
      simp [Word.toList, List.count_eq_zero.mpr absent]

private theorem head_count_positive (word : Word Nat) :
    0 < word.toList.count word.head := by
  cases word
  simp [Word.toList]

private theorem cappedMultiplicity_eq_two_iff
    (word : Word Nat) (letter : Nat) :
    S5_107.cappedMultiplicity word letter = 2 ↔
      2 ≤ word.toList.count letter := by
  unfold S5_107.cappedMultiplicity
  simp only [Nat.min_def]
  split <;> omega

/-- Unrestricted normalization for the exact invariant. Equal heads are
handled by the transported S5_793 theorem. Distinct heads are necessarily
multiple; the left head is retargeted to the right head and the residual
same-head identity is again delegated to S5_793. -/
theorem derives_of_sameSimpleSequenceLastGapInitialSignature
    {left right : Word Nat}
    (same :
      S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
        left right) :
    Derives basis left right := by
  by_cases heads : left.head = right.head
  · exact transportS5_793Derivation <|
      SemigroupBasis.CoRoots.S5_793.derives_of_sameFirstSimpleLastGapSignature
        (same.toSameFirst heads)
  · have leftCountNotOne :
        left.toList.count left.head ≠ 1 := by
      intro countOne
      have leftSimple :
          S5_107.SimpleInitial left left.head :=
        ⟨countOne, rfl⟩
      have rightSimple :=
        (same.initial left.head).mp leftSimple
      exact heads rightSimple.2.symm
    have rightCountNotOne :
        right.toList.count right.head ≠ 1 := by
      intro countOne
      have rightSimple :
          S5_107.SimpleInitial right right.head :=
        ⟨countOne, rfl⟩
      have leftSimple :=
        (same.initial right.head).mpr rightSimple
      exact heads leftSimple.2
    have leftHeadRepeated :
        left.head ∈ left.tail :=
      head_mem_tail_of_count_ne_one left leftCountNotOne
    have rightHeadMultiple :
        2 ≤ right.toList.count right.head := by
      have positive := head_count_positive right
      omega
    have leftNewMultiple :
        2 ≤ left.toList.count right.head := by
      have rightCapped :
          S5_107.cappedMultiplicity right right.head = 2 :=
        (cappedMultiplicity_eq_two_iff right right.head).2
          rightHeadMultiple
      have leftCapped :
          S5_107.cappedMultiplicity left right.head = 2 :=
        (same.capped right.head).trans rightCapped
      exact
        (cappedMultiplicity_eq_two_iff left right.head).1
          leftCapped
    obtain ⟨switchedTail, switch⟩ :=
      derivesRetargetMultipleHead
        left right.head heads leftHeadRepeated leftNewMultiple
    let switched : Word Nat := Word.mk right.head switchedTail
    have residualBlock :
        (Identity.mk switched right).SatisfiedBy
          Generated.S4_71.table.semigroup := by
      intro valuation
      have switchSound :=
        switch.sound s4_71Models valuation
      exact switchSound.symm.trans (same.blockTheory valuation)
    have residualSame :
        S5_793Invariant.SameFirstSimpleLastGapSignature
          switched right :=
      S5_793Invariant.sameSignature_of_s4_71_valid_head_eq
        ⟨switched, right⟩ residualBlock rfl
    have residualDerivation :
        Derives basis switched right :=
      transportS5_793Derivation <|
        SemigroupBasis.CoRoots.S5_793.derives_of_sameFirstSimpleLastGapSignature
          residualSame
    exact switch.trans <| by
      simpa [switched] using residualDerivation

end SemigroupBasis.CoRoots.S5_381

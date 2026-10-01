import SemigroupBasis.CoRoots.S5_216

namespace SemigroupBasis.CoRoots.S5_216

open SemigroupBasis
open DirectCompletenessArchitecture

private theorem lengthState_spec (word : Word Nat) :
    (lengthState word = .one ↔ word.toList.length = 1) ∧
      (lengthState word = .two ↔ word.toList.length = 2) ∧
      (lengthState word = .three ↔ word.toList.length = 3) ∧
      (lengthState word = .long ↔ 4 ≤ word.toList.length) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [lengthState, Word.toList]
      | cons first tail =>
          cases tail with
          | nil =>
              simp [lengthState, Word.toList]
          | cons second tail =>
              cases tail with
              | nil =>
                  simp [lengthState, Word.toList]
              | cons third tail =>
                  simp [lengthState, Word.toList]

/-- The singleton length state is exactly total word length one. -/
theorem lengthState_eq_one_iff (word : Word Nat) :
    lengthState word = .one ↔ word.toList.length = 1 :=
  (lengthState_spec word).1

/-- The quadratic length state is exactly total word length two. -/
theorem lengthState_eq_two_iff (word : Word Nat) :
    lengthState word = .two ↔ word.toList.length = 2 :=
  (lengthState_spec word).2.1

/-- The cubic length state is exactly total word length three. -/
theorem lengthState_eq_three_iff (word : Word Nat) :
    lengthState word = .three ↔ word.toList.length = 3 :=
  (lengthState_spec word).2.2.1

/-- The long length state is exactly total word length at least four. -/
theorem lengthState_eq_long_iff (word : Word Nat) :
    lengthState word = .long ↔ 4 ≤ word.toList.length :=
  (lengthState_spec word).2.2.2

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- Compatibility name for the four-block collapse supplied by the basis
foundation. -/
theorem derivesFourBlockCollapse (u v z t : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ t)
      (((u ++ u) ++ u) ++ u) :=
  derivesLongToHeadFourth u v z t

/-- Every permutation of the tail is derivable while the head stays fixed. -/
private theorem derivesTailPermutation (head : Nat) {xs ys : List Nat}
    (permutation : xs.Perm ys) :
    Derives basis (wordOfCons head xs) (wordOfCons head ys) := by
  induction permutation generalizing head with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      have suffix := ih (head := x)
      simpa [wordOfCons, Word.singleton, Word.append] using
        Derives.prepend (Word.singleton head) suffix
  | swap x y xs =>
      cases xs with
      | nil =>
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using
              derivesTailSwap
                (Word.singleton head) (Word.singleton y)
                (Word.singleton x)
      | cons z zs =>
          have swapped :=
            Derives.appendRight
              (derivesTailSwap
                (Word.singleton head) (Word.singleton y)
                (Word.singleton x))
              (wordOfCons z zs)
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using swapped
  | trans _ _ ihFirst ihSecond =>
      exact Derives.trans (ihFirst (head := head))
        (ihSecond (head := head))

private theorem derivesTripleTwoSupport
    (head other second third : Nat) (different : head ≠ other)
    (support :
      ∀ letter,
        letter ∈ [head, second, third] ↔
          letter = head ∨ letter = other) :
    Derives basis
      (wordOfCons head [second, third])
      (wordOfCons head [head, other]) := by
  have otherMember : other ∈ [head, second, third] :=
    (support other).mpr (Or.inr rfl)
  have secondClass : second = head ∨ second = other :=
    (support second).mp (by simp)
  have thirdClass : third = head ∨ third = other :=
    (support third).mp (by simp)
  rcases secondClass with secondHead | secondOther
  · subst second
    rcases thirdClass with thirdHead | thirdOther
    · subst third
      have equal : other = head := by
        simpa using otherMember
      exact False.elim (different equal.symm)
    · subst third
      exact Derives.refl _
  · subst second
    rcases thirdClass with thirdHead | thirdOther
    · subst third
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using
          Derives.symm
            (derivesFirstRepeatToMiddle
              (Word.singleton head) (Word.singleton other))
    · subst third
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using
          Derives.symm
            (derivesFirstRepeatToTail
              (Word.singleton head) (Word.singleton other))

private theorem nodupPerm
    {xs ys : List Nat} (xsNodup : xs.Nodup) (ysNodup : ys.Nodup)
    (support : ∀ letter, letter ∈ xs ↔ letter ∈ ys) :
    xs.Perm ys := by
  rw [List.perm_iff_count]
  intro letter
  rw [xsNodup.count, ysNodup.count]
  simp only [support letter]

private theorem tripleNodup_of_support
    {a b c d e f : Nat}
    (sourceNodup : [a, b, c].Nodup)
    (support :
      ∀ letter, letter ∈ [a, b, c] ↔ letter ∈ [d, e, f]) :
    [d, e, f].Nodup := by
  have ha : a = d ∨ a = e ∨ a = f := by
    simpa using (support a).mp (by simp)
  have hb : b = d ∨ b = e ∨ b = f := by
    simpa using (support b).mp (by simp)
  have hc : c = d ∨ c = e ∨ c = f := by
    simpa using (support c).mp (by simp)
  rcases ha with ha | ha | ha <;>
    rcases hb with hb | hb | hb <;>
    rcases hc with hc | hc | hc <;>
    simp_all [eq_comm]

private theorem derivesTripleOfHeadSupportEq
    (a b c d e f : Nat) (heads : a = d)
    (support :
      ∀ letter, letter ∈ [a, b, c] ↔ letter ∈ [d, e, f]) :
    Derives basis
      (wordOfCons a [b, c]) (wordOfCons d [e, f]) := by
  subst d
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      have he : e = a := by
        have member := (support e).mpr (by simp)
        simpa using member
      have hf : f = a := by
        have member := (support f).mpr (by simp)
        simpa using member
      subst e
      subst f
      exact Derives.refl _
    · have sourceSupport :
          ∀ letter,
            letter ∈ [a, a, c] ↔ letter = a ∨ letter = c := by
        intro letter
        simp [or_assoc, or_left_comm, or_comm]
      have targetSupport :
          ∀ letter,
            letter ∈ [a, e, f] ↔ letter = a ∨ letter = c := by
        intro letter
        exact (support letter).symm.trans (sourceSupport letter)
      have left :=
        derivesTripleTwoSupport a c a c hac sourceSupport
      have right :=
        derivesTripleTwoSupport a c e f hac targetSupport
      exact Derives.trans left (Derives.symm right)
  · by_cases hac : a = c
    · subst c
      have sourceSupport :
          ∀ letter,
            letter ∈ [a, b, a] ↔ letter = a ∨ letter = b := by
        intro letter
        simp [or_assoc, or_left_comm, or_comm]
      have targetSupport :
          ∀ letter,
            letter ∈ [a, e, f] ↔ letter = a ∨ letter = b := by
        intro letter
        exact (support letter).symm.trans (sourceSupport letter)
      have left :=
        derivesTripleTwoSupport a b b a hab sourceSupport
      have right :=
        derivesTripleTwoSupport a b e f hab targetSupport
      exact Derives.trans left (Derives.symm right)
    · by_cases hbc : b = c
      · subst c
        have sourceSupport :
            ∀ letter,
              letter ∈ [a, b, b] ↔ letter = a ∨ letter = b := by
          intro letter
          simp [or_assoc, or_left_comm, or_comm]
        have targetSupport :
            ∀ letter,
              letter ∈ [a, e, f] ↔ letter = a ∨ letter = b := by
          intro letter
          exact (support letter).symm.trans (sourceSupport letter)
        have left :=
          derivesTripleTwoSupport a b b b hab sourceSupport
        have right :=
          derivesTripleTwoSupport a b e f hab targetSupport
        exact Derives.trans left (Derives.symm right)
      · have sourceNodup : [a, b, c].Nodup := by
          simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac,
            Ne.symm hbc]
        have targetNodup :=
          tripleNodup_of_support sourceNodup support
        have tailSupport :
            ∀ letter, letter ∈ [b, c] ↔ letter ∈ [e, f] := by
          intro letter
          by_cases equal : letter = a
          · subst letter
            have leftAbsent : a ∉ [b, c] := by
              simpa using (List.nodup_cons.mp sourceNodup).1
            have rightAbsent : a ∉ [e, f] := by
              simpa using (List.nodup_cons.mp targetNodup).1
            simp [leftAbsent, rightAbsent]
          · simpa [equal] using support letter
        exact derivesTailPermutation a <|
          nodupPerm sourceNodup.tail targetNodup.tail tailSupport

/-- Length-three words with equal heads and support are derivably equal. -/
theorem derivesLengthThreeOfHeadSupportEq
    (left right : Word Nat)
    (leftThree : left.toList.length = 3)
    (rightThree : right.toList.length = 3)
    (heads : left.head = right.head)
    (support : SameSupport left right) :
    Derives basis left right := by
  cases left with
  | mk a leftTail =>
      cases leftTail with
      | nil =>
          simp [Word.toList] at leftThree
      | cons b leftRest =>
          cases leftRest with
          | nil =>
              simp [Word.toList] at leftThree
          | cons c leftMore =>
              have leftMoreNil : leftMore = [] := by
                simp [Word.toList] at leftThree
                omega
              subst leftMore
              cases right with
              | mk d rightTail =>
                  cases rightTail with
                  | nil =>
                      simp [Word.toList] at rightThree
                  | cons e rightRest =>
                      cases rightRest with
                      | nil =>
                          simp [Word.toList] at rightThree
                      | cons f rightMore =>
                          have rightMoreNil : rightMore = [] := by
                            simp [Word.toList] at rightThree
                            omega
                          subst rightMore
                          simpa [wordOfCons] using
                            derivesTripleOfHeadSupportEq
                              a b c d e f heads <| by
                                simpa [SameSupport, Word.toList] using support

/-- Four copies of a letter, represented as a nonempty word. -/
def headFourthPower (head : Nat) : Word Nat :=
  ⟨head, [head, head, head]⟩

/-- Every word of length at least four collapses to the fourth power of its
head. -/
theorem derivesLongWordToHeadFourth (word : Word Nat)
    (long : 4 ≤ word.toList.length) :
    Derives basis word (headFourthPower word.head) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil =>
              simp [Word.toList] at long
          | cons third more =>
              cases more with
              | nil =>
                  simp [Word.toList] at long
              | cons fourth suffix =>
                  have collapse :=
                    derivesFourBlockCollapse
                      (Word.singleton head) (Word.singleton second)
                      (Word.singleton third) (wordOfCons fourth suffix)
                  simpa [headFourthPower, wordOfCons, Word.singleton,
                    Word.append, Word.append_assoc] using collapse

/-- Long words with the same head are derivably equal. -/
theorem derivesLongWordsOfHeadEq (left right : Word Nat)
    (leftLong : 4 ≤ left.toList.length)
    (rightLong : 4 ≤ right.toList.length)
    (heads : left.head = right.head) :
    Derives basis left right := by
  have leftCollapse :=
    derivesLongWordToHeadFourth left leftLong
  have rightCollapse :=
    derivesLongWordToHeadFourth right rightLong
  have normalForms :
      headFourthPower left.head = headFourthPower right.head :=
    congrArg headFourthPower heads
  exact Derives.trans leftCollapse <| by
    rw [normalForms]
    exact Derives.symm rightCollapse

/-- Equal head/content/length-state signatures lie in the congruence generated
by the `S5_216` basis. -/
theorem derivesOfSameHeadContentLengthSignature
    (left right : Word Nat)
    (same : SameHeadContentLengthSignature left right) :
    Derives basis left right := by
  cases leftState : lengthState left with
  | one =>
      have equal : left = right :=
        Word.toList_injective (same.lengthOne leftState)
      subst right
      exact Derives.refl _
  | two =>
      have equal : left = right :=
        Word.toList_injective (same.lengthTwo leftState)
      subst right
      exact Derives.refl _
  | three =>
      have rightState : lengthState right = .three := by
        rw [← same.state]
        exact leftState
      exact derivesLengthThreeOfHeadSupportEq left right
        ((lengthState_eq_three_iff left).mp leftState)
        ((lengthState_eq_three_iff right).mp rightState)
        same.head (same.lengthThreeSupport leftState)
  | long =>
      have rightState : lengthState right = .long := by
        rw [← same.state]
        exact leftState
      exact derivesLongWordsOfHeadEq left right
        ((lengthState_eq_long_iff left).mp leftState)
        ((lengthState_eq_long_iff right).mp rightState)
        same.head

end SemigroupBasis.CoRoots.S5_216

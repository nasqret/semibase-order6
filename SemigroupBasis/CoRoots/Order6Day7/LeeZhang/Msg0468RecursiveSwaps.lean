import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0468RecursivePower

/-! B8 past-witness swaps and the unrestricted adapter for the one fixed
third-occurrence transport requested from S3. The requested fixed proof is
an explicit premise, not an axiom or an asserted completed capability. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive9726

open SemigroupBasis Order6Sunday

theorem listDerivesSwapPastInterval (left right : Nat) (firstGap secondGap : List Nat) :
    LD ([left] ++ firstGap ++ [right] ++ secondGap ++ [left, right])
      ([left] ++ firstGap ++ [right] ++ secondGap ++ [right, left]) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          have law := derivesOldLaw RecursivePublishedFinite.S6_9726.basisLaw3 (by decide)
          have substituted := law.subst (substituteFour (Word.singleton left) (Word.singleton right)
            (Word.singleton left) (Word.singleton left))
          exact S5_107.ListDerives.words substituted
      | cons head tail =>
          have law := derivesOldLaw RecursivePublishedFinite.S6_9726.basisLaw5 (by decide)
          have substituted := law.subst (substituteFour (Word.singleton left) (Word.singleton right)
            ⟨head, tail⟩ (Word.singleton left))
          have listed := S5_107.ListDerives.ofWord substituted
          simp only [Word.toList_bind] at listed
          simpa [RecursivePublishedFinite.S6_9726.basisLaw5, substituteFour,
            Word.toList, Word.singleton, List.append_assoc] using listed
  | cons firstHead firstTail =>
      cases secondGap with
      | nil =>
          have law := derivesOldLaw RecursivePublishedFinite.S6_9726.basisLaw6 (by decide)
          have substituted := law.subst (substituteFour (Word.singleton left) ⟨firstHead, firstTail⟩
            (Word.singleton right) (Word.singleton left))
          have listed := S5_107.ListDerives.ofWord substituted
          simp only [Word.toList_bind] at listed
          simpa [RecursivePublishedFinite.S6_9726.basisLaw6, substituteFour,
            Word.toList, Word.singleton, List.append_assoc] using listed
      | cons secondHead secondTail =>
          have law : Derives basis RecursiveDepth7Delta.S6_9726.addedLaw0.lhs
              RecursiveDepth7Delta.S6_9726.addedLaw0.rhs := Derives.fromBasis (by decide)
          have substituted := law.subst (substituteFour (Word.singleton left) ⟨firstHead, firstTail⟩
            (Word.singleton right) ⟨secondHead, secondTail⟩)
          have listed := S5_107.ListDerives.ofWord substituted
          simp only [Word.toList_bind] at listed
          simpa [RecursiveDepth7Delta.S6_9726.addedLaw0, substituteFour,
            Word.toList, Word.singleton, List.append_assoc] using listed

theorem listDerivesSwapBothSeen (prefixWords suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ prefixWords) (rightSeen : right ∈ prefixWords) :
    LD (prefixWords ++ left :: right :: suffix) (prefixWords ++ right :: left :: suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
  obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp leftSeen
  by_cases earlier : right ∈ before
  · obtain ⟨start, gap, beforeShape⟩ := List.mem_iff_append.mp earlier
    have swap := (listDerivesSwapPastInterval right left gap after).symm.context start suffix
    simpa [shape, beforeShape, List.append_assoc] using swap
  · have later : right ∈ after := by
      simpa [shape, earlier, Ne.symm equal] using rightSeen
    obtain ⟨gap, rest, afterShape⟩ := List.mem_iff_append.mp later
    have swap := (listDerivesSwapPastInterval left right gap rest).context before suffix
    simpa [shape, afterShape, List.append_assoc] using swap

/-- This is exactly the single finite signature delivered to S3 in the
locked ledger. The present module does not assert that it has been proved. -/
def ThirdTransport : Prop :=
  Derives basis (⟨0, [1, 0, 2, 0, 3]⟩ : Word Nat) (⟨0, [1, 0, 2, 3, 0]⟩ : Word Nat)

theorem listDerivesThirdInterval (third : ThirdTransport) (letter other : Nat)
    (firstGap secondGap : List Nat) :
    LD ([letter] ++ firstGap ++ [letter] ++ secondGap ++ [letter, other])
      ([letter] ++ firstGap ++ [letter] ++ secondGap ++ [other, letter]) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil => simpa using listDerivesTripleRotation letter (Word.singleton other)
      | cons head tail =>
          have rotation := listDerivesTripleRotation letter (⟨head, tail⟩ : Word Nat)
          have first := (rotation.append [other]).symm
          have last := listDerivesTripleRotation letter (⟨head, tail ++ [other]⟩ : Word Nat)
          have alignedLast : LD ([letter, letter, letter] ++ (head :: tail) ++ [other])
              ([letter, letter] ++ (head :: tail) ++ [other, letter]) := by
            simpa [Word.toList, List.append_assoc] using last
          simpa [List.append_assoc] using first.trans alignedLast
  | cons firstHead firstTail =>
      cases secondGap with
      | nil =>
          have law := derivesOldLaw RecursivePublishedFinite.S6_9726.basisLaw4 (by decide)
          have substituted := law.subst (substituteFour (Word.singleton letter) ⟨firstHead, firstTail⟩
            (Word.singleton other) (Word.singleton letter))
          have listed := S5_107.ListDerives.ofWord substituted
          simp only [Word.toList_bind] at listed
          simpa [RecursivePublishedFinite.S6_9726.basisLaw4, substituteFour,
            Word.toList, Word.singleton, List.append_assoc] using listed
      | cons secondHead secondTail =>
          have substituted := third.subst (substituteFour (Word.singleton letter) ⟨firstHead, firstTail⟩
            ⟨secondHead, secondTail⟩ (Word.singleton other))
          have listed := S5_107.ListDerives.ofWord substituted
          simp only [Word.toList_bind] at listed
          simpa [substituteFour, Word.toList, Word.singleton, List.append_assoc] using listed

theorem listDerivesSwapThird (third : ThirdTransport) (prefixWords suffix : List Nat)
    (letter other : Nat) (twice : 2 ≤ prefixWords.count letter) :
    LD (prefixWords ++ letter :: other :: suffix) (prefixWords ++ other :: letter :: suffix) := by
  obtain ⟨before, firstGap, secondGap, shape⟩ := Msg0463NilZ2.exists_two_occurrence_split letter twice
  have swap := (listDerivesThirdInterval third letter other firstGap secondGap).context before suffix
  simpa [shape, List.append_assoc] using swap

theorem guardedSwaps_of_third (third : ThirdTransport) : PrefixCount.GuardedSwaps basis := by
  intro prefixWords left right suffix allowed
  rcases allowed with leftTwice | rightTwice | both
  · exact listDerivesSwapThird third prefixWords suffix left right leftTwice
  · exact (listDerivesSwapThird third prefixWords suffix right left rightTwice).symm
  · exact listDerivesSwapBothSeen prefixWords suffix left right
      (List.count_pos_iff.mp (by omega)) (List.count_pos_iff.mp (by omega))

/-- Conditional only on the one exact fixed finite witness. All arbitrary-
word comparison, count reduction and empty-gap obligations are proved here. -/
theorem derivesOfSameSignature (third : ThirdTransport) {left right : Word Nat}
    (counts : PrefixCount.SameCapsThree left.toList right.toList)
    (prefixes : PrefixCount.SameBeforeTwo left.toList right.toList) : Derives basis left right := by
  have swaps := guardedSwaps_of_third third
  have grow := PrefixCount.grow_at_three_of_interval swaps tripleIntervalGrowth
  have derived := PrefixCount.compare_capped_counts swaps grow left.toList right.toList counts prefixes
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail => exact S5_107.ListDerives.toWord derived

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive9726

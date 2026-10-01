import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0490FordOnlyBlocks

/-! Unrestricted normalization by gathering, then guarded block capping.
The fixed first-occurrence render is computable on every finite input list. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordOnly

open SemigroupBasis S5_107 Examples

theorem firstBlock_ne_nil (letter : Nat) (tail : List Nat) :
    List.replicate (min ((letter :: tail).count letter) 2) letter ≠ [] := by
  intro empty
  have lengths := congrArg List.length empty
  simp only [List.length_replicate, List.length_nil, List.count_cons_self] at lengths
  omega

theorem blocksTwoAfter : ∀ (letters prefixWords : List Nat), prefixWords ≠ [] →
    LD (prefixWords ++ letters) (prefixWords ++ blocksTwo letters)
  | [], prefixWords, _ => by
      simpa [blocksTwo, firstOccurrenceSequence] using ListDerives.refl (basis := basis) prefixWords
  | letter :: tail, prefixWords, nonempty => by
      have gathered : LD (prefixWords ++ letter :: tail)
          (prefixWords ++ List.replicate ((letter :: tail).count letter) letter ++ remainder letter tail) := by
        simpa [remainder, List.append_assoc] using (gatherHead letter tail).prepend prefixWords
      have capped := capTwo prefixWords (remainder letter tail) letter
        ((letter :: tail).count letter) (Or.inl nonempty)
      have prefixNonempty :
          prefixWords ++ List.replicate (min ((letter :: tail).count letter) 2) letter ≠ [] :=
        fun empty => nonempty (List.append_eq_nil_iff.mp empty).1
      have remaining := blocksTwoAfter (remainder letter tail)
        (prefixWords ++ List.replicate (min ((letter :: tail).count letter) 2) letter) prefixNonempty
      rw [blocksTwo_cons]
      exact gathered.trans (capped.trans (by simpa [List.append_assoc] using remaining))
termination_by letters _ _ => letters.length
decreasing_by exact remainder_length_lt letter tail

theorem normalList_sound : ∀ letters : List Nat, LD letters (normalList letters)
  | [] => ListDerives.refl _
  | letter :: tail => by
      by_cases empty : remainder letter tail = []
      · rw [normalList_unary letter tail empty]
        have counts : (letter :: tail).count letter = (letter :: tail).length := by
          have partition := remainder_length_count letter tail
          simp only [empty, List.length_nil, Nat.zero_add] at partition
          simpa only [List.count_cons_self, List.length_cons] using congrArg Nat.succ partition
        have gathered := gatherHead letter tail
        change LD (letter :: tail)
          (List.replicate ((letter :: tail).count letter) letter ++ remainder letter tail) at gathered
        rw [empty, List.append_nil, counts] at gathered
        exact gathered.trans (capThree letter (letter :: tail).length)
      · rw [normalList_mixed letter tail empty, blocksTwo_cons]
        have gathered := gatherHead letter tail
        have capped := capTwo [] (remainder letter tail) letter
          ((letter :: tail).count letter) (Or.inr empty)
        simp only [List.nil_append] at capped
        have remaining := blocksTwoAfter (remainder letter tail)
          (List.replicate (min ((letter :: tail).count letter) 2) letter)
          (firstBlock_ne_nil letter tail)
        exact gathered.trans (capped.trans remaining)

theorem normalList_ne_nil (word : Word Nat) : normalList word.toList ≠ [] := by
  cases word with
  | mk head tail => exact (normalList_sound (head :: tail)).target_ne_nil

def normal (word : Word Nat) : Word Nat :=
  match normalList word.toList with
  | [] => word
  | head :: tail => ⟨head, tail⟩

theorem normal_toList (word : Word Nat) :
    (normal word).toList = normalList word.toList := by
  unfold normal
  cases shape : normalList word.toList with
  | nil => exact False.elim (normalList_ne_nil word shape)
  | cons head tail => rfl

theorem derives_normal (word : Word Nat) : Derives basis word (normal word) := by
  cases word with
  | mk head tail =>
      have derivation := normalList_sound (head :: tail)
      cases shape : normalList (head :: tail) with
      | nil => exact False.elim ((normalList_ne_nil ⟨head, tail⟩) shape)
      | cons nextHead nextTail =>
          rw [shape] at derivation
          simpa [normal, Word.toList, shape, listWordOfCons] using derivation.toWord

theorem normal_eq_of_signature {left right : Word Nat}
    (same : Signature left.toList right.toList) : normal left = normal right := by
  apply Word.toList_injective
  rw [normal_toList, normal_toList]
  exact normalList_eq same

theorem derives_of_signature {left right : Word Nat}
    (same : Signature left.toList right.toList) : Derives basis left right := by
  have leftNormal := derives_normal left
  rw [normal_eq_of_signature same] at leftNormal
  exact leftNormal.trans (derives_normal right).symm

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordOnly

import SemigroupBasis.CoRoots.S5_1155
import SemigroupBasis.Examples.CommutativePositiveModThreeFour

namespace SemigroupBasis.CoRoots.S5_1155

open SemigroupBasis
open SemigroupBasis.Examples

/-- A word presented by its first letter and remaining list. -/
def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- Append a list of letters behind a fixed nonempty word. -/
def appendTail (stem : Word Nat) (tail : List Nat) : Word Nat :=
  ⟨stem.head, stem.tail ++ tail⟩

@[simp]
theorem toList_wordOfCons (head : Nat) (tail : List Nat) :
    (wordOfCons head tail).toList = head :: tail := by
  rfl

@[simp]
theorem toList_appendTail (stem : Word Nat) (tail : List Nat) :
    (appendTail stem tail).toList = stem.toList ++ tail := by
  simp [appendTail, Word.toList]

@[simp]
theorem appendTail_nil (stem : Word Nat) :
    appendTail stem [] = stem := by
  apply Word.toList_injective
  simp

@[simp]
theorem appendTail_singleton
    (head : Nat) (tail : List Nat) :
    appendTail (Word.singleton head) tail = wordOfCons head tail := by
  rfl

@[simp]
theorem wordOfCons_head_tail (word : Word Nat) :
    wordOfCons word.head word.tail = word := by
  cases word
  rfl

theorem appendTail_cons
    (stem : Word Nat) (head : Nat) (tail : List Nat) :
    appendTail stem (head :: tail) =
      stem ++ wordOfCons head tail := by
  apply Word.toList_injective
  simp [List.append_assoc]

theorem appendTail_cons_prefix
    (stem : Word Nat) (head : Nat) (tail : List Nat) :
    appendTail stem (head :: tail) =
      appendTail (stem ++ Word.singleton head) tail := by
  apply Word.toList_injective
  simp [List.append_assoc]

/-- Every permutation strictly behind a fixed nonempty prefix is derivable. -/
theorem derivesTailPermutation
    (stem : Word Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives basis
      (appendTail stem left) (appendTail stem right) := by
  induction permutation generalizing stem with
  | nil =>
      exact Derives.refl _
  | cons head _ ih =>
      have next := ih (stem ++ Word.singleton head)
      rw [appendTail_cons_prefix, appendTail_cons_prefix]
      exact next
  | swap first second rest =>
      cases rest with
      | nil =>
          rw [appendTail_cons, appendTail_cons]
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using
              derivesSuffixSwap stem
                (Word.singleton second) (Word.singleton first)
      | cons next tail =>
          have swapped :=
            Derives.appendRight
              (derivesSuffixSwap stem
                (Word.singleton second) (Word.singleton first))
              (wordOfCons next tail)
          rw [appendTail_cons, appendTail_cons]
          simpa [wordOfCons, Word.append_assoc] using swapped
  | trans _ _ firstIH secondIH =>
      exact Derives.trans (firstIH stem) (secondIH stem)

private theorem three_copies_perm
    (letter : Nat) (letters : List Nat)
    (countEq : letters.count letter = 3) :
    letters.Perm
      (letter :: letter :: letter ::
        (((letters.erase letter).erase letter).erase letter)) := by
  have present : letter ∈ letters :=
    List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase present
  have countOnce : (letters.erase letter).count letter = 2 := by
    rw [List.count_erase_self, countEq]
  have presentOnce : letter ∈ letters.erase letter :=
    List.count_pos_iff.mp (by omega)
  have second := List.perm_cons_erase presentOnce
  have countTwice :
      ((letters.erase letter).erase letter).count letter = 1 := by
    rw [List.count_erase_self, countOnce]
  have presentTwice :
      letter ∈ (letters.erase letter).erase letter :=
    List.count_pos_iff.mp (by omega)
  exact first.trans <| List.Perm.cons letter <|
    second.trans <| List.Perm.cons letter <|
      List.perm_cons_erase presentTwice

private theorem derivesContractFourInTail
    (stem : Word Nat) (letter : Nat) (rest : List Nat) :
    Derives basis
      (appendTail stem
        (letter :: letter :: letter :: letter :: rest))
      (appendTail stem (letter :: rest)) := by
  cases rest with
  | nil =>
      simpa [appendTail, Word.append, Word.singleton,
        Word.append_assoc] using
          Derives.symm
            (derivesTailExpansion stem (Word.singleton letter))
  | cons next tail =>
      have contracted :=
        Derives.appendRight
          (Derives.symm
            (derivesTailExpansion stem (Word.singleton letter)))
          (wordOfCons next tail)
      simpa [appendTail, wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using contracted

/-- Normalize every multiplicity in the tail to its positive residue modulo
three. Recursion is on the original tail, not on an arranged intermediate. -/
theorem derivesPositiveModThreeTail :
    ∀ stem tail,
      Derives basis
        (appendTail stem tail)
        (appendTail stem (positiveModThreeReduce tail))
  | stem, [] => by
      exact Derives.refl _
  | stem, letter :: tail => by
      have suffixNormal :=
        derivesPositiveModThreeTail
          (stem ++ Word.singleton letter) tail
      have firstStep :
          Derives basis
            (appendTail stem (letter :: tail))
            (appendTail stem
              (letter :: positiveModThreeReduce tail)) := by
        rw [appendTail_cons_prefix, appendTail_cons_prefix]
        exact suffixNormal
      by_cases countSmall :
          (positiveModThreeReduce tail).count letter < 3
      · have reduced :
            positiveModThreeReduce (letter :: tail) =
              letter :: positiveModThreeReduce tail := by
          simp [positiveModThreeReduce, countSmall]
        rw [reduced]
        exact firstStep
      · have countLe :
            (positiveModThreeReduce tail).count letter ≤ 3 :=
          positiveModThreeReduce_count_le_three letter tail
        have countEq :
            (positiveModThreeReduce tail).count letter = 3 := by
          omega
        let remainder :=
          (((positiveModThreeReduce tail).erase letter).erase letter).erase
            letter
        have suffixPerm :
            (positiveModThreeReduce tail).Perm
              (letter :: letter :: letter :: remainder) := by
          simpa [remainder] using
            three_copies_perm letter (positiveModThreeReduce tail) countEq
        have expandedPerm :
            (letter :: positiveModThreeReduce tail).Perm
              (letter :: letter :: letter :: letter :: remainder) :=
          List.Perm.cons letter suffixPerm
        have arranged :=
          derivesTailPermutation stem expandedPerm
        have contracted :=
          derivesContractFourInTail stem letter remainder
        have eraseOnceCount :
            ((positiveModThreeReduce tail).erase letter).count letter = 2 := by
          rw [List.count_erase_self, countEq]
        have eraseTwiceCount :
            (((positiveModThreeReduce tail).erase letter).erase letter).count
                letter = 1 := by
          rw [List.count_erase_self, eraseOnceCount]
        have eraseTwiceHasLetter :
            letter ∈
              ((positiveModThreeReduce tail).erase letter).erase letter :=
          List.count_pos_iff.mp (by omega)
        have reducedPerm :
            (letter :: remainder).Perm
              (((positiveModThreeReduce tail).erase letter).erase letter) := by
          simpa [remainder] using
            (List.perm_cons_erase eraseTwiceHasLetter).symm
        have restored :=
          derivesTailPermutation stem reducedPerm
        have reduced :
            positiveModThreeReduce (letter :: tail) =
              ((positiveModThreeReduce tail).erase letter).erase letter := by
          simp [positiveModThreeReduce, countSmall]
        rw [reduced]
        exact Derives.trans firstStep <|
          Derives.trans arranged <|
            Derives.trans contracted restored
termination_by
  _ tail => tail.length

/-- Tail produced by one head-movement rewrite after exposing the old head
and the selected new head. -/
def retargetedTail (word : Word Nat) (selected : Nat) : List Nat :=
  word.head :: word.head :: selected :: selected :: selected ::
    (word.tail.erase word.head).erase selected

/-- The tail to normalize when selecting a head. Selecting the existing head
does not need a movement rewrite. -/
def repeatedHeadRetargetTail
    (word : Word Nat) (selected : Nat) : List Nat :=
  if word.head = selected then word.tail
  else retargetedTail word selected

/-- Explicit post-retarget normal form for the first normalization layer. -/
def repeatedHeadRetargetNormal
    (word : Word Nat) (selected : Nat) : Word Nat :=
  wordOfCons selected
    (positiveModThreeReduce (repeatedHeadRetargetTail word selected))

@[simp]
theorem repeatedHeadRetargetNormal_head
    (word : Word Nat) (selected : Nat) :
    (repeatedHeadRetargetNormal word selected).head = selected := by
  rfl

/-- With `head, selected` exposed immediately after the initial head, apply
head movement once and then normalize the entire resulting tail. -/
theorem derivesExposedHeadRetarget
    (head selected : Nat) (rest : List Nat) :
    Derives basis
      (appendTail (Word.singleton head) (head :: selected :: rest))
      (appendTail (Word.singleton selected)
        (positiveModThreeReduce
          (head :: head :: selected :: selected :: selected :: rest))) := by
  have movedCore :=
    derivesHeadMovement
      (Word.singleton head) (Word.singleton selected)
  have moved :
      Derives basis
        (appendTail (Word.singleton head) (head :: selected :: rest))
        (appendTail (Word.singleton selected)
          (head :: head :: selected :: selected :: selected :: rest)) := by
    cases rest with
    | nil =>
        simpa [appendTail, wordOfCons, Word.append, Word.singleton,
          Word.append_assoc] using movedCore
    | cons next tail =>
        have contextual :=
          Derives.appendRight movedCore (wordOfCons next tail)
        simpa [appendTail, wordOfCons, Word.append, Word.singleton,
          Word.append_assoc] using contextual
  have normalized :=
    derivesPositiveModThreeTail (Word.singleton selected)
      (head :: head :: selected :: selected :: selected :: rest)
  exact Derives.trans moved normalized

/-- Retarget a repeated head to a distinct supported letter. The proof first
uses one suffix permutation to expose `head, selected`, then invokes the
one-shot movement theorem and normalizes the whole post-movement tail. -/
theorem derivesDistinctRepeatedHeadRetarget
    (word : Word Nat) (selected : Nat)
    (different : word.head ≠ selected)
    (headRepeated : 2 ≤ word.toList.count word.head)
    (selectedSupported : selected ∈ word.toList) :
    Derives basis word
      (wordOfCons selected
        (positiveModThreeReduce (retargetedTail word selected))) := by
  cases word with
  | mk head tail =>
      change 2 ≤ (head :: tail).count head at headRepeated
      have headInTail : head ∈ tail := by
        apply List.count_pos_iff.mp
        rw [List.count_cons_self] at headRepeated
        omega
      have selectedInTail : selected ∈ tail := by
        simp only [Word.toList, List.mem_cons] at selectedSupported
        rcases selectedSupported with selectedEq | member
        · exact False.elim (different selectedEq.symm)
        · exact member
      have selectedAfterHeadErase : selected ∈ tail.erase head := by
        rw [List.mem_erase_of_ne (Ne.symm different)]
        exact selectedInTail
      have exposeHead :
          tail.Perm (head :: tail.erase head) :=
        List.perm_cons_erase headInTail
      have exposeSelected :
          (tail.erase head).Perm
            (selected :: (tail.erase head).erase selected) :=
        List.perm_cons_erase selectedAfterHeadErase
      have exposed :
          tail.Perm
            (head :: selected :: (tail.erase head).erase selected) :=
        exposeHead.trans (List.Perm.cons head exposeSelected)
      have arranged :=
        derivesTailPermutation (Word.singleton head) exposed
      have movedAndNormalized :=
        derivesExposedHeadRetarget head selected
          ((tail.erase head).erase selected)
      simpa [retargetedTail] using
        Derives.trans arranged movedAndNormalized

/-- Select any supported letter as head when the current head repeats. The
target is explicit; the equal-head branch only reduces the original tail. -/
theorem derivesRepeatedHeadRetarget
    (word : Word Nat) (selected : Nat)
    (headRepeated : 2 ≤ word.toList.count word.head)
    (selectedSupported : selected ∈ word.toList) :
    Derives basis word (repeatedHeadRetargetNormal word selected) := by
  by_cases same : word.head = selected
  · subst selected
    have normalized :=
      derivesPositiveModThreeTail
        (Word.singleton word.head) word.tail
    simpa [repeatedHeadRetargetNormal, repeatedHeadRetargetTail] using
      normalized
  · have retargeted :=
      derivesDistinctRepeatedHeadRetarget
        word selected same headRepeated selectedSupported
    simpa [repeatedHeadRetargetNormal, repeatedHeadRetargetTail, same] using
      retargeted

/-- Concrete regression: `x^4 y` derives `y^4 x` (variables `0` and `1`). -/
theorem derivesX4YToY4X :
    Derives basis
      (wordOfCons 0 [0, 0, 0, 1])
      (wordOfCons 1 [1, 1, 1, 0]) := by
  have retargeted :=
    derivesRepeatedHeadRetarget
      (wordOfCons 0 [0, 0, 0, 1]) 1 (by decide) (by decide)
  have normalEq :
      repeatedHeadRetargetNormal
          (wordOfCons 0 [0, 0, 0, 1]) 1 =
        wordOfCons 1 [1, 1, 1, 0] := by
    decide
  rw [normalEq] at retargeted
  exact retargeted

end SemigroupBasis.CoRoots.S5_1155

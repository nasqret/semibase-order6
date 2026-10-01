import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395EvenInsertion

/-! B12 swaps only after both letters have appeared. No first introduction
is moved. Empty intervening gaps are handled without empty substitutions. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SeenSwaps

open SemigroupBasis
open Msg0457S11395Semantics Msg0457S11395EvenInsertion

private def fourWords (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | n + 4 => Word.singleton (n + 4)

theorem derivesSwapShort : Derives basis law03.lhs law03.rhs :=
  Derives.fromBasis (by decide)
theorem derivesSwapAfter : Derives basis law06.lhs law06.rhs :=
  Derives.fromBasis (by decide)
theorem derivesSwapBetween : Derives basis law07.lhs law07.rhs :=
  Derives.fromBasis (by decide)
theorem derivesSwapFull : Derives basis law08.lhs law08.rhs :=
  Derives.fromBasis (by decide)

theorem swapAfterWitnesses (left right : Nat) (between before : List Nat) :
    LD ([left] ++ between ++ [right] ++ before ++ [left,right])
      ([left] ++ between ++ [right] ++ before ++ [right,left]) := by
  cases between with
  | nil =>
      cases before with
      | nil =>
          have proof := S5_107.ListDerives.ofWord (derivesSwapShort.subst
            (fourWords (Word.singleton left) (Word.singleton right)
              (Word.singleton left) (Word.singleton left)))
          simp only [Word.toList_bind] at proof
          simpa [law03, fourWords, Word.toList, Word.singleton] using proof
      | cons head tail =>
          have proof := S5_107.ListDerives.ofWord (derivesSwapAfter.subst
            (fourWords (Word.singleton left) (Word.singleton right)
              (S5_107.listWordOfCons head tail) (Word.singleton left)))
          simp only [Word.toList_bind] at proof
          simpa [law06, fourWords, Word.toList, Word.singleton,
            S5_107.listWordOfCons, List.append_assoc] using proof
  | cons head tail =>
      cases before with
      | nil =>
          have proof := S5_107.ListDerives.ofWord (derivesSwapBetween.subst
            (fourWords (Word.singleton left) (S5_107.listWordOfCons head tail)
              (Word.singleton right) (Word.singleton left)))
          simp only [Word.toList_bind] at proof
          simpa [law07, fourWords, Word.toList, Word.singleton,
            S5_107.listWordOfCons, List.append_assoc] using proof
      | cons next rest =>
          have proof := S5_107.ListDerives.ofWord (derivesSwapFull.subst
            (fourWords (Word.singleton left) (S5_107.listWordOfCons head tail)
              (Word.singleton right) (S5_107.listWordOfCons next rest)))
          simp only [Word.toList_bind] at proof
          simpa [law08, fourWords, Word.toList, Word.singleton,
            S5_107.listWordOfCons, List.append_assoc] using proof

/-- The order and distance of the two past witnesses are unrestricted. -/
theorem swapSeen (prefixWords suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ prefixWords) (rightSeen : right ∈ prefixWords) :
    LD (prefixWords ++ [left,right] ++ suffix)
      (prefixWords ++ [right,left] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
  obtain ⟨beforeLeft, afterLeft, shape⟩ := List.append_of_mem leftSeen
  have relative : right ∈ beforeLeft ∨ right ∈ afterLeft := by
    rw [shape] at rightSeen
    simpa [equal, Ne.symm equal] using rightSeen
  rcases relative with before | after
  · obtain ⟨beforeRight, between, inner⟩ := List.append_of_mem before
    rw [shape, inner]
    simpa [List.append_assoc] using
      ((swapAfterWitnesses right left between afterLeft).context beforeRight suffix).symm
  · obtain ⟨between, afterRight, inner⟩ := List.append_of_mem after
    rw [shape, inner]
    simpa [List.append_assoc] using
      (swapAfterWitnesses left right between afterRight).context beforeLeft suffix

def AllSeen (prefixWords gap : List Nat) : Prop := ∀ tested ∈ gap, tested ∈ prefixWords

theorem seenGapPermutation (prefixWords suffix : List Nat) {left right : List Nat}
    (permutation : left.Perm right) (seen : AllSeen prefixWords left) :
    LD (prefixWords ++ left ++ suffix) (prefixWords ++ right ++ suffix) := by
  induction permutation generalizing prefixWords with
  | nil => exact S5_107.ListDerives.refl _
  | cons letter _ ih =>
      apply (show LD (prefixWords ++ _ ++ suffix) (prefixWords ++ _ ++ suffix) from ?_)
      simpa [List.append_assoc] using ih (prefixWords ++ [letter]) (by
        intro tested member
        exact List.mem_append_left _ (seen tested (List.mem_cons_of_mem letter member)))
  | swap left right rest =>
      simpa [List.append_assoc] using swapSeen prefixWords (rest ++ suffix) right left
        (seen right (by simp)) (seen left (by simp))
  | trans firstPermutation _ first second =>
      apply (first prefixWords seen).trans
      apply second prefixWords
      intro tested member
      exact seen tested (firstPermutation.mem_iff.mpr member)

theorem compareSeenGaps (prefixWords left right suffix : List Nat)
    (counts : ∀ tested, left.count tested = right.count tested)
    (seen : AllSeen prefixWords left) :
    LD (prefixWords ++ left ++ suffix) (prefixWords ++ right ++ suffix) :=
  seenGapPermutation prefixWords suffix (List.perm_iff_count.mpr counts) seen

def sortedGap (gap : List Nat) : List Nat := S5_254.canonicalGapResidue gap

theorem sortedGap_perm (gap : List Nat) : (sortedGap gap).Perm gap :=
  List.mergeSort_perm _ _

theorem sortSeenGap (prefixWords gap suffix : List Nat) (seen : AllSeen prefixWords gap) :
    LD (prefixWords ++ gap ++ suffix) (prefixWords ++ sortedGap gap ++ suffix) :=
  seenGapPermutation prefixWords suffix (sortedGap_perm gap).symm seen

theorem sortedGap_eq_of_counts (left right : List Nat)
    (counts : ∀ tested, left.count tested = right.count tested) : sortedGap left = sortedGap right := by
  apply List.Perm.eq_of_pairwise
    (fun _ _ _ _ first second => Nat.le_antisymm first second)
    (S5_254.canonicalGapResidue_pairwise left) (S5_254.canonicalGapResidue_pairwise right)
  apply List.perm_iff_count.mpr
  intro tested
  change (sortedGap left).count tested = (sortedGap right).count tested
  rw [(sortedGap_perm left).count tested, (sortedGap_perm right).count tested, counts tested]

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SeenSwaps

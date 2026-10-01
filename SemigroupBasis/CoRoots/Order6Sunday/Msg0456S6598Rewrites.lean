import SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Signature
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456FordNilGapRender

/-! Actual B25 derivations, not semantic lifting from M18. The complete
FordNil B23 is derived first. The additional future/future swap permits
two first introductions to commute inside a globally repeated gap. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Rewrites

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day7.LeeZhang
open Msg0456S6598Semantics

abbrev LD := S5_107.ListDerives basis
abbrev AllRepeated := FordNil.AllRepeated

theorem ford06 : Derives basis Msg0446NilZ2.Ford.law06.lhs Msg0446NilZ2.Ford.law06.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := [⟨8, .forward, [], [], [[0], [1], [1]]⟩]) (by decide)

theorem ford09 : Derives basis Msg0446NilZ2.Ford.law09.lhs Msg0446NilZ2.Ford.law09.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := [⟨10, .forward, [], [], [[0], [1], [1]]⟩]) (by decide)

theorem ford10 : Derives basis Msg0446NilZ2.Ford.law10.lhs Msg0446NilZ2.Ford.law10.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := [⟨4, .forward, [], [1], [[0], [1]]⟩,
      ⟨15, .backward, [], [], [[0], [1], [0]]⟩]) (by decide)

/-- Every one of the actual 23 laws is a B25 consequence. -/
theorem fordBasisDerivable : ∀ identity, identity ∈ FordNil.basis →
    Derives basis identity.lhs identity.rhs := by
  intro identity member
  simp only [FordNil.basis, Msg0446NilZ2.Ford.basis, FordNil.swaps,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with old | added
  · rcases old with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    all_goals subst identity
    all_goals first | exact Derives.fromBasis (by decide) | exact ford06 | exact ford09 | exact ford10
  · rcases added with h|h|h
    all_goals subst identity
    all_goals exact Derives.fromBasis (by decide)

theorem transportFordList {left right : List Nat}
    (derivation : S5_107.ListDerives FordNil.basis left right) : LD left right := by
  cases derivation with
  | empty => exact S5_107.ListDerives.empty
  | words proof => exact S5_107.ListDerives.words (proof.transport fordBasisDerivable)

def futureFull : Identity Nat := ⟨⟨0,[1,2,0,3,1]⟩,⟨1,[0,2,0,3,1]⟩⟩
def futureNoBefore : Identity Nat := ⟨⟨0,[1,0,2,1]⟩,⟨1,[0,0,2,1]⟩⟩
def futureNoBetween : Identity Nat := ⟨⟨0,[1,2,0,1]⟩,⟨1,[0,2,0,1]⟩⟩
def futureShort : Identity Nat := ⟨⟨0,[1,0,1]⟩,⟨1,[0,0,1]⟩⟩

theorem derivesFutureFull : Derives basis futureFull.lhs futureFull.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := [⟨24,.forward,[],[],[[0],[2],[1],[3]]⟩]) (by decide)

theorem derivesFutureNoBefore : Derives basis futureNoBefore.lhs futureNoBefore.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := [⟨11,.backward,[],[],[[0],[1],[2]]⟩,
      ⟨12,.forward,[],[],[[0],[1],[2]]⟩]) (by decide)

theorem derivesFutureNoBetween : Derives basis futureNoBetween.lhs futureNoBetween.rhs :=
  Derives.fromBasis (by decide)

theorem derivesFutureShort : Derives basis futureShort.lhs futureShort.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := [⟨4,.backward,[],[],[[0],[1]]⟩,
      ⟨5,.forward,[],[],[[0],[1]]⟩]) (by decide)

private def fourWords (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | n + 4 => Word.singleton (n + 4)

/-- Both witnesses lie in the future. Empty fillers are handled as actual
list contexts, never as empty substitution images. -/
theorem swapFuture (left right : Nat) (before between : List Nat) :
    LD ([left,right] ++ before ++ [left] ++ between ++ [right])
      ([right,left] ++ before ++ [left] ++ between ++ [right]) := by
  cases before with
  | nil =>
      cases between with
      | nil =>
          have proof := S5_107.ListDerives.ofWord (derivesFutureShort.subst
            (fourWords (Word.singleton left) (Word.singleton right)
              (Word.singleton left) (Word.singleton left)))
          simp only [Word.toList_bind] at proof
          simpa [futureShort, fourWords, Word.toList_bind, Word.toList, Word.singleton] using proof
      | cons head tail =>
          have proof := S5_107.ListDerives.ofWord (derivesFutureNoBefore.subst
            (fourWords (Word.singleton left) (Word.singleton right)
              (S5_107.listWordOfCons head tail) (Word.singleton left)))
          simp only [Word.toList_bind] at proof
          simpa [futureNoBefore, fourWords, Word.toList_bind, Word.toList, Word.singleton,
            S5_107.listWordOfCons, List.append_assoc] using proof
  | cons head tail =>
      cases between with
      | nil =>
          have proof := S5_107.ListDerives.ofWord (derivesFutureNoBetween.subst
            (fourWords (Word.singleton left) (Word.singleton right)
              (S5_107.listWordOfCons head tail) (Word.singleton left)))
          simp only [Word.toList_bind] at proof
          simpa [futureNoBetween, fourWords, Word.toList_bind, Word.toList, Word.singleton,
            S5_107.listWordOfCons, List.append_assoc] using proof
      | cons next rest =>
          have proof := S5_107.ListDerives.ofWord (derivesFutureFull.subst
            (fourWords (Word.singleton left) (Word.singleton right)
              (S5_107.listWordOfCons head tail) (S5_107.listWordOfCons next rest)))
          simp only [Word.toList_bind] at proof
          simpa [futureFull, fourWords, Word.toList_bind, Word.toList, Word.singleton,
            S5_107.listWordOfCons, List.append_assoc] using proof

/-- All four past/future witness configurations, including two new
introductions. No first-order or bounded-length premise is required. -/
theorem swapRepeated (prefixWords suffix : List Nat) (left right : Nat)
    (leftRepeated : 2 ≤ (prefixWords ++ [left,right] ++ suffix).count left)
    (rightRepeated : 2 ≤ (prefixWords ++ [left,right] ++ suffix).count right) :
    LD (prefixWords ++ [left,right] ++ suffix)
      (prefixWords ++ [right,left] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
  by_cases seen : left ∈ prefixWords ∨ right ∈ prefixWords
  · exact transportFordList (FordNil.transportGuardedList
      (FordSwapCore.listDerivesSwapNonSimpleSeen prefixWords suffix left right
        leftRepeated rightRepeated seen))
  have leftFuture : left ∈ suffix :=
    (FordSwapCore.external_of_repeated prefixWords suffix left right equal leftRepeated).resolve_left
      (fun member => seen (Or.inl member))
  have swappedCount : (prefixWords ++ [right,left] ++ suffix).count right =
      (prefixWords ++ [left,right] ++ suffix).count right := by
    simp [List.count_append, equal]
  have rightFuture : right ∈ suffix :=
    (FordSwapCore.external_of_repeated prefixWords suffix right left (Ne.symm equal)
      (by rw [swappedCount]; exact rightRepeated)).resolve_left
        (fun member => seen (Or.inr member))
  obtain ⟨beforeLeft, afterLeft, shape⟩ := List.append_of_mem leftFuture
  have relative : right ∈ beforeLeft ∨ right ∈ afterLeft := by
    rw [shape] at rightFuture
    simpa [equal, Ne.symm equal] using rightFuture
  rcases relative with before | after
  · obtain ⟨beforeRight, between, inner⟩ := List.append_of_mem before
    rw [shape, inner]
    simpa [List.append_assoc] using
      ((swapFuture right left beforeRight between).context prefixWords afterLeft).symm
  · obtain ⟨between, afterRight, inner⟩ := List.append_of_mem after
    rw [shape, inner]
    simpa [List.append_assoc] using
      (swapFuture left right beforeLeft between).context prefixWords afterRight

end SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Rewrites

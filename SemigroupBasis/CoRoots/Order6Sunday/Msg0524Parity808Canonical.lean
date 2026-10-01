import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808Blocks
import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808RunSort

/-! Callable whole-word reduction followed by singleton-aware run sorting.
Fuel is input length. The last block is excluded from sorting. Semantic
key completeness and uniqueness are separate obligations, not assumed here. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808Canonical

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107 (ListDerives)
open Msg0524Parity808Gather
open Msg0524Parity808Blocks
open Msg0524Parity808RunSort

def spine : Nat → List Nat → List (Nat × Nat)
  | 0, word => word.map (fun a => (a,0))
  | fuel + 1, word =>
    match word.reverse with
    | [] => []
    | a :: stem =>
      spine fuel (eraseLetter a stem.reverse) ++ [(a,reducedExponent (stem.reverse.count a + 1)-1)]

theorem render_spine (fuel : Nat) (word : List Nat) : render (spine fuel word) = normalize fuel word := by
  induction fuel generalizing word with
  | zero =>
    induction word with
    | nil => rfl
    | cons a tail ih => simpa [spine,normalize,render,blockWord] using congrArg (List.cons a) ih
  | succ fuel ih =>
    cases reversed : word.reverse with
    | nil => simp only [spine,normalize,reversed,render,List.flatMap_nil]
    | cons a stem =>
      have positive := reducedExponent_positive (stem.reverse.count a + 1) (by omega)
      have count : reducedExponent (stem.reverse.count a + 1) - 1 + 1 =
          reducedExponent (stem.reverse.count a + 1) := by omega
      simp only [spine,normalize,reversed,render,List.flatMap_append,List.flatMap_cons,
        List.flatMap_nil,List.append_nil]
      change render (spine fuel (eraseLetter a stem.reverse)) ++
        blockWord (a,reducedExponent (stem.reverse.count a+1)-1) = _
      rw [ih]
      simp only [blockWord,count]

def terminalSort (blocks : List (Nat × Nat)) : List (Nat × Nat) :=
  match blocks.reverse with
  | [] => []
  | last :: reversedPrefix => sortRuns reversedPrefix.reverse ++ [last]

theorem terminalSort_perm (blocks : List (Nat × Nat)) : (terminalSort blocks).Perm blocks := by
  cases reversed : blocks.reverse with
  | nil =>
    have empty : blocks = [] := by simpa using congrArg List.reverse reversed
    subst blocks
    exact List.Perm.refl _
  | cons last reversedPrefix =>
    have represented : blocks = reversedPrefix.reverse ++ [last] := by simpa using congrArg List.reverse reversed
    simp only [terminalSort,reversed]
    rw [represented]
    exact (sortRuns_perm reversedPrefix.reverse).append_right [last]

theorem terminalSort_derives (blocks : List (Nat × Nat)) :
    LD (render blocks) (render (terminalSort blocks)) := by
  cases reversed : blocks.reverse with
  | nil =>
    have empty : blocks = [] := by simpa using congrArg List.reverse reversed
    subst blocks
    exact ListDerives.refl _
  | cons last reversedPrefix =>
    have represented : blocks = reversedPrefix.reverse ++ [last] := by simpa using congrArg List.reverse reversed
    have step := sortRuns_derives reversedPrefix.reverse (blockWord last) (blockWord_nonempty last)
    simp only [terminalSort,reversed]
    rw [represented]
    simpa only [render,List.flatMap_append,
      List.flatMap_cons,List.flatMap_nil,List.append_nil] using step

def canonical (word : List Nat) : List Nat := render (terminalSort (spine word.length word))

theorem canonical_derives (word : List Nat) : LD word (canonical word) := by
  have first := normal_derives word
  have second := terminalSort_derives (spine word.length word)
  rw [render_spine] at second
  exact first.trans second

theorem canonical_count (word : List Nat) (x : Nat) :
    (canonical word).count x = reducedExponent (word.count x) := by
  have permutation := (terminalSort_perm (spine word.length word)).flatMap_right blockWord
  have counts := permutation.count_eq x
  change (canonical word).count x = (render (spine word.length word)).count x at counts
  rw [render_spine] at counts
  exact counts.trans (normal_count word x)

theorem canonical_count_bound (word : List Nat) (x : Nat) : (canonical word).count x ≤ 3 := by
  rw [canonical_count]
  exact reducedExponent_bound _

theorem canonical_count_parity (word : List Nat) (x : Nat) :
    (canonical word).count x % 2 = word.count x % 2 := by
  rw [canonical_count]
  exact reducedExponent_parity _

theorem canonical_cons_ne_nil (a : Nat) (tail : List Nat) : canonical (a :: tail) ≠ [] :=
  ListDerives.target_ne_nil (canonical_derives (a :: tail))

def canonicalWord (word : Word Nat) : Word Nat :=
  match canonical word.toList with
  | [] => word
  | a :: tail => ⟨a,tail⟩

theorem canonicalWord_toList (word : Word Nat) : (canonicalWord word).toList = canonical word.toList := by
  have nonempty : canonical word.toList ≠ [] := canonical_cons_ne_nil word.head word.tail
  cases h : canonical word.toList with
  | nil => exact False.elim (nonempty h)
  | cons a tail =>
    have normalized : canonicalWord word = ⟨a,tail⟩ := by unfold canonicalWord; rw [h]
    rw [normalized]
    rfl

theorem canonicalWord_derives (word : Word Nat) : Derives basis word (canonicalWord word) := by
  have step := canonical_derives word.toList
  rw [← canonicalWord_toList word] at step
  exact step.toWord

theorem canonicalWord_count (word : Word Nat) (x : Nat) :
    (canonicalWord word).toList.count x = reducedExponent (word.toList.count x) := by
  rw [canonicalWord_toList,canonical_count]

theorem canonicalWord_count_bound (word : Word Nat) (x : Nat) : (canonicalWord word).toList.count x ≤ 3 := by
  rw [canonicalWord_count]
  exact reducedExponent_bound _

theorem canonicalWord_count_parity (word : Word Nat) (x : Nat) :
    (canonicalWord word).toList.count x % 2 = word.toList.count x % 2 := by
  rw [canonicalWord_count]
  exact reducedExponent_parity _

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808Canonical

import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808Gather

/-! A callable whole-word terminal-block reducer for Parity808. The fuel is
the input length, not a fixed finite test bound. Sorting repeated block runs
and semantic completeness are intentionally not claimed here. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808Blocks

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107
open Msg0524Parity808Gather

def normalize : Nat → List Nat → List Nat
  | 0, word => word
  | fuel + 1, word =>
    match word.reverse with
    | [] => []
    | a :: reversedStem =>
      normalize fuel (eraseLetter a reversedStem.reverse) ++
        List.replicate (reducedExponent (reversedStem.reverse.count a + 1)) a

def normal (word : List Nat) : List Nat := normalize word.length word

theorem normalize_derives (fuel : Nat) (word : List Nat) : LD word (normalize fuel word) := by
  induction fuel generalizing word with
  | zero => exact ListDerives.refl _
  | succ fuel ih =>
    cases reversed : word.reverse with
    | nil =>
      have empty : word = [] := by simpa using congrArg List.reverse reversed
      subst word
      exact ListDerives.refl _
    | cons a stem =>
      have represented : word = stem.reverse ++ [a] := by
        simpa using congrArg List.reverse reversed
      simp only [normalize,reversed]
      have first : LD word
          (eraseLetter a stem.reverse ++ List.replicate (reducedExponent (stem.reverse.count a + 1)) a) := by
        simpa only [represented] using gatherTerminalParity stem.reverse a
      exact first.trans ((ih (eraseLetter a stem.reverse)).append _)

theorem normal_derives (word : List Nat) : LD word (normal word) := normalize_derives word.length word

theorem erase_count (word : List Nat) (a x : Nat) :
    (eraseLetter a word).count x = if x = a then 0 else word.count x := by
  by_cases same : x = a
  · subst x
    rw [if_pos rfl]
    exact List.count_eq_zero.mpr (by simp [eraseLetter])
  · rw [if_neg same]
    exact List.count_filter (by simpa using same)

theorem normalize_count (fuel : Nat) (word : List Nat) (x : Nat) (enough : word.length ≤ fuel) :
    (normalize fuel word).count x = reducedExponent (word.count x) := by
  induction fuel generalizing word with
  | zero =>
    cases word with
    | nil => rfl
    | cons a stem => simp at enough
  | succ fuel ih =>
    cases reversed : word.reverse with
    | nil =>
      have empty : word = [] := by simpa using congrArg List.reverse reversed
      subst word
      rfl
    | cons a stem =>
      have represented : word = stem.reverse ++ [a] := by
        simpa using congrArg List.reverse reversed
      have small : (eraseLetter a stem.reverse).length ≤ fuel := by
        have bound := List.length_filter_le (fun b => b != a) stem.reverse
        simp only [List.length_reverse] at bound
        have original := enough
        rw [represented,List.length_append,List.length_reverse,List.length_singleton] at original
        unfold eraseLetter
        omega
      simp only [normalize,reversed,List.count_append]
      rw [ih _ small,erase_count]
      by_cases same : x = a
      · subst x
        simp [represented,List.count_append,reducedExponent]
      · simp [represented,same,Ne.symm same,List.count_append,List.count_replicate]

theorem normal_count (word : List Nat) (x : Nat) :
    (normal word).count x = reducedExponent (word.count x) := normalize_count word.length word x (by omega)

theorem normal_count_bound (word : List Nat) (x : Nat) : (normal word).count x ≤ 3 := by
  rw [normal_count]
  exact reducedExponent_bound _

theorem normal_count_parity (word : List Nat) (x : Nat) :
    (normal word).count x % 2 = word.count x % 2 := by
  rw [normal_count]
  exact reducedExponent_parity _

theorem normal_cons_ne_nil (a : Nat) (tail : List Nat) : normal (a :: tail) ≠ [] :=
  ListDerives.target_ne_nil (normal_derives (a :: tail))

def normalWord (word : Word Nat) : Word Nat :=
  match normal word.toList with
  | [] => word
  | a :: tail => ⟨a,tail⟩

theorem normalWord_toList (word : Word Nat) : (normalWord word).toList = normal word.toList := by
  have nonempty : normal word.toList ≠ [] := normal_cons_ne_nil word.head word.tail
  cases h : normal word.toList with
  | nil => exact False.elim (nonempty h)
  | cons a tail =>
    have normalized : normalWord word = ⟨a,tail⟩ := by
      unfold normalWord
      rw [h]
    rw [normalized]
    rfl

theorem normalWord_derives (word : Word Nat) :
    Derives Msg0524Parity808Gather.basis word (normalWord word) := by
  have step := normal_derives word.toList
  rw [← normalWord_toList word] at step
  exact step.toWord

theorem normalWord_count (word : Word Nat) (x : Nat) :
    (normalWord word).toList.count x = reducedExponent (word.toList.count x) := by
  rw [normalWord_toList,normal_count]

theorem normalWord_count_bound (word : Word Nat) (x : Nat) : (normalWord word).toList.count x ≤ 3 := by
  rw [normalWord_count]
  exact reducedExponent_bound _

theorem normalWord_count_parity (word : Word Nat) (x : Nat) :
    (normalWord word).toList.count x % 2 = word.toList.count x % 2 := by
  rw [normalWord_count]
  exact reducedExponent_parity _

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808Blocks

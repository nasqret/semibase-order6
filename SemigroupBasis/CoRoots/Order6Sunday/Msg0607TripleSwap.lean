import SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleRules
import SemigroupBasis.Examples.CyclicTwo

set_option maxRecDepth 100000

/-!
Region rewriting under Σ4.

* `listDerivesSwap`: an adjacent pair `y s` may be swapped when `y` occurs
  earlier and both letters occur later.
* `listDerivesRegionPerm`: a region all of whose letters occur both before and
  after it may be permuted arbitrarily.
* `listDerivesDeleteSquare`: a square `c c` inside such a region may be deleted.
* `listDerivesCanonRegion`: such a region derives to `canon`, the increasing
  list of its odd-count letters.
-/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleSwap

open SemigroupBasis
open Msg0607TripleTables
open Msg0607TripleRules

/-- Swap `y s` when `y` occurs in `P` and both `y` and `s` occur in `Q`. -/
theorem listDerivesSwap (P Q : List Nat) (y s : Nat)
    (yBefore : y ∈ P) (yAfter : y ∈ Q) (sAfter : s ∈ Q) :
    ListDerives (P ++ [y, s] ++ Q) (P ++ [s, y] ++ Q) := by
  by_cases equal : y = s
  · subst equal
    exact S5_107.ListDerives.refl _
  obtain ⟨P₁, A, rfl⟩ := List.mem_iff_append.mp yBefore
  obtain ⟨B, Q', rfl⟩ := List.mem_iff_append.mp yAfter
  rw [List.mem_append, List.mem_cons] at sAfter
  rcases sAfter with sInB | sIsY | sInQ'
  · obtain ⟨B₁, B₂, rfl⟩ := List.mem_iff_append.mp sInB
    have core := (swapCore2 y s A B₁ B₂).context P₁ Q'
    simpa [List.append_assoc] using core
  · exact absurd sIsY.symm equal
  · obtain ⟨C, D, rfl⟩ := List.mem_iff_append.mp sInQ'
    have core := (swapCore1 y s A B C).context P₁ D
    simpa [List.append_assoc] using core

/-- A region whose letters all occur before and after it may be permuted. -/
theorem listDerivesRegionPerm (Rt : List Nat) :
    ∀ {R₁ R₂ : List Nat}, R₁.Perm R₂ → ∀ L : List Nat,
      (∀ c ∈ R₁, c ∈ L) → (∀ c ∈ R₁, c ∈ Rt) →
      ListDerives (L ++ R₁ ++ Rt) (L ++ R₂ ++ Rt) := by
  intro R₁ R₂ permutation
  induction permutation with
  | nil =>
      intro L _ _
      exact S5_107.ListDerives.refl _
  | @cons x R₁ R₂ _ ih =>
      intro L before after
      have step := ih (L ++ [x]) (fun c mem => List.mem_append_left _ (before c (by simp [mem])))
        (fun c mem => after c (by simp [mem]))
      simpa [List.append_assoc] using step
  | swap a b R =>
      intro L before after
      have swapped := listDerivesSwap L (R ++ Rt) b a (before b (by simp))
        (List.mem_append_right _ (after b (by simp))) (List.mem_append_right _ (after a (by simp)))
      simpa [List.append_assoc] using swapped
  | @trans R₁ R₂ R₃ h₁ _ ih₁ ih₂ =>
      intro L before after
      have first := ih₁ L before after
      have second := ih₂ L (fun c mem => before c (h₁.mem_iff.mpr mem))
        (fun c mem => after c (h₁.mem_iff.mpr mem))
      exact first.trans second

/-- Delete a square `c c` when `c` occurs before and after the region. -/
theorem listDerivesDeleteSquare (L Rt A B : List Nat) (c : Nat)
    (before : c ∈ L) (after : c ∈ Rt) :
    ListDerives (L ++ (A ++ [c, c] ++ B) ++ Rt) (L ++ (A ++ B) ++ Rt) := by
  obtain ⟨L₁, L₂, rfl⟩ := List.mem_iff_append.mp before
  obtain ⟨R₁, R₂, rfl⟩ := List.mem_iff_append.mp after
  have core := (deleteCore c (L₂ ++ A) (B ++ R₁)).context L₁ R₂
  simpa [List.append_assoc] using core

/-! ## The canonical square-free representative of a region -/

/-- The increasing list of the letters with odd count. -/
def canon (R : List Nat) : List Nat :=
  (Examples.parityReduce R).mergeSort fun left right => decide (left ≤ right)

theorem mem_canon (x : Nat) (R : List Nat) : x ∈ canon R ↔ R.count x % 2 = 1 := by
  simp only [canon, List.mem_mergeSort, Examples.mem_parityReduce_iff]

theorem canon_nodup (R : List Nat) : (canon R).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Examples.parityReduce_nodup R)

theorem canon_pairwise (R : List Nat) : (canon R).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true → decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right leftMiddle middleRight
    exact decide_eq_true (Nat.le_trans (of_decide_eq_true leftMiddle) (of_decide_eq_true middleRight))
  have total : ∀ left right : Nat, (decide (left ≤ right) || decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with h | h
    · simp [h]
    · simp [h]
  have sorted := List.pairwise_mergeSort transitive total (Examples.parityReduce R)
  simpa [canon] using sorted.imp fun relation => of_decide_eq_true relation

/-- Two sorted duplicate-free lists with the same members are equal. -/
theorem sorted_eq_of_mem_iff {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·)) (rightSorted : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (same : ∀ x, x ∈ left ↔ x ∈ right) : left = right := by
  have permutation : left.Perm right := by
    rw [List.perm_iff_count]
    intro x
    rw [leftNodup.count, rightNodup.count]
    simp only [same x]
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => Nat.le_antisymm h₁ h₂)
    leftSorted rightSorted permutation

/-- `canon` depends only on the count parities. -/
theorem canon_eq_of_parity {R₁ R₂ : List Nat}
    (parity : ∀ x, R₁.count x % 2 = R₂.count x % 2) : canon R₁ = canon R₂ :=
  sorted_eq_of_mem_iff (canon_pairwise R₁) (canon_pairwise R₂) (canon_nodup R₁) (canon_nodup R₂)
    (fun x => by rw [mem_canon, mem_canon, parity x])

theorem canon_perm_of_count_le_one {R : List Nat} (bound : ∀ c, R.count c ≤ 1) :
    (canon R).Perm R := by
  rw [List.perm_iff_count]
  intro x
  rw [(canon_nodup R).count]
  have := bound x
  by_cases mem : x ∈ canon R
  · rw [if_pos mem]
    have odd := (mem_canon x R).mp mem
    omega
  · rw [if_neg mem]
    have notOdd : ¬ R.count x % 2 = 1 := fun h => mem ((mem_canon x R).mpr h)
    omega

theorem count_erase_erase (R : List Nat) (c x : Nat) (multiple : 2 ≤ R.count c) :
    ((R.erase c).erase c).count x % 2 = R.count x % 2 := by
  by_cases equal : x = c
  · subst equal
    have first : (R.erase x).count x = R.count x - 1 := List.count_erase_self
    have second : ((R.erase x).erase x).count x = (R.erase x).count x - 1 := List.count_erase_self
    rw [second, first]
    omega
  · have first : (R.erase c).count x = R.count x := List.count_erase_of_ne equal
    have second : ((R.erase c).erase c).count x = (R.erase c).count x :=
      List.count_erase_of_ne equal
    rw [second, first]

/-- A region whose letters occur before and after derives to `canon`. -/
theorem listDerivesCanonRegion (L Rt : List Nat) :
    ∀ (n : Nat) (R : List Nat), R.length ≤ n →
      (∀ c ∈ R, c ∈ L) → (∀ c ∈ R, c ∈ Rt) →
      ListDerives (L ++ R ++ Rt) (L ++ canon R ++ Rt) := by
  intro n
  induction n with
  | zero =>
      intro R length _ _
      have empty : R = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp length)
      subst empty
      have canonNil : canon [] = [] := by simp [canon, Examples.parityReduce]
      rw [canonNil]
      exact S5_107.ListDerives.refl _
  | succ n ih =>
      intro R length before after
      by_cases repeated : ∃ c ∈ R, 2 ≤ R.count c
      · obtain ⟨c, memC, multiple⟩ := repeated
        have memErase : c ∈ R.erase c := by
          apply List.count_pos_iff.mp
          rw [List.count_erase_self]
          omega
        have perm1 : R.Perm (c :: R.erase c) := List.perm_cons_erase memC
        have perm2 : (R.erase c).Perm (c :: (R.erase c).erase c) := List.perm_cons_erase memErase
        have permutation : R.Perm (c :: c :: (R.erase c).erase c) := perm1.trans (perm2.cons c)
        have step1 := listDerivesRegionPerm Rt permutation L before after
        have step2 := listDerivesDeleteSquare L Rt [] ((R.erase c).erase c) c (before c memC)
          (after c memC)
        have subset : ∀ x ∈ (R.erase c).erase c, x ∈ R := fun x mem =>
          List.mem_of_mem_erase (List.mem_of_mem_erase mem)
        have shorter : ((R.erase c).erase c).length ≤ n := by
          have l1 : (R.erase c).length = R.length - 1 := List.length_erase_of_mem memC
          have l2 : ((R.erase c).erase c).length = (R.erase c).length - 1 :=
            List.length_erase_of_mem memErase
          have pos : 0 < R.length := List.length_pos_of_mem memC
          omega
        have step3 := ih ((R.erase c).erase c) shorter (fun x mem => before x (subset x mem))
          (fun x mem => after x (subset x mem))
        have canonEq : canon ((R.erase c).erase c) = canon R :=
          canon_eq_of_parity (fun x => count_erase_erase R c x multiple)
        rw [canonEq] at step3
        refine step1.trans (S5_107.ListDerives.trans ?_ step3)
        simpa [List.append_assoc] using step2
      · have bound : ∀ x, R.count x ≤ 1 := by
          intro x
          apply Classical.byContradiction
          intro large
          exact repeated ⟨x, List.count_pos_iff.mp (by omega), by omega⟩
        exact listDerivesRegionPerm Rt (canon_perm_of_count_le_one bound).symm L before after

end SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleSwap

import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808RunSort

/-! Generic normal-form properties of the existing run sorter. These do not
construct a word canonicalizer or assert uniqueness from a block multiset. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808RunNormal

open Msg0524Parity808RunSort

def BeforeBarrier (key : Nat) : List (Nat × Nat) → Prop
  | [] => True
  | head :: tail => head.2 = 0 ∨ (key ≤ head.1 ∧ BeforeBarrier key tail)

def RunSorted : List (Nat × Nat) → Prop
  | [] => True
  | head :: tail => RunSorted tail ∧ (head.2 = 0 ∨ BeforeBarrier head.1 tail)

def singletonBlocks : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | head :: tail => if head.2 = 0 then head :: singletonBlocks tail else singletonBlocks tail

theorem before_mono (small large : Nat) (le : small ≤ large) (blocks : List (Nat × Nat))
    (bound : BeforeBarrier large blocks) : BeforeBarrier small blocks := by
  induction blocks with
  | nil => trivial
  | cons head tail ih =>
    rcases bound with single | ⟨headBound,tailBound⟩
    · exact Or.inl single
    · exact Or.inr ⟨Nat.le_trans le headBound,ih tailBound⟩

theorem before_insert (key : Nat) (block : Nat × Nat) (blocks : List (Nat × Nat))
    (lower : key ≤ block.1) (bound : BeforeBarrier key blocks) :
    BeforeBarrier key (Msg0524Parity808RunSort.insert block blocks) := by
  induction blocks with
  | nil => exact Or.inr ⟨lower,True.intro⟩
  | cons head tail ih =>
    by_cases stop : head.2 = 0 ∨ block.1 ≤ head.1
    · rw [Msg0524Parity808RunSort.insert,if_pos stop]
      exact Or.inr ⟨lower,bound⟩
    · have notSingle : head.2 ≠ 0 := fun h => stop (Or.inl h)
      have body := bound.resolve_left notSingle
      rw [Msg0524Parity808RunSort.insert,if_neg stop]
      exact Or.inr ⟨body.1,ih body.2⟩

theorem insert_sorted (block : Nat × Nat) (blocks : List (Nat × Nat))
    (sorted : RunSorted blocks) : RunSorted (Msg0524Parity808RunSort.insert block blocks) := by
  induction blocks with
  | nil => exact ⟨True.intro,Or.inr True.intro⟩
  | cons head tail ih =>
    by_cases stop : head.2 = 0 ∨ block.1 ≤ head.1
    · rw [Msg0524Parity808RunSort.insert,if_pos stop]
      refine ⟨sorted,Or.inr ?_⟩
      rcases stop with single | le
      · exact Or.inl single
      · rcases sorted.2 with single | bound
        · exact Or.inl single
        · exact Or.inr ⟨le,before_mono block.1 head.1 le tail bound⟩
    · have notSingle : head.2 ≠ 0 := fun h => stop (Or.inl h)
      have headLower : head.1 ≤ block.1 := by omega
      rw [Msg0524Parity808RunSort.insert,if_neg stop]
      exact ⟨ih sorted.1,Or.inr (before_insert head.1 block tail headLower
        (sorted.2.resolve_left notSingle))⟩

theorem sortRuns_sorted (blocks : List (Nat × Nat)) : RunSorted (sortRuns blocks) := by
  induction blocks with
  | nil => trivial
  | cons head tail ih =>
    by_cases single : head.2 = 0
    · rw [sortRuns,if_pos single]
      exact ⟨ih,Or.inl single⟩
    · rw [sortRuns,if_neg single]
      exact insert_sorted head (sortRuns tail) ih

theorem insert_eq_cons (block : Nat × Nat) (blocks : List (Nat × Nat))
    (bound : BeforeBarrier block.1 blocks) :
    Msg0524Parity808RunSort.insert block blocks = block :: blocks := by
  cases blocks with
  | nil => rfl
  | cons head tail =>
    have stop : head.2 = 0 ∨ block.1 ≤ head.1 := by
      rcases bound with single | body
      · exact Or.inl single
      · exact Or.inr body.1
    exact if_pos stop

theorem sortRuns_fixed (blocks : List (Nat × Nat)) (sorted : RunSorted blocks) :
    sortRuns blocks = blocks := by
  induction blocks with
  | nil => rfl
  | cons head tail ih =>
    by_cases single : head.2 = 0
    · simp only [sortRuns,if_pos single,ih sorted.1]
    · rw [sortRuns,if_neg single,ih sorted.1]
      exact insert_eq_cons head tail (sorted.2.resolve_left single)

theorem sortRuns_fixed_iff (blocks : List (Nat × Nat)) :
    sortRuns blocks = blocks ↔ RunSorted blocks := by
  constructor
  · intro fixed
    exact fixed ▸ sortRuns_sorted blocks
  · exact sortRuns_fixed blocks

theorem sortRuns_idempotent (blocks : List (Nat × Nat)) :
    sortRuns (sortRuns blocks) = sortRuns blocks :=
  sortRuns_fixed (sortRuns blocks) (sortRuns_sorted blocks)

theorem insert_singletons (block : Nat × Nat) (repeated : block.2 ≠ 0)
    (blocks : List (Nat × Nat)) :
    singletonBlocks (Msg0524Parity808RunSort.insert block blocks) = singletonBlocks blocks := by
  induction blocks with
  | nil => simp only [Msg0524Parity808RunSort.insert,singletonBlocks,if_neg repeated]
  | cons head tail ih =>
    by_cases stop : head.2 = 0 ∨ block.1 ≤ head.1
    · rw [Msg0524Parity808RunSort.insert,if_pos stop]
      exact if_neg repeated
    · have notSingle : head.2 ≠ 0 := fun h => stop (Or.inl h)
      simp only [Msg0524Parity808RunSort.insert,if_neg stop,singletonBlocks,if_neg notSingle]
      exact ih

theorem sortRuns_singletons (blocks : List (Nat × Nat)) :
    singletonBlocks (sortRuns blocks) = singletonBlocks blocks := by
  induction blocks with
  | nil => rfl
  | cons head tail ih =>
    by_cases single : head.2 = 0
    · simp only [sortRuns,singletonBlocks,if_pos single,ih]
    · rw [sortRuns,if_neg single,insert_singletons head single]
      simpa only [singletonBlocks,if_neg single] using ih

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808RunNormal

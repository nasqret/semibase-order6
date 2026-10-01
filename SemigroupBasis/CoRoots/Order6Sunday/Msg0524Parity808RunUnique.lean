import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808RunNormal

/-! Permutation-invariant normal forms inside singleton-separated runs.
Faithful keys allow identical duplicate blocks but exclude different block
counts at one letter. No word-spine wrapper or factor semantics is imported. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808RunUnique

open Msg0524Parity808RunSort
open Msg0524Parity808RunNormal
open Msg0524Parity808Gather (LD)

def AllRepeated (blocks : List (Nat × Nat)) : Prop := ∀ b ∈ blocks, b.2 ≠ 0

def FaithfulKeys (blocks : List (Nat × Nat)) : Prop :=
  ∀ b ∈ blocks, ∀ c ∈ blocks, b.1 = c.1 → b = c

theorem allRepeated_perm (left right : List (Nat × Nat)) (perm : left.Perm right)
    (pure : AllRepeated left) : AllRepeated right := by
  intro b member
  exact pure b (perm.mem_iff.mpr member)

theorem faithfulKeys_perm (left right : List (Nat × Nat)) (perm : left.Perm right)
    (faithful : FaithfulKeys left) : FaithfulKeys right := by
  intro b hb c hc same
  exact faithful b (perm.mem_iff.mpr hb) c (perm.mem_iff.mpr hc) same

theorem faithfulKeys_of_nodup (blocks : List (Nat × Nat))
    (distinct : (blocks.map Prod.fst).Nodup) : FaithfulKeys blocks := by
  induction blocks with
  | nil => intro b hb; cases hb
  | cons head tail ih =>
    have hd : head.1 ∉ tail.map Prod.fst ∧ (tail.map Prod.fst).Nodup := by
      simpa only [List.map_cons,List.nodup_cons] using distinct
    intro b hb c hc same
    rcases List.mem_cons.mp hb with hb | hb
    · subst b
      rcases List.mem_cons.mp hc with hc | hc
      · exact hc.symm
      · have member : head.1 ∈ tail.map Prod.fst := by
          rw [same]
          exact List.mem_map_of_mem hc
        exact False.elim (hd.1 member)
    · rcases List.mem_cons.mp hc with hc | hc
      · subst c
        have member : head.1 ∈ tail.map Prod.fst := by
          rw [← same]
          exact List.mem_map_of_mem hb
        exact False.elim (hd.1 member)
      · exact ih hd.2 b hb c hc same

theorem before_all (key : Nat) (blocks : List (Nat × Nat)) (pure : AllRepeated blocks)
    (bound : BeforeBarrier key blocks) : ∀ b ∈ blocks, key ≤ b.1 := by
  induction blocks with
  | nil => intro b hb; cases hb
  | cons head tail ih =>
    have body := bound.resolve_left (pure head (by simp))
    intro b member
    rcases List.mem_cons.mp member with same | member
    · subst b; exact body.1
    · exact ih (fun c hc => pure c (List.mem_cons_of_mem head hc)) body.2 b member

theorem head_min (head : Nat × Nat) (tail : List (Nat × Nat))
    (pure : AllRepeated (head :: tail)) (sorted : RunSorted (head :: tail)) :
    ∀ b ∈ head :: tail, head.1 ≤ b.1 := by
  intro b member
  rcases List.mem_cons.mp member with same | member
  · subst b; exact Nat.le_refl _
  · exact before_all head.1 tail (fun c hc => pure c (List.mem_cons_of_mem head hc))
      (sorted.2.resolve_left (pure head (by simp))) b member

theorem sorted_perm_eq (left right : List (Nat × Nat)) (perm : left.Perm right)
    (pure : AllRepeated left) (faithful : FaithfulKeys left)
    (leftSorted : RunSorted left) (rightSorted : RunSorted right) : left = right := by
  induction left generalizing right with
  | nil => exact perm.nil_eq
  | cons head tail ih =>
    cases right with
    | nil => have impossible := perm.length_eq; simp at impossible
    | cons other rest =>
      have otherMember : other ∈ head :: tail := perm.mem_iff.mpr (by simp)
      have headMember : head ∈ other :: rest := perm.mem_iff.mp (by simp)
      have forward := head_min head tail pure leftSorted other otherMember
      have backward := head_min other rest (allRepeated_perm _ _ perm pure) rightSorted head headMember
      have same : head = other := faithful head (by simp) other otherMember
        (Nat.le_antisymm forward backward)
      subst other
      have pureTail : AllRepeated tail := fun b hb => pure b (List.mem_cons_of_mem head hb)
      have faithfulTail : FaithfulKeys tail := fun b hb c hc eq =>
        faithful b (List.mem_cons_of_mem head hb) c (List.mem_cons_of_mem head hc) eq
      exact congrArg (List.cons head) (ih rest perm.cons_inv pureTail faithfulTail leftSorted.1 rightSorted.1)

theorem sortRuns_perm_eq (left right : List (Nat × Nat)) (perm : left.Perm right)
    (pure : AllRepeated left) (faithful : FaithfulKeys left) : sortRuns left = sortRuns right := by
  have leftPerm := sortRuns_perm left
  have rightPerm := sortRuns_perm right
  exact sorted_perm_eq (sortRuns left) (sortRuns right)
    (leftPerm.trans (perm.trans rightPerm.symm))
    (allRepeated_perm _ _ leftPerm.symm pure)
    (faithfulKeys_perm _ _ leftPerm.symm faithful)
    (sortRuns_sorted left) (sortRuns_sorted right)

theorem sortRuns_perm_eq_of_nodup (left right : List (Nat × Nat)) (perm : left.Perm right)
    (pure : AllRepeated left) (distinct : (left.map Prod.fst).Nodup) :
    sortRuns left = sortRuns right :=
  sortRuns_perm_eq left right perm pure (faithfulKeys_of_nodup left distinct)

theorem insert_append_barrier (block : Nat × Nat) (run : List (Nat × Nat))
    (marker : Nat × Nat) (tail : List (Nat × Nat)) (single : marker.2 = 0) :
    Msg0524Parity808RunSort.insert block (run ++ marker :: tail) =
      Msg0524Parity808RunSort.insert block run ++ marker :: tail := by
  induction run with
  | nil => simp [Msg0524Parity808RunSort.insert,single]
  | cons head rest ih =>
    by_cases stop : head.2 = 0 ∨ block.1 ≤ head.1
    · simp only [List.cons_append,Msg0524Parity808RunSort.insert,if_pos stop]
    · simp only [List.cons_append,Msg0524Parity808RunSort.insert,if_neg stop]
      rw [ih]

theorem sortRuns_append_barrier (run : List (Nat × Nat)) (marker : Nat × Nat)
    (tail : List (Nat × Nat)) (single : marker.2 = 0) :
    sortRuns (run ++ marker :: tail) = sortRuns run ++ marker :: sortRuns tail := by
  induction run with
  | nil => simp only [List.nil_append,sortRuns,if_pos single]
  | cons head rest ih =>
    by_cases headSingle : head.2 = 0
    · simp only [List.cons_append,sortRuns,if_pos headSingle,ih]
    · simp only [List.cons_append,sortRuns,if_neg headSingle]
      rw [ih,insert_append_barrier head (sortRuns rest) marker (sortRuns tail) single]

inductive SameRuns : List (Nat × Nat) → List (Nat × Nat) → Prop
  | last (left right : List (Nat × Nat)) (pure : AllRepeated left)
      (faithful : FaithfulKeys left) (perm : left.Perm right) : SameRuns left right
  | split (left right : List (Nat × Nat)) (marker : Nat × Nat)
      (leftTail rightTail : List (Nat × Nat)) (pure : AllRepeated left)
      (faithful : FaithfulKeys left) (perm : left.Perm right) (single : marker.2 = 0)
      (remaining : SameRuns leftTail rightTail) :
      SameRuns (left ++ marker :: leftTail) (right ++ marker :: rightTail)

theorem sameRuns_sort_eq {left right : List (Nat × Nat)} (same : SameRuns left right) :
    sortRuns left = sortRuns right := by
  induction same with
  | last left right pure faithful perm => exact sortRuns_perm_eq left right perm pure faithful
  | split left right marker leftTail rightTail pure faithful perm single remaining ih =>
    rw [sortRuns_append_barrier left marker leftTail single,
      sortRuns_append_barrier right marker rightTail single,
      sortRuns_perm_eq left right perm pure faithful,ih]

theorem sameRuns_derives {left right : List (Nat × Nat)} (same : SameRuns left right)
    (suffix : List Nat) (nonempty : suffix ≠ []) :
    LD (render left ++ suffix) (render right ++ suffix) := by
  have first := sortRuns_derives left suffix nonempty
  have second := sortRuns_derives right suffix nonempty
  rw [sameRuns_sort_eq same] at first
  exact first.trans second.symm

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808RunUnique

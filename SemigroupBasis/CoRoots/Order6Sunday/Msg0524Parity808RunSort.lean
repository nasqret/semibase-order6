import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808Repeated

/-! Sort repeated-block runs without crossing singleton separators.
A block stores its letter and excess over one copy. A separate nonempty
suffix protects the distinguished final block. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808RunSort

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107 (ListDerives)
open Msg0524Parity808Gather
open Msg0524Parity808Repeated (blockCommute)

def blockWord (block : Nat × Nat) : List Nat := List.replicate (block.2+1) block.1
def render (blocks : List (Nat × Nat)) : List Nat := blocks.flatMap blockWord

def insert (block : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [block]
  | head :: tail =>
    if head.2 = 0 ∨ block.1 ≤ head.1 then block :: head :: tail
    else head :: insert block tail

def sortRuns : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | head :: tail =>
    if head.2 = 0 then head :: sortRuns tail else insert head (sortRuns tail)

theorem blockWord_nonempty (block : Nat × Nat) : blockWord block ≠ [] := by
  simp [blockWord,List.replicate_succ]

theorem render_cons_nonempty (head : Nat × Nat) (tail : List (Nat × Nat)) :
    render (head :: tail) ≠ [] := by
  simp [render,blockWord,List.replicate_succ]

theorem blockSwap (left right : Nat × Nat) (leftRepeated : 0 < left.2)
    (rightRepeated : 0 < right.2) (suffix : List Nat) (nonempty : suffix ≠ []) :
    LD (blockWord left ++ blockWord right ++ suffix)
      (blockWord right ++ blockWord left ++ suffix) := by
  have hl : left.2 - 1 + 2 = left.2 + 1 := by omega
  have hr : right.2 - 1 + 2 = right.2 + 1 := by omega
  simpa only [hl,hr,blockWord] using
    blockCommute left.1 right.1 (left.2-1) (right.2-1) suffix nonempty

theorem insert_perm (block : Nat × Nat) (blocks : List (Nat × Nat)) :
    (insert block blocks).Perm (block :: blocks) := by
  induction blocks with
  | nil => exact List.Perm.refl _
  | cons head tail ih =>
    by_cases stop : head.2 = 0 ∨ block.1 ≤ head.1
    · simp only [insert,if_pos stop]; exact List.Perm.refl _
    · simp only [insert,if_neg stop]
      exact (ih.cons head).trans (List.Perm.swap block head tail)

theorem sortRuns_perm (blocks : List (Nat × Nat)) : (sortRuns blocks).Perm blocks := by
  induction blocks with
  | nil => exact List.Perm.refl _
  | cons head tail ih =>
    by_cases single : head.2 = 0
    · simpa only [sortRuns,if_pos single] using ih.cons head
    · simpa only [sortRuns,if_neg single] using (insert_perm head (sortRuns tail)).trans (ih.cons head)

theorem insert_derives (block : Nat × Nat) (repeated : 0 < block.2)
    (blocks : List (Nat × Nat)) (suffix : List Nat) (nonempty : suffix ≠ []) :
    LD (blockWord block ++ render blocks ++ suffix) (render (insert block blocks) ++ suffix) := by
  induction blocks with
  | nil => simpa only [insert,render,List.flatMap_nil,List.flatMap_cons,List.append_nil] using
      (ListDerives.refl (basis := basis) (blockWord block ++ suffix))
  | cons head tail ih =>
    by_cases stop : head.2 = 0 ∨ block.1 ≤ head.1
    · simp only [insert,if_pos stop,render,List.flatMap_cons,List.append_assoc]
      exact ListDerives.refl _
    · have headRepeated : 0 < head.2 := by omega
      have tailNonempty : render tail ++ suffix ≠ [] := by
        cases suffix with
        | nil => exact False.elim (nonempty rfl)
        | cons c rest => simp
      have swap := blockSwap block head repeated headRepeated (render tail ++ suffix) tailNonempty
      have swap' : LD (blockWord block ++ render (head :: tail) ++ suffix)
          (blockWord head ++ (blockWord block ++ render tail ++ suffix)) := by
        simpa only [render,List.flatMap_cons,List.append_assoc] using swap
      simpa only [insert,if_neg stop,render,List.flatMap_cons,List.append_assoc] using
        swap'.trans (ih.prepend (blockWord head))

theorem sortRuns_derives (blocks : List (Nat × Nat)) (suffix : List Nat) (nonempty : suffix ≠ []) :
    LD (render blocks ++ suffix) (render (sortRuns blocks) ++ suffix) := by
  induction blocks with
  | nil => exact ListDerives.refl _
  | cons head tail ih =>
    have first : LD (render (head :: tail) ++ suffix)
        (blockWord head ++ render (sortRuns tail) ++ suffix) := by
      simpa only [render,List.flatMap_cons,List.append_assoc] using ih.prepend (blockWord head)
    by_cases single : head.2 = 0
    · simpa only [sortRuns,if_pos single,render,List.flatMap_cons,List.append_assoc] using first
    · have repeated : 0 < head.2 := by omega
      simpa only [sortRuns,if_neg single] using first.trans (insert_derives head repeated (sortRuns tail) suffix nonempty)

theorem singleton_stays (head : Nat × Nat) (tail : List (Nat × Nat)) (single : head.2 = 0) :
    sortRuns (head :: tail) = head :: sortRuns tail := by simp only [sortRuns,if_pos single]

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808RunSort

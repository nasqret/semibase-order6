import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808Gather

/-! Arbitrary repeated blocks commute and permute before a nonempty suffix.
The suffix restriction is essential; no final-block swap is asserted. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808Repeated

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107 (ListDerives)
open Msg0524Parity808Gather

theorem squareSwap (a b : Nat) (suffix : List Nat) (nonempty : suffix ≠ []) :
    LD (List.replicate 2 a ++ List.replicate 2 b ++ suffix)
      (List.replicate 2 b ++ List.replicate 2 a ++ suffix) := by
  cases suffix with
  | nil => exact False.elim (nonempty rfl)
  | cons c tail =>
    simpa [Word.singleton,Word.toList,Word.append] using
      ListDerives.ofWord (wordTailSquares (Word.singleton a) (Word.singleton b) ⟨c,tail⟩)

theorem growLeft (a b n m : Nat) (suffix : List Nat)
    (previous : LD (List.replicate (n+1) a ++ List.replicate m b ++ suffix)
      (List.replicate m b ++ List.replicate (n+1) a ++ suffix)) :
    LD (List.replicate (n+2) a ++ List.replicate m b ++ suffix)
      (List.replicate m b ++ List.replicate (n+2) a ++ suffix) := by
  have first := previous.prepend [a]
  have first' : LD (List.replicate (n+2) a ++ List.replicate m b ++ suffix)
      (a :: (List.replicate m b ++ List.replicate (n+1) a ++ suffix)) := by
    simpa only [List.replicate_succ,List.singleton_append,List.cons_append,List.append_assoc] using first
  have move := (gatherAcross a (List.replicate m b)).append (List.replicate n a ++ suffix)
  have second : LD (a :: (List.replicate m b ++ List.replicate (n+1) a ++ suffix))
      (List.replicate m b ++ List.replicate (n+2) a ++ suffix) := by
    simpa only [List.replicate_succ,List.singleton_append,List.cons_append,
      List.nil_append,List.append_assoc] using move
  exact first'.trans second

theorem blockCommute (a b i j : Nat) (suffix : List Nat) (nonempty : suffix ≠ []) :
    LD (List.replicate (i+2) a ++ List.replicate (j+2) b ++ suffix)
      (List.replicate (j+2) b ++ List.replicate (i+2) a ++ suffix) := by
  induction i with
  | zero =>
    induction j with
    | zero => exact squareSwap a b suffix nonempty
    | succ j ih =>
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using
        (growLeft b a (j+1) 2 suffix ih.symm).symm
  | succ i ih =>
    simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using growLeft a b (i+1) (j+2) suffix ih

def repeatedBlock (block : Nat × Nat) : List Nat := List.replicate (block.2+2) block.1
def renderRepeated (blocks : List (Nat × Nat)) : List Nat := blocks.flatMap repeatedBlock

theorem repeated_perm {left right : List (Nat × Nat)} (permutation : left.Perm right)
    (suffix : List Nat) (nonempty : suffix ≠ []) :
    LD (renderRepeated left ++ suffix) (renderRepeated right ++ suffix) := by
  induction permutation generalizing suffix with
  | nil => exact ListDerives.refl _
  | cons block _ ih =>
    simpa only [renderRepeated,List.flatMap_cons,List.append_assoc] using
      (ih suffix nonempty).prepend (repeatedBlock block)
  | swap x y rest =>
    have restNonempty : renderRepeated rest ++ suffix ≠ [] := by
      cases suffix with
      | nil => exact False.elim (nonempty rfl)
      | cons c tail => simp
    simpa only [renderRepeated,List.flatMap_cons,repeatedBlock,List.append_assoc] using
      blockCommute y.1 x.1 y.2 x.2 (renderRepeated rest ++ suffix) restNonempty
  | trans _ _ first second => exact (first suffix nonempty).trans (second suffix nonempty)

def sortRepeated (blocks : List (Nat × Nat)) : List (Nat × Nat) :=
  blocks.mergeSort (fun left right => decide (left.1 ≤ right.1))

theorem sortRepeated_perm (blocks : List (Nat × Nat)) : (sortRepeated blocks).Perm blocks :=
  List.mergeSort_perm _ _

theorem sortRepeated_derives (blocks : List (Nat × Nat)) (suffix : List Nat) (nonempty : suffix ≠ []) :
    LD (renderRepeated blocks ++ suffix) (renderRepeated (sortRepeated blocks) ++ suffix) :=
  repeated_perm (sortRepeated_perm blocks).symm suffix nonempty

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808Repeated

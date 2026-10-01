import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5369SemanticKey
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Exact screened B8 calculus for the literal S5369 table. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0534S5369Derivations

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107 (ListDerives)
open Msg0524S5369Evaluator Msg0524S5369Observations Msg0524S5369SemanticKey

def law0 : Identity Nat := ⟨⟨0,[0,1]⟩,⟨0,[1,0]⟩⟩
def law1 : Identity Nat := ⟨⟨0,[1,2]⟩,⟨0,[2,1]⟩⟩
def law2 : Identity Nat := ⟨⟨0,[0,0,1]⟩,⟨0,[0,1,1]⟩⟩
def law3 : Identity Nat := ⟨⟨0,[0,0,1]⟩,⟨0,[1,1,1]⟩⟩
def law4 : Identity Nat := ⟨⟨0,[0,1,2]⟩,⟨0,[1,1,2]⟩⟩
def law5 : Identity Nat := ⟨⟨0,[0,0,0,0]⟩,⟨0,[0,0,0,1]⟩⟩
def law6 : Identity Nat := ⟨⟨0,[0,0,0,0]⟩,⟨0,[0,1,2,3]⟩⟩
def law7 : Identity Nat := ⟨⟨0,[1,2,3,4]⟩,⟨0,[0,0,0,0]⟩⟩
def basis : List (Identity Nat) := [law0,law1,law2,law3,law4,law5,law6,law7]

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply valid_of_key
  all_goals refine ⟨rfl, by decide, ?_⟩
  all_goals intro x
  all_goals by_cases h0 : x = 0
  all_goals by_cases h1 : x = 1
  all_goals by_cases h2 : x = 2
  all_goals simp [law0,law1,law2,law3,law4,law5,law6,law7,
    Word.toList,lengthCap,h0,h1,h2,eq_comm]

abbrev LD := ListDerives basis

theorem lawSubstitution (law : Identity Nat) (member : law ∈ basis)
    (substitution : Nat → Word Nat) :
    LD (law.lhs.toList.flatMap (fun x => (substitution x).toList))
      (law.rhs.toList.flatMap (fun x => (substitution x).toList)) := by
  simpa only [Word.toList_bind] using
    ListDerives.ofWord ((Derives.fromBasis member).subst substitution)

private def sub3 (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | _ => z

theorem tailSwap (head x y : Nat) (suffix : List Nat) :
    LD (head :: x :: y :: suffix) (head :: y :: x :: suffix) := by
  have core := lawSubstitution law1 (by simp [basis])
    (sub3 (Word.singleton head) (Word.singleton x) (Word.singleton y))
  have fixed : LD [head,x,y] [head,y,x] := by
    simpa [law1,sub3,Word.toList,Word.singleton] using core
  exact fixed.append suffix

theorem tailPermutation {left right : List Nat} (permutation : left.Perm right)
    (head : Nat) : LD (head :: left) (head :: right) := by
  induction permutation generalizing head with
  | nil => exact ListDerives.refl _
  | cons x _ ih => exact (ih x).prepend [head]
  | swap x y rest => exact tailSwap head y x rest
  | trans _ _ first second => exact (first head).trans (second head)

theorem tripleToDouble (x y : Nat) : LD [x,x,x,y] [x,x,y,y] := by
  have core := lawSubstitution law2 (by simp [basis])
    (sub3 (Word.singleton x) (Word.singleton y) (Word.singleton 0))
  simpa [law2,sub3,Word.toList,Word.singleton] using core

theorem tripleToSingle (x y : Nat) : LD [x,x,x,y] [x,y,y,y] := by
  have core := lawSubstitution law3 (by simp [basis])
    (sub3 (Word.singleton x) (Word.singleton y) (Word.singleton 0))
  simpa [law3,sub3,Word.toList,Word.singleton] using core

theorem doubleShift (x y z : Nat) : LD [x,x,y,z] [x,y,y,z] := by
  have core := lawSubstitution law4 (by simp [basis])
    (sub3 (Word.singleton x) (Word.singleton y) (Word.singleton z))
  simpa [law4,sub3,Word.toList,Word.singleton] using core

private def sub5 (x a b c d : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => a
  | 2 => b
  | 3 => c
  | _ => d

theorem collapseFive (x a b c d : Nat) (tail : List Nat) :
    LD (x :: a :: b :: c :: d :: tail) [x,x,x,x,x] := by
  have core := lawSubstitution law7 (by simp [basis])
    (sub5 (Word.singleton x) (Word.singleton a) (Word.singleton b)
      (Word.singleton c) ⟨d,tail⟩)
  simpa [law7,sub5,Word.toList,Word.singleton] using core

theorem long_normal (word : Word Nat) (long : 5 ≤ word.toList.length) :
    LD word.toList [word.head,word.head,word.head,word.head,word.head] := by
  rcases word with ⟨x,tail⟩
  cases tail with
  | nil => simp [Word.toList] at long
  | cons a tail =>
    cases tail with
    | nil => simp [Word.toList] at long
    | cons b tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons c tail =>
        cases tail with
        | nil => simp [Word.toList] at long
        | cons d tail => exact collapseFive x a b c d tail

theorem long_derives (left right : Word Nat) (heads : left.head = right.head)
    (longLeft : 5 ≤ left.toList.length) (longRight : 5 ≤ right.toList.length) :
    Derives basis left right := by
  have first := long_normal left longLeft
  have second := long_normal right longRight
  rw [heads] at first
  have lists := first.trans second.symm
  cases left
  cases right
  exact _root_.SemigroupBasis.CoRoots.S5_107.ListDerives.toWord lists

end SemigroupBasis.CoRoots.Order6Sunday.Msg0534S5369Derivations

import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5352SemanticKey
import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662SemanticKey
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.CappedListNormalization
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Exact raw4 calculus for S5352. Proper-prefix permutations and a
terminal-dependent budget instantiate the existing capped-list engine. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5352Derivations

open SemigroupBasis
open Msg0524S5352Evaluator Msg0524S5352Observations
open Msg0524S5352SemanticKey
open Msg0524S9662SemanticKey (snoc toList_snoc)
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.Order6Day7.LeeZhang

def law0 : Identity Nat := ⟨⟨0,[0,0]⟩,⟨0,[0,0,0]⟩⟩
def law1 : Identity Nat := ⟨⟨0,[1,0]⟩,⟨1,[0,0]⟩⟩
def law2 : Identity Nat := ⟨⟨0,[1,2]⟩,⟨1,[0,2]⟩⟩
def law3 : Identity Nat := ⟨⟨0,[0,1,1,1,0]⟩,⟨0,[0,0,1,1,1]⟩⟩
def basis : List (Identity Nat) := [law0,law1,law2,law3]

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals apply valid_of_key
  all_goals refine ⟨?_, by decide⟩
  all_goals intro x
  all_goals by_cases h0 : x = 0
  all_goals by_cases h1 : x = 1
  all_goals by_cases h2 : x = 2
  all_goals simp [Word.toList, h0, h1, h2, eq_comm]

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

theorem fourToThree (x : Nat) : LD [x,x,x,x] [x,x,x] := by
  have core := (lawSubstitution law0 (by simp [basis]) (fun _ => Word.singleton x)).symm
  simpa [law0, Word.toList, Word.singleton] using core

theorem prefixSwap (x y : Nat) (rest : List Nat) (terminal : Nat) :
    LD (x :: y :: (rest ++ [terminal])) (y :: x :: (rest ++ [terminal])) := by
  have core := lawSubstitution law2 (by simp [basis])
    (sub3 (Word.singleton x) (Word.singleton y) (snoc rest terminal))
  have represented : (snoc rest terminal).head :: (snoc rest terminal).tail = rest ++ [terminal] :=
    toList_snoc rest terminal
  simpa [law2, sub3, Word.toList, Word.singleton, represented] using core

theorem prefixPermutation {left right : List Nat} (permutation : left.Perm right) (terminal : Nat) :
    LD (left ++ [terminal]) (right ++ [terminal]) := by
  induction permutation with
  | nil => exact ListDerives.refl _
  | cons x _ ih => simpa only [List.cons_append, List.singleton_append] using ih.prepend [x]
  | swap x y rest => exact prefixSwap y x rest terminal
  | trans _ _ first second => exact first.trans second

theorem terminalContraction (front rest : List Nat) (x : Nat) :
    LD (front ++ [x,x,x] ++ rest ++ [x]) (front ++ [x,x] ++ rest ++ [x]) := by
  have first := prefixPermutation
    ((List.perm_append_comm (l₁ := [x,x,x]) (l₂ := rest)).append_left front) x
  have middle := (fourToThree x).prepend (front ++ rest)
  have final := prefixPermutation
    ((List.perm_append_comm (l₁ := rest) (l₂ := [x,x])).append_left front) x
  simp only [List.append_assoc, List.cons_append, List.nil_append] at first middle final ⊢
  exact first.trans (middle.trans final)

def prefixSystem (terminal : Nat) : Normalization.System (List Nat) where
  rel left right := LD (left ++ [terminal]) (right ++ [terminal])
  refl := fun _ => .refl _
  symm := fun proof => proof.symm
  trans := fun first second => first.trans second

def prefixLimit (terminal letter : Nat) : Nat := if letter = terminal then 2 else 3

def prefixRules (terminal : Nat) : CappedList.Rules (prefixSystem terminal) (prefixLimit terminal) where
  swap := by
    intro front x y rest
    simpa only [prefixSystem, List.append_assoc, List.cons_append] using
      (prefixSwap x y rest terminal).prepend front
  contract := by
    intro front x rest
    by_cases same : x = terminal
    · subst x
      simpa only [prefixSystem, prefixLimit, if_pos rfl, List.replicate_succ,
        List.replicate_zero, List.append_assoc, List.cons_append, List.nil_append] using
        terminalContraction front rest terminal
    · simpa only [prefixSystem, prefixLimit, if_neg same, List.replicate_succ,
        List.replicate_zero, List.append_assoc, List.cons_append, List.nil_append] using
        (fourToThree x).context front (rest ++ [terminal])

def normalPrefix (stem : List Nat) (terminal : Nat) : List Nat :=
  CappedList.normal (prefixLimit terminal) stem

theorem normalizePrefix (stem : List Nat) (terminal : Nat) :
    LD (stem ++ [terminal]) (normalPrefix stem terminal ++ [terminal]) :=
  (prefixRules terminal).normal_sound stem

theorem normalPrefix_count (stem : List Nat) (terminal x : Nat) :
    (normalPrefix stem terminal ++ [terminal]).count x = min ((stem ++ [terminal]).count x) 3 := by
  simp only [List.count_append, normalPrefix, CappedList.count_normal]
  by_cases same : x = terminal
  · subst x
    simp only [prefixLimit, if_true, List.count_singleton_self]
    omega
  · simp [prefixLimit, same, Ne.symm same]

theorem sameTerminal (left right : List Nat) (terminal : Nat)
    (counts : ∀ x, min ((left ++ [terminal]).count x) 3 = min ((right ++ [terminal]).count x) 3) :
    LD (left ++ [terminal]) (right ++ [terminal]) := by
  apply (prefixRules terminal).rel_of_counts
  intro x
  have total := counts x
  simp only [List.count_append] at total
  by_cases same : x = terminal
  · subst x
    simp only [prefixLimit, if_true]
    simp only [List.count_singleton_self] at total
    omega
  · simp only [prefixLimit, if_neg same]
    simpa [same, Ne.symm same] using total

theorem saturatedSwitch (x y : Nat) : LD [x,x,y,y,y,x] [x,x,x,y,y,y] := by
  have core := lawSubstitution law3 (by simp [basis])
    (sub3 (Word.singleton x) (Word.singleton y) (Word.singleton 0))
  simpa [law3, sub3, Word.toList, Word.singleton] using core

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5352Derivations

import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395EvenInsertion

/-! Unrestricted terminal-block gathering for the unchanged three-law
Parity808 family. No finite screen or semantic completeness is a premise. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808Gather

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107
open Msg0457S11395EvenInsertion (replicateAdd)

def law0 : Identity Nat := ⟨⟨0,[0]⟩,⟨0,[0,0,0]⟩⟩
def law1 : Identity Nat := ⟨⟨0,[0,1,1,2]⟩,⟨0,[1,1,0,2]⟩⟩
def law2 : Identity Nat := ⟨⟨0,[1,0]⟩,⟨1,[0,0]⟩⟩
def basis : List (Identity Nat) := [law0,law1,law2]
abbrev LD := ListDerives basis

private def sub3 (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | _ => z

theorem wordPower (u : Word Nat) :
    Derives basis (u ++ u) (((u ++ u) ++ u) ++ u) := by
  have core := (Derives.fromBasis (basis := basis) (e := law0) (by simp [basis])).subst
    (sub3 u u u)
  simpa [law0,sub3,Word.bind,Word.append,Word.singleton,List.append_assoc] using core

theorem wordGather (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (v ++ (u ++ u)) := by
  have core := (Derives.fromBasis (basis := basis) (e := law2) (by simp [basis])).subst
    (sub3 u v u)
  change Derives basis ((u ++ v) ++ u) ((v ++ u) ++ u) at core
  simpa only [Word.append_assoc] using core

theorem wordTailSquares (u v suffix : Word Nat) :
    Derives basis (((u ++ u) ++ (v ++ v)) ++ suffix)
      (((v ++ v) ++ (u ++ u)) ++ suffix) := by
  have first := (Derives.fromBasis (basis := basis) (e := law1) (by simp [basis])).subst
    (sub3 u v suffix)
  change Derives basis ((((u ++ u) ++ v) ++ v) ++ suffix)
    ((((u ++ v) ++ v) ++ u) ++ suffix) at first
  have first' : Derives basis (((u ++ u) ++ (v ++ v)) ++ suffix)
      (((u ++ (v ++ v)) ++ u) ++ suffix) := by
    simpa only [Word.append_assoc] using first
  exact first'.trans ((wordGather u (v ++ v)).appendRight suffix)

theorem fourToTwo (a : Nat) : LD [a,a,a,a] [a,a] := by
  simpa [Word.singleton,Word.append,Word.toList] using
    ListDerives.ofWord (wordPower (Word.singleton a)).symm

theorem gatherAcross (a : Nat) (middle : List Nat) :
    LD ([a] ++ middle ++ [a]) (middle ++ [a,a]) := by
  cases middle with
  | nil => exact ListDerives.refl _
  | cons b rest =>
    simpa [Word.singleton,Word.append,Word.toList,List.append_assoc] using
      ListDerives.ofWord (wordGather (Word.singleton a) ⟨b,rest⟩)

def eraseLetter (a : Nat) (word : List Nat) : List Nat :=
  word.filter (fun b => b != a)

/-- All occurrences of the actual final letter gather at the right edge.
The nonfinal letters retain their literal order, with no permutation premise. -/
theorem gatherTerminal (stem : List Nat) (a : Nat) :
    LD (stem ++ [a]) (eraseLetter a stem ++ List.replicate (stem.count a + 1) a) := by
  induction stem with
  | nil => exact ListDerives.refl _
  | cons b stem ih =>
    have first := ih.prepend [b]
    by_cases same : b = a
    · subst b
      have move := (gatherAcross a (eraseLetter a stem)).append (List.replicate (stem.count a) a)
      have second : LD (a :: (eraseLetter a stem ++ List.replicate (stem.count a + 1) a))
          (eraseLetter a stem ++ List.replicate (stem.count a + 1 + 1) a) := by
        simpa only [List.replicate_succ,List.singleton_append,List.cons_append,
          List.nil_append,List.append_assoc] using move
      simpa [eraseLetter,List.count_cons_self] using first.trans second
    · simpa [eraseLetter,same,Ne.symm same,List.count_cons] using first

def reducedExponent (n : Nat) : Nat :=
  if n < 2 then n else 2 + n % 2

theorem reducedExponent_small (n : Nat) (small : n < 4) : reducedExponent n = n := by
  unfold reducedExponent
  split <;> omega

theorem reducedExponent_period (n : Nat) (large : 4 ≤ n) :
    reducedExponent (n - 2) = reducedExponent n := by
  simp only [reducedExponent,if_neg (by omega : ¬ n - 2 < 2),if_neg (by omega : ¬ n < 2)]
  omega

theorem reducedExponent_bound (n : Nat) : reducedExponent n ≤ 3 := by
  unfold reducedExponent
  split <;> omega

theorem reducedExponent_positive (n : Nat) (positive : 0 < n) : 0 < reducedExponent n := by
  unfold reducedExponent
  split <;> omega

theorem reducedExponent_parity (n : Nat) : reducedExponent n % 2 = n % 2 := by
  unfold reducedExponent
  split <;> omega

theorem reducePower (a n : Nat) :
    LD (List.replicate n a) (List.replicate (reducedExponent n) a) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases small : n < 4
    · rw [reducedExponent_small n small]
      exact ListDerives.refl _
    · have large : 4 ≤ n := by omega
      have four : LD (List.replicate 4 a) (List.replicate 2 a) := fourToTwo a
      have first := four.append (List.replicate (n - 4) a)
      have size4 : 4 + (n - 4) = n := by omega
      have size2 : 2 + (n - 4) = n - 2 := by omega
      rw [← replicateAdd,← replicateAdd,size4,size2] at first
      have second := ih (n - 2) (by omega)
      rw [reducedExponent_period n large] at second
      exact first.trans second

/-- The final block is 1 for a singleton, 2 for a positive even count,
and 3 for an odd count at least3; all preceding letters are unchanged. -/
theorem gatherTerminalParity (stem : List Nat) (a : Nat) :
    LD (stem ++ [a])
      (eraseLetter a stem ++ List.replicate (reducedExponent (stem.count a + 1)) a) :=
  (gatherTerminal stem a).trans ((reducePower a (stem.count a + 1)).prepend (eraseLetter a stem))

theorem contextualGatherTerminalParity (front stem tail : List Nat) (a : Nat) :
    LD (front ++ stem ++ [a] ++ tail)
      (front ++ eraseLetter a stem ++ List.replicate (reducedExponent (stem.count a + 1)) a ++ tail) := by
  simpa only [List.append_assoc] using (gatherTerminalParity stem a).context front tail

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808Gather

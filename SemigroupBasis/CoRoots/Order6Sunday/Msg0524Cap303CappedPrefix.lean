import SemigroupBasis.CoRoots.Order6Sunday.ApprovedB3BridgesFinite
import SemigroupBasis.CoRoots.S5_303Invariant

/-! The exact approved Cap303 B3, with capped prefix reduction before two
fixed final positions. No bound on the word length or variable set occurs. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion

open SemigroupBasis
open SemigroupBasis.Examples

open ApprovedB3BridgesFinite

abbrev B3 : List (Identity Nat) := Cap303.approvedBasis

theorem tripleContraction (u : Word Nat) :
    Derives B3 ((u ++ u) ++ u) (u ++ u) := by
  have instantiated :=
    Derives.subst Cap303.approvedDerivesLaw0.symm (fun _ => u)
  change Derives B3 ((u ++ u) ++ u) (u ++ u) at instantiated
  exact instantiated

theorem rotate (u v : Word Nat) :
    Derives B3 ((u ++ v) ++ u) ((v ++ u) ++ u) := by
  let substitution : Nat → Word Nat := fun n => if n = 0 then u else v
  have instantiated := Derives.subst Cap303.approvedDerivesLaw1 substitution
  change Derives B3 ((u ++ v) ++ u) ((v ++ u) ++ u) at instantiated
  exact instantiated

theorem prefixSwap (u v q r : Word Nat) :
    Derives B3 (((u ++ v) ++ q) ++ r) (((v ++ u) ++ q) ++ r) := by
  let substitution : Nat → Word Nat := fun
    | 0 => u
    | 1 => v
    | 2 => q
    | _ => r
  have instantiated := Derives.subst Cap303.approvedDerivesLaw3 substitution
  change Derives B3 (((u ++ v) ++ q) ++ r) (((v ++ u) ++ q) ++ r)
    at instantiated
  exact instantiated

def pairWord (stem : List Nat) (p t : Nat) : Word Nat :=
  wordOfPrefixFinal (stem ++ [p]) t

@[simp] theorem toList_pairWord (stem : List Nat) (p t : Nat) :
    (pairWord stem p t).toList = stem ++ [p, t] := by
  simp [pairWord, toList_wordOfPrefixFinal, List.append_assoc]

@[simp] theorem pairWord_cons (x : Nat) (stem : List Nat) (p t : Nat) :
    pairWord (x :: stem) p t = Word.singleton x ++ pairWord stem p t := rfl

@[simp] private theorem prefixFinal_append_singleton
    (stem : List Nat) (p t : Nat) :
    wordOfPrefixFinal stem p ++ Word.singleton t =
      wordOfPrefixFinal (stem ++ [p]) t := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal, toList_wordOfPrefixFinal]

theorem prefixPermutation {a b : List Nat} (permutation : a.Perm b)
    (p t : Nat) : Derives B3 (pairWord a p t) (pairWord b p t) := by
  induction permutation with
  | nil => exact Derives.refl _
  | cons x _ ih =>
      simpa only [pairWord_cons] using Derives.prepend (Word.singleton x) ih
  | swap x y xs =>
      simpa [pairWord, wordOfPrefixFinal, prefixFinal_append_singleton,
        Word.append_assoc, List.append_assoc] using
        prefixSwap (Word.singleton y) (Word.singleton x)
          (wordOfPrefixFinal xs p) (Word.singleton t)
  | trans _ _ first second => exact first.trans second

theorem stemContext (front : List Nat) {a b : List Nat} {p t q r : Nat}
    (derivation : Derives B3 (pairWord a p t) (pairWord b q r)) :
    Derives B3 (pairWord (front ++ a) p t) (pairWord (front ++ b) q r) := by
  induction front with
  | nil => exact derivation
  | cons x xs ih =>
      simpa only [List.cons_append, pairWord_cons] using
        Derives.prepend (Word.singleton x) ih

theorem consToEnd (x : Nat) : ∀ stem : List Nat,
    (x :: stem).Perm (stem ++ [x])
  | [] => List.Perm.refl _
  | y :: ys =>
      (List.Perm.swap y x ys).trans (List.Perm.cons y (consToEnd x ys))

private theorem twoToEnd (x : Nat) (stem : List Nat) :
    (x :: x :: stem).Perm (stem ++ [x, x]) := by
  have first := consToEnd x (x :: stem)
  have second := (consToEnd x stem).append_right [x]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    first.trans second

theorem rotateAtEnd (front : List Nat) (p t : Nat) :
    Derives B3 (pairWord (front ++ [t]) p t)
      (pairWord (front ++ [p]) t t) := by
  have core : Derives B3 (pairWord [t] p t) (pairWord [p] t t) := by
    simpa [pairWord, wordOfPrefixFinal, Word.append_assoc] using
      rotate (Word.singleton t) (Word.singleton p)
  exact stemContext front core

private theorem contractReservedTwo (front : List Nat) (t : Nat) :
    Derives B3 (pairWord (front ++ [t]) t t) (pairWord front t t) := by
  have core : Derives B3 (pairWord [t] t t) (pairWord [] t t) := by
    simpa [pairWord, wordOfPrefixFinal, Word.append_assoc] using
      tripleContraction (Word.singleton t)
  simpa only [List.append_nil] using stemContext front core

private theorem contractReservedOne (front : List Nat) (p t : Nat) :
    Derives B3 (pairWord (front ++ [p, p]) p t)
      (pairWord (front ++ [p]) p t) := by
  have core : Derives B3 (pairWord [p, p] p t) (pairWord [p] p t) := by
    simpa [pairWord, wordOfPrefixFinal, Word.append_assoc] using
      Derives.appendRight (tripleContraction (Word.singleton p)) (Word.singleton t)
  exact stemContext front core

/-- The penultimate letter has one occurrence reserved, or two when the
last two letters agree. All other prefix letters may retain two copies. -/
def allowance (p t x : Nat) : Nat :=
  if x = p then (if p = t then 0 else 1) else 2

def reduceStem (p t : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := reduceStem p t xs
      if reduced.count x < allowance p t x then x :: reduced else reduced

theorem count_reduceStem (p t z : Nat) (stem : List Nat) :
    (reduceStem p t stem).count z = min (stem.count z) (allowance p t z) := by
  induction stem with
  | nil => simp [reduceStem]
  | cons x xs ih =>
      simp only [reduceStem]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at hcount
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx), ih]
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, ih]
          rw [ih] at hcount
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx), ih]

theorem deleteExtra (x : Nat) (stem : List Nat) (p t : Nat)
    (enough : allowance p t x ≤ stem.count x) :
    Derives B3 (pairWord (x :: stem) p t) (pairWord stem p t) := by
  by_cases xp : x = p
  · subst x
    by_cases pt : p = t
    · subst t
      exact (prefixPermutation (consToEnd p stem) p p).trans
        (contractReservedTwo stem p)
    · have positive : 0 < stem.count p := by
        simpa [allowance, pt] using enough
      have member : p ∈ stem := List.count_pos_iff.mp positive
      have expose : stem.Perm (p :: stem.erase p) := List.perm_cons_erase member
      have arrange : (p :: stem).Perm (stem.erase p ++ [p, p]) :=
        (List.Perm.cons p expose).trans (twoToEnd p (stem.erase p))
      have targetArrange : stem.Perm (stem.erase p ++ [p]) :=
        expose.trans (consToEnd p (stem.erase p))
      exact (prefixPermutation arrange p t).trans
        ((contractReservedOne (stem.erase p) p t).trans
          (prefixPermutation targetArrange.symm p t))
  · have two : 2 ≤ stem.count x := by simpa [allowance, xp] using enough
    have member : x ∈ stem := List.count_pos_iff.mp (by omega)
    have erasedPositive : 0 < (stem.erase x).count x := by
      rw [List.count_erase_self]
      omega
    have erasedMember : x ∈ stem.erase x := List.count_pos_iff.mp erasedPositive
    have expose : stem.Perm (x :: x :: (stem.erase x).erase x) :=
      (List.perm_cons_erase member).trans
        (List.Perm.cons x (List.perm_cons_erase erasedMember))
    have contraction :
        Derives B3 (pairWord (x :: x :: x :: (stem.erase x).erase x) p t)
          (pairWord (x :: x :: (stem.erase x).erase x) p t) := by
      simpa [pairWord, wordOfPrefixFinal, Word.append_assoc, List.append_assoc] using
        Derives.appendRight (tripleContraction (Word.singleton x))
          (pairWord ((stem.erase x).erase x) p t)
    exact (prefixPermutation (List.Perm.cons x expose) p t).trans
      (contraction.trans (prefixPermutation expose.symm p t))

/-- Constructive unrestricted capped reduction, retaining the two endpoints. -/
theorem normalizeStem : ∀ (stem : List Nat) (p t : Nat),
    Derives B3 (pairWord stem p t) (pairWord (reduceStem p t stem) p t)
  | [], p, t => Derives.refl _
  | x :: xs, p, t => by
      have tailNormal := normalizeStem xs p t
      have prefixed :
          Derives B3 (pairWord (x :: xs) p t)
            (pairWord (x :: reduceStem p t xs) p t) := by
        simpa only [pairWord_cons] using
          Derives.prepend (Word.singleton x) tailNormal
      by_cases kept : (reduceStem p t xs).count x < allowance p t x
      · simpa only [reduceStem, if_pos kept] using prefixed
      · have dropped := deleteExtra x (reduceStem p t xs) p t (by omega)
        simpa only [reduceStem, if_neg kept] using prefixed.trans dropped

example : reduceStem 1 2 [0, 0, 0, 1, 1, 1, 2, 2] = [0, 0, 1, 2, 2] := by decide
example : reduceStem 1 1 [1, 1, 1] = [] := by decide
example : B3 = [Cap303.approvedBasisLaw0, Cap303.approvedBasisLaw1,
    Cap303.approvedBasisLaw2] := rfl

end SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion

#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.tripleContraction
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.rotate
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.prefixSwap
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.prefixPermutation
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.rotateAtEnd
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.count_reduceStem
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.deleteExtra
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.normalizeStem

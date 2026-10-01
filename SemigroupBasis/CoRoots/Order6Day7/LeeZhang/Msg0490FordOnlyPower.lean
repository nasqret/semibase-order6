import SemigroupBasis.CoRoots.Order6Sunday.FordOnlyExactFinite
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Actual arbitrary-word gathering and contextual caps for the approved
FORDONLY four-law basis. Empty contexts are lists, never substitution images. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordOnly

open SemigroupBasis Order6Sunday S5_107

abbrev basis := FordOnlyExactFinite.basis
abbrev LD := ListDerives basis

private def twoWords (first second : Word Nat) : Nat → Word Nat
  | 0 => first
  | _ => second

theorem lawSubstitution (law : Identity Nat) (member : law ∈ basis)
    (substitution : Nat → Word Nat) :
    LD (law.lhs.toList.flatMap (fun x => (substitution x).toList))
      (law.rhs.toList.flatMap (fun x => (substitution x).toList)) := by
  simpa only [Word.toList_bind] using
    ListDerives.ofWord ((Derives.fromBasis member).subst substitution)

theorem gatherOne (letter : Nat) (middle suffix : List Nat) :
    LD (letter :: middle ++ letter :: suffix)
      (letter :: letter :: middle ++ suffix) := by
  cases middle with
  | nil => exact ListDerives.refl _
  | cons head tail =>
      have core := (lawSubstitution FordOnlyExactFinite.basisLaw1
        (by simp [basis, FordOnlyExactFinite.basis])
        (twoWords (Word.singleton letter) (listWordOfCons head tail))).symm
      simpa [FordOnlyExactFinite.basisLaw1, twoWords, Word.toList,
        Word.singleton, listWordOfCons, List.append_assoc] using core.append suffix

theorem fourToThree (letter : Nat) :
    LD [letter, letter, letter, letter] [letter, letter, letter] := by
  have core := (lawSubstitution FordOnlyExactFinite.basisLaw0
    (by simp [basis, FordOnlyExactFinite.basis]) (fun _ => Word.singleton letter)).symm
  simpa [FordOnlyExactFinite.basisLaw0, Word.toList, Word.singleton] using core

theorem contextualTriple (prefixWords suffix : List Nat) (letter : Nat)
    (context : prefixWords ≠ [] ∨ suffix ≠ []) :
    LD (prefixWords ++ [letter, letter, letter] ++ suffix)
      (prefixWords ++ [letter, letter] ++ suffix) := by
  cases prefixWords with
  | cons head tail =>
      have core := (lawSubstitution FordOnlyExactFinite.basisLaw3
        (by simp [basis, FordOnlyExactFinite.basis])
        (twoWords (listWordOfCons head tail) (Word.singleton letter))).symm
      simpa [FordOnlyExactFinite.basisLaw3, twoWords, Word.toList,
        Word.singleton, listWordOfCons, List.append_assoc] using core.append suffix
  | nil =>
      cases suffix with
      | nil => simp at context
      | cons head tail =>
          have core := (lawSubstitution FordOnlyExactFinite.basisLaw2
            (by simp [basis, FordOnlyExactFinite.basis])
            (twoWords (Word.singleton letter) (listWordOfCons head tail))).symm
          simpa [FordOnlyExactFinite.basisLaw2, twoWords, Word.toList,
            Word.singleton, listWordOfCons, List.append_assoc] using core

theorem capThreeExtra (letter extra : Nat) :
    LD (List.replicate (extra + 3) letter) [letter, letter, letter] := by
  induction extra with
  | zero => exact ListDerives.refl _
  | succ extra ih =>
      have first : LD (List.replicate (extra + 1 + 3) letter)
          (List.replicate (extra + 3) letter) := by
        rw [show extra + 1 + 3 = 4 + extra by omega,
          show extra + 3 = 3 + extra by omega]
        rw [← List.replicate_append_replicate, ← List.replicate_append_replicate]
        exact (fourToThree letter).append (List.replicate extra letter)
      exact first.trans ih

theorem capThree (letter count : Nat) :
    LD (List.replicate count letter) (List.replicate (min count 3) letter) := by
  by_cases small : count ≤ 3
  · rw [Nat.min_eq_left small]
    exact ListDerives.refl _
  · have large : 3 ≤ count := by omega
    rw [Nat.min_eq_right large]
    simpa [Nat.sub_add_cancel large] using capThreeExtra letter (count - 3)

theorem capTwoExtra (prefixWords suffix : List Nat) (letter extra : Nat)
    (context : prefixWords ≠ [] ∨ suffix ≠ []) :
    LD (prefixWords ++ List.replicate (extra + 2) letter ++ suffix)
      (prefixWords ++ [letter, letter] ++ suffix) := by
  induction extra with
  | zero => exact ListDerives.refl _
  | succ extra ih =>
      have guarded : prefixWords ≠ [] ∨ List.replicate extra letter ++ suffix ≠ [] := by
        rcases context with left | right
        · exact Or.inl left
        · exact Or.inr (fun empty => right (List.append_eq_nil_iff.mp empty).2)
      have first : LD (prefixWords ++ List.replicate (extra + 1 + 2) letter ++ suffix)
          (prefixWords ++ List.replicate (extra + 2) letter ++ suffix) := by
        rw [show extra + 1 + 2 = 3 + extra by omega,
          show extra + 2 = 2 + extra by omega]
        rw [← List.replicate_append_replicate, ← List.replicate_append_replicate]
        simpa [List.append_assoc] using
          contextualTriple prefixWords (List.replicate extra letter ++ suffix) letter guarded
      exact first.trans ih

theorem capTwo (prefixWords suffix : List Nat) (letter count : Nat)
    (context : prefixWords ≠ [] ∨ suffix ≠ []) :
    LD (prefixWords ++ List.replicate count letter ++ suffix)
      (prefixWords ++ List.replicate (min count 2) letter ++ suffix) := by
  by_cases small : count ≤ 2
  · rw [Nat.min_eq_left small]
    exact ListDerives.refl _
  · have large : 2 ≤ count := by omega
    rw [Nat.min_eq_right large]
    simpa [Nat.sub_add_cancel large] using
      capTwoExtra prefixWords suffix letter (count - 2) context

theorem gatherBlock (extra letter : Nat) (middle suffix : List Nat) :
    LD (List.replicate (extra + 1) letter ++ middle ++ letter :: suffix)
      (List.replicate (extra + 2) letter ++ middle ++ suffix) := by
  rw [← List.replicate_append_replicate, ← List.replicate_append_replicate]
  simpa [List.append_assoc] using
    (gatherOne letter middle suffix).prepend (List.replicate extra letter)

theorem gatherAll : ∀ (seen : Nat), 0 < seen → ∀ (letter : Nat) (middle rest : List Nat),
    LD (List.replicate seen letter ++ middle ++ rest)
      (List.replicate (seen + rest.count letter) letter ++
        middle ++ rest.filter (fun x => decide (x ≠ letter)))
  | seen, _, letter, middle, [] => by
      simp only [List.count_nil, Nat.add_zero, List.filter_nil]
      exact ListDerives.refl _
  | seen, positive, letter, middle, head :: tail => by
      by_cases equal : head = letter
      · subst head
        have first : LD (List.replicate seen letter ++ middle ++ letter :: tail)
            (List.replicate (seen + 1) letter ++ middle ++ tail) := by
          cases seen with
          | zero => omega
          | succ extra => exact gatherBlock extra letter middle tail
        have remaining := gatherAll (seen + 1) (by omega) letter middle tail
        have countEq : seen + (letter :: tail).count letter = (seen + 1) + tail.count letter := by
          simp
          omega
        apply first.trans
        rw [countEq]
        simpa using remaining
      · have remaining := gatherAll seen positive letter (middle ++ [head]) tail
        simpa [equal, List.count_cons_of_ne equal, List.append_assoc] using remaining
termination_by _ _ _ _ rest => rest.length

theorem gatherHead (letter : Nat) (tail : List Nat) :
    LD (letter :: tail)
      (List.replicate ((letter :: tail).count letter) letter ++
        tail.filter (fun x => decide (x ≠ letter))) := by
  simpa [List.count_cons_self, Nat.add_comm] using gatherAll 1 (by omega) letter [] tail

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordOnly

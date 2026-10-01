import SemigroupBasis.CoRoots.S5_254Assembly
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0446TailBudget

/-! A table-independent square-bank comparison theorem. Every algebraic
capability is an explicit input; this module neither instantiates them for
S6_9386 nor claims completeness of any displayed basis. The later B12 adapter
must prove centrality, triple-guarded insertion, and count preservation. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.CapThreeBank

open SemigroupBasis

abbrev bank := S5_254.renderSquareBank
abbrev LD := S5_107.ListDerives

def SameCaps (left right : List Nat) : Prop :=
  ∀ letter, Msg0446TailBudget.cap 3 (left.count letter) =
    Msg0446TailBudget.cap 3 (right.count letter)

structure Rules (basis : List (Identity Nat)) : Prop where
  centralPair : ∀ letter payload,
    LD basis ([letter, letter] ++ payload) (payload ++ [letter, letter])
  appendPairAtThree : ∀ letters letter, 3 ≤ letters.count letter →
    LD basis letters (letters ++ [letter, letter])
  preservesCounts : ∀ {left right}, LD basis left right → SameCaps left right

theorem bankPermutation {basis : List (Identity Nat)} (rules : Rules basis)
    {source target : List Nat} (permutation : source.Perm target) :
    LD basis (bank source) (bank target) := by
  induction permutation with
  | nil => exact S5_107.ListDerives.empty
  | cons letter _ induction =>
      simpa [bank, S5_254.renderSquareBank] using induction.prepend [letter, letter]
  | swap left right rest =>
      have swapped := rules.centralPair left [right, right]
      simpa [bank, S5_254.renderSquareBank, List.append_assoc] using
        (swapped.append (bank rest)).symm
  | trans _ _ first second => exact first.trans second

theorem insertBankHead {basis : List (Identity Nat)} (rules : Rules basis)
    (stem labels : List Nat) (letter : Nat)
    (triple : 3 ≤ (stem ++ bank labels).count letter) :
    LD basis (stem ++ bank labels) (stem ++ bank (letter :: labels)) := by
  have inserted := rules.appendPairAtThree (stem ++ bank labels) letter triple
  have moved := ((rules.centralPair letter (bank labels)).prepend stem).symm
  apply inserted.trans
  simpa [bank, S5_254.renderSquareBank, List.append_assoc] using moved

theorem stem_ge_three_of_head_absent (stem left right : List Nat) (letter : Nat)
    (same : SameCaps (stem ++ bank (letter :: left)) (stem ++ bank right))
    (absent : letter ∉ right) : 3 ≤ stem.count letter := by
  have components := (Msg0446TailBudget.cap_eq_iff 3 _ _).1 (same letter)
  have rightZero : right.count letter = 0 := List.count_eq_zero.mpr absent
  simp only [List.count_append, S5_254.count_renderSquareBank, List.count_cons_self] at components
  rw [rightZero] at components
  simp only [Nat.mul_zero, Nat.add_zero] at components
  omega

/-- Align arbitrary square banks with the same capped counts, in any common
stem. Matching labels are exposed by a permutation and moved into the stem.
An unmatched label can be deleted only when the surviving stem already has
three copies; that condition follows from the exact cap equality. -/
theorem align {basis : List (Identity Nat)} (rules : Rules basis)
    (stem left right : List Nat)
    (same : SameCaps (stem ++ bank left) (stem ++ bank right)) :
    LD basis (stem ++ bank left) (stem ++ bank right) := by
  cases left with
  | nil =>
      cases right with
      | nil => exact S5_107.ListDerives.refl _
      | cons letter tail =>
          have stemTriple : 3 ≤ stem.count letter :=
            stem_ge_three_of_head_absent stem tail [] letter
              (fun tested => (same tested).symm) (by simp)
          have tailTriple : 3 ≤ (stem ++ bank tail).count letter := by
            rw [List.count_append]
            omega
          have inserted := insertBankHead rules stem tail letter tailTriple
          have reducedSame : SameCaps (stem ++ bank []) (stem ++ bank tail) := by
            intro tested
            exact (same tested).trans (rules.preservesCounts inserted tested).symm
          have smaller : ([] : List Nat).length + tail.length <
              ([] : List Nat).length + (letter :: tail).length := by simp
          exact (align rules stem [] tail reducedSame).trans inserted
  | cons letter tail =>
      by_cases present : letter ∈ right
      · let nextStem := stem ++ [letter, letter]
        have reordered : LD basis (stem ++ bank right)
            (nextStem ++ bank (right.erase letter)) := by
          simpa [nextStem, bank, S5_254.renderSquareBank, List.append_assoc] using
            (bankPermutation rules (List.perm_cons_erase present)).prepend stem
        have reducedSame : SameCaps (nextStem ++ bank tail)
            (nextStem ++ bank (right.erase letter)) := by
          intro tested
          simpa [nextStem, bank, S5_254.renderSquareBank, List.append_assoc] using
            (same tested).trans (rules.preservesCounts reordered tested)
        have erasedLength := List.length_erase_of_mem present
        have smaller : tail.length + (right.erase letter).length <
            (letter :: tail).length + right.length := by
          simp only [List.length_cons]
          omega
        have recurse := align rules nextStem tail (right.erase letter) reducedSame
        have leftAligned : LD basis (stem ++ bank (letter :: tail))
            (nextStem ++ bank (right.erase letter)) := by
          simpa [nextStem, bank, S5_254.renderSquareBank, List.append_assoc] using recurse
        exact leftAligned.trans reordered.symm
      · have stemTriple := stem_ge_three_of_head_absent stem tail right letter same present
        have tailTriple : 3 ≤ (stem ++ bank tail).count letter := by
          rw [List.count_append]
          omega
        have inserted := insertBankHead rules stem tail letter tailTriple
        have reducedSame : SameCaps (stem ++ bank tail) (stem ++ bank right) := by
          intro tested
          exact (rules.preservesCounts inserted tested).trans (same tested)
        have smaller : tail.length + right.length < (letter :: tail).length + right.length := by
          simp only [List.length_cons]
          omega
        exact inserted.symm.trans (align rules stem tail right reducedSame)
termination_by left.length + right.length
decreasing_by all_goals simp_all only [List.length_cons, List.length_nil]

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.CapThreeBank

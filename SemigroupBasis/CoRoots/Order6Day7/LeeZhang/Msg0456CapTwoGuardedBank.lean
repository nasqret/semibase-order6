import SemigroupBasis.CoRoots.S5_254Assembly
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456FordNilSemantics
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456FordNilPower

/-! Unrestricted square-bank alignment with retained first-occurrence
anchors. All bank labels must already occur in the common stem. The actual
B23 adapter at the end proves every algebraic input. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.CapTwoGuardedBank

open SemigroupBasis

abbrev bank := S5_254.renderSquareBank
abbrev LD := S5_107.ListDerives

def SameCaps (left right : List Nat) : Prop :=
  ∀ letter, Msg0446TailBudget.cap 2 (left.count letter) =
    Msg0446TailBudget.cap 2 (right.count letter)

structure Rules (basis : List (Identity Nat)) : Prop where
  centralPair : ∀ stem letter payload, letter ∈ stem →
    LD basis (stem ++ [letter, letter] ++ payload) (stem ++ payload ++ [letter, letter])
  appendPairAtTwo : ∀ letters letter, 2 ≤ letters.count letter →
    LD basis letters (letters ++ [letter, letter])
  preservesCounts : ∀ {left right}, LD basis left right → SameCaps left right

theorem bankPermutation {basis : List (Identity Nat)} (rules : Rules basis)
    (stem : List Nat) {source target : List Nat} (permutation : source.Perm target)
    (seen : ∀ letter ∈ source, letter ∈ stem) :
    LD basis (stem ++ bank source) (stem ++ bank target) := by
  induction permutation generalizing stem with
  | nil => exact S5_107.ListDerives.refl _
  | cons letter _ induction =>
      simpa [bank, S5_254.renderSquareBank, List.append_assoc] using
        induction (stem ++ [letter, letter])
          (fun tested member => List.mem_append_left _
            (seen tested (List.mem_cons_of_mem letter member)))
  | swap left right rest =>
      have leftSeen := seen left (by simp)
      have swapped := rules.centralPair stem left [right, right] leftSeen
      simpa [bank, S5_254.renderSquareBank, List.append_assoc] using
        (swapped.append (bank rest)).symm
  | trans firstPermutation _ first second =>
      exact (first stem seen).trans (second stem
        (fun letter member => seen letter (firstPermutation.mem_iff.mpr member)))

theorem insertBankHead {basis : List (Identity Nat)} (rules : Rules basis)
    (stem labels : List Nat) (letter : Nat) (seen : letter ∈ stem)
    (repeated : 2 ≤ (stem ++ bank labels).count letter) :
    LD basis (stem ++ bank labels) (stem ++ bank (letter :: labels)) := by
  have inserted := rules.appendPairAtTwo (stem ++ bank labels) letter repeated
  have moved := (rules.centralPair stem letter (bank labels) seen).symm
  apply inserted.trans
  simpa [bank, S5_254.renderSquareBank, List.append_assoc] using moved

theorem stem_ge_two_of_head_absent (stem left right : List Nat) (letter : Nat)
    (same : SameCaps (stem ++ bank (letter :: left)) (stem ++ bank right))
    (absent : letter ∉ right) : 2 ≤ stem.count letter := by
  have components := (Msg0446TailBudget.cap_eq_iff 2 _ _).1 (same letter)
  have rightZero : right.count letter = 0 := List.count_eq_zero.mpr absent
  simp only [List.count_append, S5_254.count_renderSquareBank, List.count_cons_self] at components
  rw [rightZero] at components
  simp only [Nat.mul_zero, Nat.add_zero] at components
  omega

/-- Matching labels are moved into the common stem. An unmatched pair
can disappear only after exact cap equality proves two surviving copies. -/
theorem align {basis : List (Identity Nat)} (rules : Rules basis)
    (stem left right : List Nat)
    (leftSeen : ∀ letter ∈ left, letter ∈ stem)
    (rightSeen : ∀ letter ∈ right, letter ∈ stem)
    (same : SameCaps (stem ++ bank left) (stem ++ bank right)) :
    LD basis (stem ++ bank left) (stem ++ bank right) := by
  cases left with
  | nil =>
      cases right with
      | nil => exact S5_107.ListDerives.refl _
      | cons letter tail =>
          have stemTwo : 2 ≤ stem.count letter :=
            stem_ge_two_of_head_absent stem tail [] letter
              (fun tested => (same tested).symm) (by simp)
          have tailTwo : 2 ≤ (stem ++ bank tail).count letter := by
            rw [List.count_append]
            omega
          have inserted := insertBankHead rules stem tail letter (rightSeen letter (by simp)) tailTwo
          have reducedSame : SameCaps (stem ++ bank []) (stem ++ bank tail) := by
            intro tested
            exact (same tested).trans (rules.preservesCounts inserted tested).symm
          have tailSeen := fun tested member => rightSeen tested (List.mem_cons_of_mem letter member)
          have smaller : ([] : List Nat).length + tail.length <
              ([] : List Nat).length + (letter :: tail).length := by simp
          exact (align rules stem [] tail leftSeen tailSeen reducedSame).trans inserted
  | cons letter tail =>
      by_cases present : letter ∈ right
      · let nextStem := stem ++ [letter, letter]
        have reordered : LD basis (stem ++ bank right)
            (nextStem ++ bank (right.erase letter)) := by
          simpa [nextStem, bank, S5_254.renderSquareBank, List.append_assoc] using
            bankPermutation rules stem (List.perm_cons_erase present) rightSeen
        have reducedSame : SameCaps (nextStem ++ bank tail)
            (nextStem ++ bank (right.erase letter)) := by
          intro tested
          simpa [nextStem, bank, S5_254.renderSquareBank, List.append_assoc] using
            (same tested).trans (rules.preservesCounts reordered tested)
        have nextLeftSeen : ∀ tested ∈ tail, tested ∈ nextStem := by
          intro tested member
          exact List.mem_append_left _ (leftSeen tested (List.mem_cons_of_mem letter member))
        have nextRightSeen : ∀ tested ∈ right.erase letter, tested ∈ nextStem := by
          intro tested member
          exact List.mem_append_left _ (rightSeen tested
            ((List.perm_cons_erase present).mem_iff.mpr (List.mem_cons_of_mem letter member)))
        have erasedLength := List.length_erase_of_mem present
        have smaller : tail.length + (right.erase letter).length <
            (letter :: tail).length + right.length := by
          simp only [List.length_cons]
          omega
        have recurse := align rules nextStem tail (right.erase letter) nextLeftSeen nextRightSeen reducedSame
        have leftAligned : LD basis (stem ++ bank (letter :: tail))
            (nextStem ++ bank (right.erase letter)) := by
          simpa [nextStem, bank, S5_254.renderSquareBank, List.append_assoc] using recurse
        exact leftAligned.trans reordered.symm
      · have stemTwo := stem_ge_two_of_head_absent stem tail right letter same present
        have tailTwo : 2 ≤ (stem ++ bank tail).count letter := by
          rw [List.count_append]
          omega
        have inserted := insertBankHead rules stem tail letter (leftSeen letter (by simp)) tailTwo
        have reducedSame : SameCaps (stem ++ bank tail) (stem ++ bank right) := by
          intro tested
          exact (rules.preservesCounts inserted tested).trans (same tested)
        have tailSeen := fun tested member => leftSeen tested (List.mem_cons_of_mem letter member)
        have smaller : tail.length + right.length < (letter :: tail).length + right.length := by
          simp only [List.length_cons]
          omega
        exact inserted.symm.trans (align rules stem tail right tailSeen rightSeen reducedSame)
termination_by left.length + right.length
decreasing_by all_goals simp_all only [List.length_cons, List.length_nil]

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.CapTwoGuardedBank

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

def bankRules : CapTwoGuardedBank.Rules basis where
  centralPair := fun stem letter payload seen => listDerivesPairAcrossSeen stem payload letter seen
  appendPairAtTwo := listDerivesAppendPairOfCountGeTwo
  preservesCounts := fun derivation letter => listDerives_preserve_caps derivation letter

theorem listDerivesAlignBanks (stem left right : List Nat)
    (leftSeen : ∀ letter ∈ left, letter ∈ stem)
    (rightSeen : ∀ letter ∈ right, letter ∈ stem)
    (same : CapTwoGuardedBank.SameCaps
      (stem ++ CapTwoGuardedBank.bank left) (stem ++ CapTwoGuardedBank.bank right)) :
    S5_107.ListDerives basis
      (stem ++ CapTwoGuardedBank.bank left) (stem ++ CapTwoGuardedBank.bank right) :=
  CapTwoGuardedBank.align bankRules stem left right leftSeen rightSeen same

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

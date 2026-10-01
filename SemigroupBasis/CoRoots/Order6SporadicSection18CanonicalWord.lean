import SemigroupBasis.CoRoots.Order6SporadicSection18OrderedAlphabet
import SemigroupBasis.CoRoots.Order6SporadicSection18RunSegmentation

/-! The paper-facing canonical-word interface for Lemma18.5. Arbitrary words
are segmented using their GLOBAL simple-letter predicate, and the proved
raw-chain saturation is invoked with the exact ordered nonsimple alphabet. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis

def StartsN (letters : List Nat) : Prop :=
  ∃ head tail, letters = head :: tail ∧ letters.count head ≠ 1

def EndsN (letters : List Nat) : Prop :=
  EndsWithN (fun x => letters.count x ≠ 1) letters

def HasSimple (letters : List Nat) : Prop := ∃ x, letters.count x = 1

def CanonicalForm (letters : List Nat) : Prop :=
  ∃ (alphabet : List Nat) (first : Slot) (rest : List Slot),
    alphabet.Pairwise (· < ·) ∧ alphabet.Nodup ∧
    (∀ x, x ∈ alphabet ↔ x ∈ letters ∧ letters.count x ≠ 1) ∧
    rest ≠ [] ∧ first.gap = [] ∧ (∀ slot ∈ rest, slot.gap ≠ []) ∧
    (∀ slot ∈ first :: rest, ∀ x ∈ slot.gap, letters.count x = 1) ∧
    CanonicalChain alphabet (first :: rest) ∧ render (first :: rest) = letters

private theorem nonempty_member {α : Type} (letters : List α) (nonempty : letters ≠ []) :
    ∃ x, x ∈ letters := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs => exact ⟨x, by simp⟩

theorem CanonicalForm.hasSimple {letters : List Nat} (formed : CanonicalForm letters) : HasSimple letters := by
  obtain ⟨alphabet, first, rest, _, _, _, restNonempty, _, gapsNonempty, gapsSimple, _, _⟩ := formed
  obtain ⟨slot, slotMember⟩ := nonempty_member rest restNonempty
  obtain ⟨x, letterMember⟩ := nonempty_member slot.gap (gapsNonempty slot slotMember)
  exact ⟨x, gapsSimple slot (List.mem_cons_of_mem first slotMember) x letterMember⟩

theorem CanonicalForm.nonempty {letters : List Nat} (formed : CanonicalForm letters) : letters ≠ [] := by
  obtain ⟨x, one⟩ := formed.hasSimple
  intro empty
  rw [empty, List.count_nil] at one
  omega

/-- Explicitly expose the paper's nonempty, ordered square blocks, maximal
simple gaps, equal-or-disjoint supports and forbidden crossing condition. -/
theorem CanonicalForm.explicitBlocks {letters : List Nat} (formed : CanonicalForm letters) :
    ∃ first rest, render (first :: rest) = letters ∧ first.gap = [] ∧ rest ≠ [] ∧
      (∀ slot ∈ rest, slot.gap ≠ []) ∧
      (∀ slot ∈ first :: rest, slot.block ≠ [] ∧ slot.block.Pairwise (· < ·) ∧ slot.block.Nodup ∧
        (∀ x ∈ slot.block, letters.count x ≠ 1) ∧ (∀ x ∈ slot.gap, letters.count x = 1)) ∧
      OverlapClosed (first :: rest) ∧ CrossingClosed (first :: rest) := by
  obtain ⟨alphabet, first, rest, ordered, _, exactAlphabet, restNonempty, firstEmpty,
    gapsNonempty, gapsSimple, canonical, shape⟩ := formed
  refine ⟨first, rest, shape, firstEmpty, restNonempty, gapsNonempty, ?_, canonical.2.1, canonical.2.2⟩
  intro slot member
  have good := canonical.1 slot member
  refine ⟨good.1, good.ordered ordered, good.nodup ordered, ?_, gapsSimple slot member⟩
  intro x letter
  exact ((exactAlphabet x).mp (good.bounded x letter)).2

/-- Lemma18.5 for every finite word with a simple letter and globally
non-simple first/last letters. There is no fixed alphabet or length bound. -/
theorem lemma18_5 (letters : List Nat) (starts : StartsN letters) (ends : EndsN letters)
    (simple : HasSimple letters) :
    ∃ normal, ListDerives letters normal ∧ CanonicalForm normal := by
  let nonSimple : Nat → Prop := fun x => letters.count x ≠ 1
  let alphabet := nonSimpleAlphabet letters
  have ended : EndsWithN nonSimple letters := ends
  obtain ⟨first, rest, rawShape, runs⟩ := exists_rawRuns nonSimple letters ended
  have firstEmpty : first.gap = [] := runs.first_gap_empty (by
    obtain ⟨head, tail, shape, notOne⟩ := starts
    exact ⟨head, tail, rawShape.trans shape, notOne⟩)
  have hasOther : ∃ x, x ∈ rawRender (first :: rest) ∧ ¬ nonSimple x := by
    obtain ⟨x, one⟩ := simple
    have member : x ∈ letters := by
      by_cases present : x ∈ letters
      · exact present
      · have zero := List.count_eq_zero.mpr present
        have impossible : False := by omega
        exact False.elim impossible
    refine ⟨x, ?_, ?_⟩
    · rw [rawShape]
      exact member
    · intro notOne
      exact notOne one
  have restNonempty := runs.tail_nonempty firstEmpty hasOther
  have bounded : BoundedNonempty alphabet (first :: rest) := by
    intro slot member
    have good := runs.slotGood slot member
    refine ⟨good.1, ?_⟩
    intro x letter
    apply (nonSimpleAlphabet_mem letters x).mpr
    refine ⟨?_, good.2.1 x letter⟩
    have present := rawRender_slot_mem (first :: rest) slot member x letter
    simpa only [rawShape] using present
  have nonsimple : ∀ slot ∈ first :: rest, ∀ x ∈ slot.block,
      ([] ++ rawRender (first :: rest) ++ []).count x ≠ 1 := by
    intro slot member x letter
    simpa only [nonSimple, rawShape, List.nil_append, List.append_nil] using
      (runs.slotGood slot member).2.1 x letter
  obtain ⟨output, canonical, rewriting, gaps⟩ :=
    exists_saturated_rawChain alphabet (first :: rest) [] [] bounded nonsimple
  cases output with
  | nil =>
      have impossible : first.gap :: rest.map Slot.gap = [] := by
        simpa only [List.map_cons, List.map_nil] using gaps
      cases impossible
  | cons next tail =>
      have derivation : ListDerives letters (render (next :: tail)) := by
        simpa only [List.nil_append, List.append_nil, rawShape] using rewriting
      have same := Actual.derives_sameEval derivation
      have gapShape : first.gap :: rest.map Slot.gap = next.gap :: tail.map Slot.gap := by
        simpa only [List.map_cons] using gaps
      have heads := (List.cons.inj gapShape).1
      have tails := (List.cons.inj gapShape).2
      have nextEmpty : next.gap = [] := heads.symm.trans firstEmpty
      have tailNonempty : tail ≠ [] := by
        intro empty
        have lengths := congrArg List.length tails
        rw [empty] at lengths
        simp only [List.length_map, List.length_nil] at lengths
        have restEmpty : rest = [] := by
          cases rest with
          | nil => rfl
          | cons slot slots =>
              simp only [List.length_cons] at lengths
              omega
        exact restNonempty restEmpty
      have nonemptyGaps : ∀ slot ∈ tail, slot.gap ≠ [] := by
        intro slot member
        have mapped : slot.gap ∈ tail.map Slot.gap := List.mem_map.mpr ⟨slot, member, rfl⟩
        have oldMapped : slot.gap ∈ rest.map Slot.gap := by
          rw [tails]
          exact mapped
        obtain ⟨oldSlot, oldMember, equal⟩ := List.mem_map.mp oldMapped
        intro empty
        exact (runs.2 oldSlot oldMember).2 (equal.trans empty)
      have simpleGaps : ∀ slot ∈ next :: tail, ∀ x ∈ slot.gap,
          (render (next :: tail)).count x = 1 := by
        intro slot member x letter
        have mapped : slot.gap ∈ (next :: tail).map Slot.gap := List.mem_map.mpr ⟨slot, member, rfl⟩
        have oldMapped : slot.gap ∈ (first :: rest).map Slot.gap := by
          rw [gaps]
          exact mapped
        obtain ⟨oldSlot, oldMember, equal⟩ := List.mem_map.mp oldMapped
        have oldLetter : x ∈ oldSlot.gap := by
          rw [equal]
          exact letter
        have notSelected := (runs.slotGood oldSlot oldMember).2.2 x oldLetter
        have one : letters.count x = 1 := by
          by_cases isOne : letters.count x = 1
          · exact isOne
          · exact False.elim (notSelected isOne)
        exact (same.countOne x).mp one
      have exactAlphabet : ∀ x, x ∈ alphabet ↔
          x ∈ render (next :: tail) ∧ (render (next :: tail)).count x ≠ 1 := by
        intro x
        have original := nonSimpleAlphabet_mem letters x
        constructor
        · intro member
          have old := original.mp member
          exact ⟨(same.mem x).mp old.1, fun one => old.2 ((same.countOne x).mpr one)⟩
        · intro member
          exact original.mpr ⟨(same.mem x).mpr member.1,
            fun one => member.2 ((same.countOne x).mp one)⟩
      exact ⟨render (next :: tail), derivation, alphabet, next, tail,
        nonSimpleAlphabet_ordered letters, nonSimpleAlphabet_nodup letters, exactAlphabet,
        tailNonempty, nextEmpty, nonemptyGaps, simpleGaps, canonical, rfl⟩

/-- Canonicalize both sides without assuming that their simple factors or
non-simple blocks already match. The actual C7 identity is preserved. -/
theorem canonicalize_identity (identity : Identity Nat) (valid : identity.SatisfiedBy Actual.table.semigroup)
    (leftStart : StartsN identity.lhs.toList) (leftEnd : EndsN identity.lhs.toList)
    (rightStart : StartsN identity.rhs.toList) (rightEnd : EndsN identity.rhs.toList)
    (simple : HasSimple identity.lhs.toList) :
    ∃ left right, CanonicalForm left ∧ CanonicalForm right ∧
      ListDerives identity.lhs.toList left ∧ ListDerives identity.rhs.toList right ∧ Actual.SameEval left right := by
  have original := Actual.sameEval_valid identity valid
  have rightSimple : HasSimple identity.rhs.toList := by
    obtain ⟨x, one⟩ := simple
    exact ⟨x, (original.countOne x).mp one⟩
  obtain ⟨left, leftDerivation, leftForm⟩ := lemma18_5 identity.lhs.toList leftStart leftEnd simple
  obtain ⟨right, rightDerivation, rightForm⟩ := lemma18_5 identity.rhs.toList rightStart rightEnd rightSimple
  have leftSame := (Actual.derives_sameEval leftDerivation).symm
  have rightSame := Actual.derives_sameEval rightDerivation
  exact ⟨left, right, leftForm, rightForm, leftDerivation, rightDerivation, leftSame.trans (original.trans rightSame)⟩

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalForm.hasSimple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalForm.nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalForm.explicitBlocks
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.lemma18_5
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonicalize_identity

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

import SemigroupBasis.CoRoots.Order6SporadicSection18OuterBlockEquality
import SemigroupBasis.CoRoots.Order6SporadicSection18CanonicalWord
import SemigroupBasis.CoRoots.Order6SporadicSection18ConnectedMerge
import SemigroupBasis.CoRoots.Order6SporadicSection18ConnectedEnds

/-! A canonical form with positional outer-block equality. The equality is
bound to the same chain as the canonical witness, not to a second arbitrary
decomposition. The frozen Lemma18.5 construction is strengthened by carrying
the proved pointwise block-inclusion invariant through its saturation step. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis

def ClosedCanonicalForm (letters : List Nat) : Prop :=
  ∃ (alphabet : List Nat) (first : Slot) (rest : List Slot),
    alphabet.Pairwise (· < ·) ∧ alphabet.Nodup ∧
    (∀ x, x ∈ alphabet ↔ x ∈ letters ∧ letters.count x ≠ 1) ∧
    rest ≠ [] ∧ first.gap = [] ∧ (∀ slot ∈ rest, slot.gap ≠ []) ∧
    (∀ slot ∈ first :: rest, ∀ x ∈ slot.gap, letters.count x = 1) ∧
    CanonicalChain alphabet (first :: rest) ∧ render (first :: rest) = letters ∧
    ∃ middle last, rest = middle ++ [last] ∧ first.block = last.block

theorem ClosedCanonicalForm.canonical {letters : List Nat}
    (formed : ClosedCanonicalForm letters) : CanonicalForm letters := by
  obtain ⟨alphabet, first, rest, ordered, nodup, exactAlphabet, restNonempty,
    firstEmpty, gapsNonempty, gapsSimple, canonical, shape, _⟩ := formed
  exact ⟨alphabet, first, rest, ordered, nodup, exactAlphabet, restNonempty,
    firstEmpty, gapsNonempty, gapsSimple, canonical, shape⟩

/-- The first and last square blocks literally coincide and are nonempty. -/
theorem ClosedCanonicalForm.repeatedOuter {letters : List Nat}
    (formed : ClosedCanonicalForm letters) :
    ∃ block middle, block ≠ [] ∧
      letters = squareList block ++ middle ++ squareList block := by
  obtain ⟨alphabet, first, rest, _, _, _, _, firstEmpty, _, _, canonical,
    shape, middle, last, tailShape, blockShape⟩ := formed
  refine ⟨first.block, render middle ++ last.gap,
    (canonical.1 first (List.Mem.head rest)).1, ?_⟩
  rw [← shape, tailShape]
  simp only [render, render_append, firstEmpty, List.nil_append,
    List.append_nil, blockShape, List.append_assoc]

/-- The Lemma18.5 construction retains equal outer blocks whenever the
input has matching endpoint letters. No connectedness preservation is assumed. -/
theorem lemma18_5_closed (letters : List Nat)
    (starts : StartsN letters) (ends : EndsN letters) (simple : HasSimple letters)
    (endpoint : Nat) (interior : List Nat)
    (closed : letters = endpoint :: interior ++ [endpoint]) :
    ∃ normal, ListDerives letters normal ∧ ClosedCanonicalForm normal := by
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
  obtain ⟨output, canonical, rewriting, gaps, extended⟩ :=
    exists_saturated_rawChain_withAnchors alphabet (first :: rest) [] [] bounded nonsimple
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
      have outer : ∃ middle last, tail = middle ++ [last] ∧ next.block = last.block :=
        ChainExtends.closed_outer_blocks runs firstEmpty endpoint interior
          (rawShape.trans closed) extended canonical tailNonempty
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
        tailNonempty, nextEmpty, nonemptyGaps, simpleGaps, canonical, rfl, outer⟩

theorem closedEnvelope_canonical (endpoint : Nat) (interior : List Nat)
    (simple : HasSimple (Connectedization.closedEnvelopeWord endpoint interior).toList) :
    ∃ normal,
      ListDerives (Connectedization.closedEnvelopeWord endpoint interior).toList normal ∧
        ClosedCanonicalForm normal := by
  have endpoints := Reduction.connected_nonsimpleEnds
    (Connectedization.closedEnvelopeWord endpoint interior)
    (Connectedization.closedEnvelopeWord_connected endpoint interior)
  exact lemma18_5_closed _ endpoints.1 endpoints.2 simple endpoint interior rfl

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.ClosedCanonicalForm.canonical
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.ClosedCanonicalForm.repeatedOuter
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.lemma18_5_closed
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.closedEnvelope_canonical

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

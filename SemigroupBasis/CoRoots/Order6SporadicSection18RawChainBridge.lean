import SemigroupBasis.CoRoots.Order6SporadicSection18SaturationExists
import SemigroupBasis.CoRoots.Order6SporadicSection18ActualEvaluation

/-! Lift canonical saturation from square blocks to arbitrary globally
non-simple raw blocks, retaining both external contexts and every internal gap. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis

def rawRender : List Slot → List Nat
  | [] => []
  | slot :: rest => slot.gap ++ slot.block ++ rawRender rest

theorem rawRender_slot_mem (chain : List Slot) :
    ∀ slot ∈ chain, ∀ x ∈ slot.block, x ∈ rawRender chain := by
  induction chain with
  | nil => intro slot member; cases member
  | cons head rest ih =>
      intro slot member x letter
      rcases List.mem_cons.mp member with equal | member
      · subst slot
        simp only [rawRender, List.mem_append]
        exact Or.inl (Or.inr letter)
      · have seen := ih slot member x letter
        simp only [rawRender, List.mem_append]
        exact Or.inr seen

theorem doubleChain (chain : List Slot) (before after : List Nat) :
    (∀ slot ∈ chain, ∀ x ∈ slot.block, (before ++ rawRender chain ++ after).count x ≠ 1) →
      ListDerives (before ++ rawRender chain ++ after) (before ++ render chain ++ after) := by
  induction chain generalizing before with
  | nil => intro _; exact S5_107.ListDerives.refl _
  | cons head rest ih =>
      intro nonsimple
      let nextPrefix := before ++ head.gap ++ squareList head.block
      have headNonsimple : ∀ x ∈ head.block,
          ((before ++ head.gap) ++ head.block ++ (rawRender rest ++ after)).count x ≠ 1 := by
        intro x member
        simpa only [rawRender, List.append_assoc] using nonsimple head (by simp) x member
      have first : ListDerives (before ++ rawRender (head :: rest) ++ after)
          (nextPrefix ++ rawRender rest ++ after) := by
        simpa only [rawRender, nextPrefix, List.append_assoc] using
          doubleBlock (before ++ head.gap) head.block (rawRender rest ++ after) headNonsimple
      have same := Actual.derives_sameEval first
      have tailNonsimple : ∀ slot ∈ rest, ∀ x ∈ slot.block,
          (nextPrefix ++ rawRender rest ++ after).count x ≠ 1 := by
        intro slot member x letter one
        exact (nonsimple slot (List.mem_cons_of_mem head member) x letter) ((same.countOne x).mpr one)
      have second := ih nextPrefix tailNonsimple
      simpa only [render, nextPrefix, List.append_assoc] using first.trans second

/-- Arbitrarily many raw blocks can be converted to noncrossing, equal-or-
disjoint normalized square blocks. Nonsimplicity is checked in the WHOLE word,
including both contexts, rather than separately within each selected block. -/
theorem exists_saturated_rawChain (alphabet : List Nat) (input : List Slot) (before after : List Nat)
    (bounded : BoundedNonempty alphabet input)
    (nonsimple : ∀ slot ∈ input, ∀ x ∈ slot.block, (before ++ rawRender input ++ after).count x ≠ 1) :
    ∃ output, CanonicalChain alphabet output ∧
      ListDerives (before ++ rawRender input ++ after) (before ++ render output ++ after) ∧
      input.map Slot.gap = output.map Slot.gap := by
  obtain ⟨output, canonical, derivation, gaps⟩ := exists_saturated_squareChain alphabet input bounded
  exact ⟨output, canonical, (doubleChain input before after nonsimple).trans (derivation.context before after), gaps⟩

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.rawRender_slot_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.doubleChain
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.exists_saturated_rawChain

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

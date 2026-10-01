import SemigroupBasis.CoRoots.Order6Astra.C8StarRecursion
import SemigroupBasis.CoRoots.Order6Astra.C8CutCalculus

namespace SemigroupBasis.CoRoots.Order6Astra.C8ChainComparison

open Order6SporadicSection19.Published
open C8TailCuts C8CutCalculus C8ListDerives C8BranchAlgebra

theorem perm_to_front {α : Type} (before after : List α) (value : α) :
    (before ++ value :: after).Perm (value :: (before ++ after)) := by
  induction before with
  | nil => exact List.Perm.refl _
  | cons first rest ih =>
    exact (List.Perm.cons first ih).trans (List.Perm.swap value first (rest ++ after))

/-- Pointwise derivability in both directions is enough for chains of
pairwise disjoint nonempty branches. Disjoint support makes the matching
injective, and each selected branch is moved by the actual exchange rule. -/
theorem compare_chains (separator : Word Nat) (left right : List (Word Nat))
    (leftPairwise : left.Pairwise (fun a b => Disjoint a.toList b.toList))
    (rightPairwise : right.Pairwise (fun a b => Disjoint a.toList b.toList))
    (forward : ∀ a ∈ left, ∃ b ∈ right, Derives basis a b)
    (backward : ∀ b ∈ right, ∃ a ∈ left, Derives basis b a) :
    Derives basis (chain separator left) (chain separator right) := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => exact Derives.refl _
    | cons first rest =>
      obtain ⟨a, member, _⟩ := backward first List.mem_cons_self
      cases member
  | cons first rest ih =>
    obtain ⟨selected, selectedMember, headDerived⟩ := forward first List.mem_cons_self
    obtain ⟨before, after, split⟩ := List.mem_iff_append.mp selectedMember
    have permutation : right.Perm (selected :: (before ++ after)) := by
      rw [split]
      exact perm_to_front before after selected
    have targetPairwise := permutation.pairwise rightPairwise
      (fun {_ _} h => disjoint_symm h)
    have sourceBoth := List.pairwise_cons.mp leftPairwise
    have targetBoth := List.pairwise_cons.mp targetPairwise
    have headSupport := C8ListDerives.support (of_words headDerived)
    have restForward : ∀ a ∈ rest, ∃ b ∈ before ++ after, Derives basis a b := by
      intro a member
      obtain ⟨b, inRight, derived⟩ := forward a (List.mem_cons_of_mem first member)
      have different : b ≠ selected := by
        intro equal
        have inB : a.head ∈ b.toList :=
          (C8ListDerives.support (of_words derived) a.head).mp List.mem_cons_self
        have inFirst : a.head ∈ first.toList := (headSupport a.head).mpr (by simpa only [equal] using inB)
        exact sourceBoth.1 a member a.head inFirst List.mem_cons_self
      have targetMember := permutation.mem_iff.mp inRight
      exact ⟨b, (List.mem_cons.mp targetMember).resolve_left different, derived⟩
    have restBackward : ∀ b ∈ before ++ after, ∃ a ∈ rest, Derives basis b a := by
      intro b member
      have inRight : b ∈ right := permutation.mem_iff.mpr (List.mem_cons_of_mem selected member)
      obtain ⟨a, inLeft, derived⟩ := backward b inRight
      have different : a ≠ first := by
        intro equal
        have inA : b.head ∈ a.toList :=
          (C8ListDerives.support (of_words derived) b.head).mp List.mem_cons_self
        have inSelected : b.head ∈ selected.toList := (headSupport b.head).mp (by simpa only [equal] using inA)
        exact targetBoth.1 b member b.head inSelected List.mem_cons_self
      exact ⟨a, (List.mem_cons.mp inLeft).resolve_left different, derived⟩
    have tailDerived := ih (before ++ after) sourceBoth.2 targetBoth.2 restForward restBackward
    have paired : Derives basis (chain separator (first :: rest))
        (chain separator (selected :: (before ++ after))) :=
      (Derives.appendRight (Derives.prepend separator headDerived) (chain separator rest)).trans
        (Derives.prepend (separator ++ selected) tailDerived)
    exact paired.trans (chain_perm separator permutation.symm)

end SemigroupBasis.CoRoots.Order6Astra.C8ChainComparison

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8ChainComparison.compare_chains

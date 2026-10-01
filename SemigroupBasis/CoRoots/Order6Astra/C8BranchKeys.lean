import SemigroupBasis.CoRoots.Order6Astra.C8IslandKey
import SemigroupBasis.CoRoots.Order6Astra.C8StarKeyFacts

namespace SemigroupBasis.CoRoots.Order6Astra.C8BranchKeys

open C8TailCuts C8SemanticKey C8Star C8StarFrames C8StarKeyFacts
open C8KeyCalculus C8IslandKey C8BranchAlgebra

theorem prefix_island (star : Star) (branch : Word Nat) (member : branch ∈ star.branches)
    (p : List Nat) (t : Nat) (literal : branch.toList = p ++ [t]) (fresh : t ∉ p) :
    Nonempty (Island star.word.toList p) := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  let left := (chain (star.root ++ star.root) before).toList
  let right := (chain (star.root ++ star.root) after).toList
  refine ⟨⟨left, t :: right, ?_, ?_⟩⟩
  · rw [Star.word, split, chain_split, literal]
    change (left ++ (p ++ [t])) ++ right = _
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · intro x hx contrary
    have inBranch : x ∈ branch.toList := by rw [literal]; exact List.mem_append.mpr (Or.inl hx)
    rcases List.mem_append.mp contrary with inLeft | later
    · exact frame_isolated star before after branch split x inBranch
        (List.mem_append.mpr (Or.inl inLeft))
    · rcases List.mem_cons.mp later with equal | inRight
      · subst x
        exact fresh hx
      · exact frame_isolated star before after branch split x inBranch
          (List.mem_append.mpr (Or.inr inRight))

/-- The matching branch prefixes have the FULL recursive key: support,
simplicity, ordered cuts, every marker tail, and the full-prefix flag. -/
theorem matching_prefix_key (left right : Star) (key : Key left.word.toList right.word.toList)
    (branch : Word Nat) (member : branch ∈ left.branches) (p : List Nat) (t : Nat)
    (literal : branch.toList = p ++ [t]) (fresh : t ∉ p) :
    ∃ other ∈ right.branches, ∃ q : List Nat,
      other.toList = q ++ [t] ∧ t ∉ q ∧ Key p q := by
  obtain ⟨other, otherMember, q, target, targetFresh, same, tails⟩ :=
    matching_branch left right key branch member p t literal fresh
  obtain ⟨first⟩ := prefix_island left branch member p t literal fresh
  obtain ⟨second⟩ := prefix_island right other otherMember q t target targetFresh
  exact ⟨other, otherMember, q, target, targetFresh,
    key_islands key first second same (cuts_of_tails p q same tails)⟩

end SemigroupBasis.CoRoots.Order6Astra.C8BranchKeys

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8BranchKeys.prefix_island
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8BranchKeys.matching_prefix_key

import SemigroupBasis.CoRoots.Order6Astra.C8TailCuts
import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedRootSpanIsolation

namespace SemigroupBasis.CoRoots.Order6Astra.C8BranchIsolation

open Order6SporadicSection19.Published
open MaximalFactors FactorBoundaries BlockAlignment MacroWitnesses RootFamily
open RootBlockPartition RootSpanIsolation CanonicalPresentation

/-- A gap between consecutive copies of one root square has no letter shared
with either exterior context. G2 excludes other roots crossing the boundary;
exact nonsimple coverage excludes repeated outside letters. -/
theorem gap_isolated (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (family : Family roots word)
    (terminal : Terminal roots word) (partition : SquarePartition roots word pieces)
    (coverage : ∀ x, Covered roots x ↔ 2 ≤ word.toList.count x)
    (root : Word Nat) (member : root ∈ roots) (before inside after : List (Word Nat))
    (split : pieces = before ++ ((root ++ root) :: (inside ++ (root ++ root) :: after)))
    (consecutive : (root ++ root) ∉ inside) :
    C8TailCuts.Disjoint (flatten inside)
      (flatten ((before ++ [root ++ root]) ++ ((root ++ root) :: after))) := by
  have arranged : pieces = (before ++ [root ++ root]) ++
      (inside ++ (root ++ root) :: after) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using split
  apply separated_squares_separate_letters roots word pieces family partition coverage
    (before ++ [root ++ root]) inside ((root ++ root) :: after) arranged
  intro other otherMember inner outer
  have different : root ≠ other := by
    intro equal
    subst other
    exact consecutive inner
  have absent := terminal_inner_root_absent roots word pieces terminal partition
    root other member otherMember different before inside after split inner
  have squareNe : other ++ other ≠ root ++ root := by
    intro equal
    exact consecutive (equal ▸ inner)
  rcases List.mem_append.mp outer with earlier | later
  · rcases List.mem_append.mp earlier with inBefore | atRoot
    · exact absent.1 inBefore
    · exact squareNe (List.mem_singleton.mp atRoot)
  · rcases List.mem_cons.mp later with atRoot | inAfter
    · exact squareNe atRoot
    · exact absent.2 inAfter

/-- The last actual factor of a nonempty consecutive-root gap is outside
the root family. A root square there would give the forbidden G1 adjacency. -/
theorem gap_last_outside (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (terminal : Terminal roots word)
    (partition : SquarePartition roots word pieces) (root : Word Nat)
    (member : root ∈ roots) (before initial after : List (Word Nat)) (last : Word Nat)
    (split : pieces = before ++ ((root ++ root) ::
      (initial ++ last :: (root ++ root) :: after)))
    (consecutive : (root ++ root) ∉ initial ++ [last]) : Outside roots last := by
  have lastMember : last ∈ pieces := by
    rw [split]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr
      (List.mem_append.mpr (Or.inr List.mem_cons_self)))))
  rcases partition.2 last lastMember with square | outside
  · obtain ⟨other, otherMember, equal⟩ := square
    have different : root ≠ other := by
      intro e
      subst other
      exact consecutive (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr equal.symm)))
    have related : GeneralizedRelated root other word := by
      apply Or.inl
      refine ⟨flatten before, flatten initial, flatten after, ?_⟩
      rw [← partition.1, split, equal]
      simp only [flatten, FactorBoundaries.flatten_append, List.append_assoc]
    exact False.elim ((terminal_members roots word terminal root other member otherMember
      different) related)
  · exact outside

/-- The nonempty gap has an actual final simple letter, not merely a chosen
element of its support. This supplies the recursive normal form's marker. -/
theorem gap_terminal_marker (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (terminal : Terminal roots word)
    (partition : SquarePartition roots word pieces)
    (coverage : ∀ x, Covered roots x ↔ 2 ≤ word.toList.count x)
    (root : Word Nat) (member : root ∈ roots) (before inside after : List (Word Nat))
    (split : pieces = before ++ ((root ++ root) :: (inside ++ (root ++ root) :: after)))
    (consecutive : (root ++ root) ∉ inside) (nonempty : inside ≠ []) :
    ∃ leading : List Nat, ∃ marker : Nat,
      flatten inside = leading ++ [marker] ∧ word.toList.count marker = 1 := by
  rcases nil_or_last inside with empty | ⟨initial, last, tail⟩
  · exact False.elim (nonempty empty)
  have literal : pieces = before ++ ((root ++ root) ::
      (initial ++ last :: (root ++ root) :: after)) := by
    simpa only [tail, List.append_assoc, List.cons_append, List.nil_append] using split
  have outside := gap_last_outside roots word pieces terminal partition root member
    before initial after last literal (by simpa only [tail] using consecutive)
  have lastMember : last ∈ pieces := by
    rw [literal]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr
      (List.mem_append.mpr (Or.inr List.mem_cons_self)))))
  have simple := outside_part_simple roots word pieces partition coverage last lastMember outside
  rcases nil_or_last last.toList with empty | ⟨start, marker, lastSplit⟩
  · exact False.elim (piece_nonempty last empty)
  · refine ⟨flatten initial ++ start, marker, ?_, ?_⟩
    · rw [tail, FactorBoundaries.flatten_append]
      simp only [flatten, List.append_nil, lastSplit, List.append_assoc]
    · apply simple marker
      rw [lastSplit]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))

end SemigroupBasis.CoRoots.Order6Astra.C8BranchIsolation

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8BranchIsolation.gap_isolated
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8BranchIsolation.gap_last_outside
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8BranchIsolation.gap_terminal_marker

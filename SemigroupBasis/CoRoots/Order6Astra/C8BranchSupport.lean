import SemigroupBasis.CoRoots.Order6Astra.C8RawChain

namespace SemigroupBasis.CoRoots.Order6Astra.C8BranchSupport

open Order6SporadicSection19.Published
open MaximalFactors FactorBoundaries C8BranchPieces C8CanonicalBranches C8RawChain
open C8TailCuts

theorem member_before (square : Word Nat) (gaps : List (List (Word Nat)))
    (gap : List (Word Nat)) (member : gap ∈ gaps) (x : Nat) (inside : x ∈ flatten gap) :
    x ∈ flatten (beforePieces square gaps) := by
  induction gaps with
  | nil => cases member
  | cons first rest ih =>
    simp only [beforePieces, flatten, FactorBoundaries.flatten_append, List.mem_append]
    rcases List.mem_cons.mp member with equal | later
    · subst gap
      exact Or.inr (Or.inl inside)
    · exact Or.inr (Or.inr (ih later))

theorem member_after (square : Word Nat) (gaps : List (List (Word Nat)))
    (gap : List (Word Nat)) (member : gap ∈ gaps) (x : Nat) (inside : x ∈ flatten gap) :
    x ∈ flatten (afterPieces square gaps) := by
  induction gaps with
  | nil => cases member
  | cons first rest ih =>
    simp only [afterPieces, FactorBoundaries.flatten_append, flatten, List.mem_append]
    rcases List.mem_cons.mp member with equal | later
    · subst gap
      exact Or.inl inside
    · exact Or.inr (Or.inr (ih later))

theorem pairwise_of_cuts {α : Type} (relation : α → α → Prop) (xs : List α)
    (allCuts : ∀ before x after, xs = before ++ x :: after →
      ∀ y ∈ before ++ after, relation x y) : xs.Pairwise relation := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons first rest ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih ?_⟩
    · intro y member
      exact allCuts [] first rest rfl y member
    · intro before x after split y member
      have whole : first :: rest = (first :: before) ++ x :: after :=
        congrArg (List.cons first) split
      exact allCuts (first :: before) x after whole y (List.mem_cons_of_mem first member)

/-- The actual gaps are pairwise support-disjoint, including empty gaps. -/
theorem gaps_pairwise (word : Word Nat) (d : Decomposition word) :
    d.gaps.Pairwise (fun left right => Disjoint (flatten left) (flatten right)) := by
  apply pairwise_of_cuts
  intro before gap after split other member x inside contrary
  have isolated := d.isolated before gap after split
  apply isolated x inside
  rw [FactorBoundaries.flatten_append, FactorBoundaries.flatten_append]
  rcases List.mem_append.mp member with earlier | later
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl (member_before (d.root ++ d.root) before other earlier x contrary))))
  · apply List.mem_append.mpr
    apply Or.inr
    change x ∈ (d.root ++ d.root).toList ++ flatten (afterPieces (d.root ++ d.root) after)
    exact List.mem_append.mpr (Or.inr
      (member_after (d.root ++ d.root) after other later x contrary))

theorem pack_pairwise (gaps : List (List Nat)) (disjoint : gaps.Pairwise Disjoint) :
    (pack gaps).Pairwise (fun left right => Disjoint left.toList right.toList) := by
  induction gaps with
  | nil => exact List.Pairwise.nil
  | cons gap rest ih =>
    have both := List.pairwise_cons.mp disjoint
    cases gap with
    | nil => exact ih both.2
    | cons x xs =>
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih both.2⟩
      intro word member
      exact both.1 word.toList ((mem_pack rest word).mp member)

theorem branches_pairwise (word : Word Nat) (d : Decomposition word) :
    (pack (d.gaps.map flatten)).Pairwise
      (fun left right => Disjoint left.toList right.toList) := by
  apply pack_pairwise
  simpa only [List.pairwise_map] using gaps_pairwise word d

theorem branch_support (word : Word Nat) (d : Decomposition word) (branch : Word Nat)
    (member : branch ∈ pack (d.gaps.map flatten)) :
    ∀ x ∈ branch.toList, x ∈ word.toList := by
  have present := (mem_pack (d.gaps.map flatten) branch).mp member
  obtain ⟨gap, gapMember, equal⟩ := List.mem_map.mp present
  intro x inside
  rw [d.literal]
  apply List.mem_append.mpr
  apply Or.inr
  exact member_after (d.root ++ d.root) d.gaps gap gapMember x (by simpa only [equal] using inside)

/-- Removing one outer-root letter gives a strictly smaller ambient alphabet
for every recursive branch. No post-normalization word-length bound is used. -/
theorem branch_erase_alphabet (word : Word Nat) (d : Decomposition word)
    (alphabet : List Nat) (covered : ∀ x ∈ word.toList, x ∈ alphabet)
    (branch : Word Nat) (member : branch ∈ pack (d.gaps.map flatten)) :
    ∀ x ∈ branch.toList, x ∈ alphabet.erase d.root.head := by
  intro x inside
  have apart := (packed_branch word d branch member).1
  have different : x ≠ d.root.head := by
    intro equal
    subst x
    exact apart d.root.head inside List.mem_cons_self
  exact (List.mem_erase_of_ne different).mpr
    (covered x (branch_support word d branch member x inside))

theorem root_head_present (word : Word Nat) (d : Decomposition word) :
    d.root.head ∈ word.toList := by
  rw [d.literal, Word.toList_append]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl List.mem_cons_self)))

end SemigroupBasis.CoRoots.Order6Astra.C8BranchSupport

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8BranchSupport.gaps_pairwise
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8BranchSupport.branches_pairwise
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8BranchSupport.branch_erase_alphabet

import SemigroupBasis.CoRoots.Order6Astra.C8BranchPieces

namespace SemigroupBasis.CoRoots.Order6Astra.C8CanonicalBranches

open Order6SporadicSection19.Published
open MaximalFactors FactorBoundaries BlockAlignment RootFamily RootBlockPartition
open CanonicalPresentation RootSpanIsolation C8BranchPieces C8BranchIsolation ConnectedTerminalEndpoints

/-- A semantic-free recursive decomposition interface. Gaps are actual lists
of nonempty factors, and every nonempty gap has an actual final simple marker.
The isolation field retains each gap's exact exterior contexts. -/
structure Decomposition (word : Word Nat) where
  root : Word Nat
  shape : RootShape root
  gaps : List (List (Word Nat))
  literal : word.toList = (root ++ root).toList ++ flatten (afterPieces (root ++ root) gaps)
  root_apart : ∀ gap ∈ gaps, C8TailCuts.Disjoint (flatten gap) root.toList
  markers : ∀ gap ∈ gaps, gap ≠ [] → ∃ leading : List Nat, ∃ marker : Nat,
    flatten gap = leading ++ [marker] ∧ word.toList.count marker = 1
  isolated : ∀ before gap after, gaps = before ++ gap :: after →
    C8TailCuts.Disjoint (flatten gap)
      (flatten ((beforePieces (root ++ root) before ++ [root ++ root]) ++
        ((root ++ root) :: afterPieces (root ++ root) after)))

theorem of_form (word : Word Nat) (form : Form word) : Nonempty (Decomposition word) := by
  obtain ⟨gaps, cut, absent, literal⟩ := form_gaps word form
  obtain ⟨root, rootMember, square⟩ := form.first_square
  let pieces := form.first :: expand form.chunks
  have partition : SquarePartition form.roots word pieces := form_partition word form
  have piecesCut : pieces = (root ++ root) :: afterPieces (root ++ root) gaps := by
    dsimp [pieces]
    rw [cut, square]
  have isolated : ∀ before gap after, gaps = before ++ gap :: after →
      C8TailCuts.Disjoint (flatten gap)
        (flatten ((beforePieces (root ++ root) before ++ [root ++ root]) ++
          ((root ++ root) :: afterPieces (root ++ root) after))) := by
    intro before gap after split
    have inside : gap ∈ gaps := by
      rw [split]
      exact List.mem_append.mpr (Or.inr List.mem_cons_self)
    have gapAbsent : root ++ root ∉ gap := by simpa only [square] using absent gap inside
    have actual : pieces = beforePieces (root ++ root) before ++
        ((root ++ root) :: (gap ++ (root ++ root) :: afterPieces (root ++ root) after)) := by
      rw [piecesCut, split]
      exact gap_context (root ++ root) before after gap
    exact gap_isolated form.roots word pieces form.family form.terminal partition
      form.coverage root rootMember (beforePieces (root ++ root) before) gap
      (afterPieces (root ++ root) after) actual gapAbsent
  refine ⟨⟨root, (form.family.2 root rootMember).1, gaps, ?_, ?_, ?_, isolated⟩⟩
  · simpa only [square] using literal
  · intro gap member x hx inRoot
    obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
    have iso := isolated before gap after split
    apply iso x hx
    rw [FactorBoundaries.flatten_append]
    apply List.mem_append.mpr
    apply Or.inr
    change x ∈ (root ++ root).toList ++ flatten (afterPieces (root ++ root) after)
    apply List.mem_append.mpr
    apply Or.inl
    rw [Word.toList_append]
    exact List.mem_append.mpr (Or.inl inRoot)
  · intro gap member nonempty
    obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
    have actual : pieces = beforePieces (root ++ root) before ++
        ((root ++ root) :: (gap ++ (root ++ root) :: afterPieces (root ++ root) after)) := by
      rw [piecesCut, split]
      exact gap_context (root ++ root) before after gap
    exact gap_terminal_marker form.roots word pieces form.terminal partition form.coverage
      root rootMember (beforePieces (root ++ root) before) gap
      (afterPieces (root ++ root) after) actual
      (by simpa only [square] using absent gap member) nonempty

/-- An actual unrestricted derivation supplies the recursive decomposition.
No reification, coverage or reach/completeness premise is provided by callers. -/
theorem normalize_connected (word : Word Nat) (connected : Connected word) :
    ∃ normal : Word Nat, Derives basis word normal ∧ Nonempty (Decomposition normal) := by
  obtain ⟨normal, derived, ⟨form⟩, _⟩ := normalize_connected_canonical word connected
  exact ⟨normal, derived, of_form normal form⟩

end SemigroupBasis.CoRoots.Order6Astra.C8CanonicalBranches

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8CanonicalBranches.of_form
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8CanonicalBranches.normalize_connected

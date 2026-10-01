import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedTerminalRepeatBoundary

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedTerminalEndpoints

open MaximalFactors FactorBoundaries BlockAlignment MacroWitnesses RootFamily
open RootBlockPartition SimpleFactorInvariant TerminalRepeatBoundary

/-- The published non-singleton, no-disjoint-nonempty-cut definition. This is
the same word interface as Examples.LeeL.SourceWords.Connected, with Apart
in place of its definitionally identical Disjoint. No heavy Lee-L dependency
is imported merely for a duplicate proposition. -/
def Connected (word : Word Nat) : Prop :=
  2 ≤ word.toList.length ∧
    ¬ ∃ left right : Word Nat, word = left ++ right ∧ Apart left right

theorem connected_cut_overlap (word : Word Nat) (connected : Connected word)
    (left right : List Nat) (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (split : word.toList = left ++ right) :
    ∃ value : Nat, value ∈ left ∧ value ∈ right := by
  classical
  apply Classical.byContradiction
  intro absent
  have apart : ∀ value ∈ left, value ∉ right := by
    intro value inLeft inRight
    exact absent ⟨value, inLeft, inRight⟩
  cases left with
  | nil => exact leftNonempty rfl
  | cons first rest =>
    cases right with
    | nil => exact rightNonempty rfl
    | cons last tail =>
      apply connected.2
      refine ⟨⟨first, rest⟩, ⟨last, tail⟩, ?_, apart⟩
      apply Word.toList_injective
      simpa only [Word.toList_append, Word.toList] using split

theorem connected_head_repeated (word : Word Nat) (connected : Connected word) :
    2 ≤ word.toList.count word.head := by
  cases word with
  | mk first rest =>
    have nonempty : rest ≠ [] := by
      intro empty
      have size := connected.1
      simp only [Word.toList, empty, List.length_cons, List.length_nil] at size
      omega
    obtain ⟨value, singleton, later⟩ :=
      connected_cut_overlap ⟨first, rest⟩ connected [first] rest
        (List.cons_ne_nil first []) nonempty rfl
    have equal : value = first := List.mem_singleton.mp singleton
    subst value
    have positive : 0 < rest.count first := List.count_pos_iff.mpr later
    change 2 ≤ (first :: rest).count first
    simp only [List.count_cons_self]
    omega

theorem flatten_nonempty (pieces : List (Word Nat)) (nonempty : pieces ≠ []) :
    flatten pieces ≠ [] := by
  cases pieces with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
    cases first with
    | mk value tail =>
      change value :: (tail ++ flatten rest) ≠ []
      exact List.cons_ne_nil value (tail ++ flatten rest)

theorem common_root_letter_eq (roots : List (Word Nat)) (word left right : Word Nat)
    (family : Family roots word) (leftMember : left ∈ roots) (rightMember : right ∈ roots)
    (value : Nat) (inLeft : value ∈ left.toList) (inRight : value ∈ right.toList) :
    left = right := by
  classical
  apply Classical.byContradiction
  intro different
  obtain ⟨rest, permutation⟩ :=
    select_member_pair roots left right leftMember rightMember different
  have reordered : Family (left :: right :: rest) word :=
    family_perm roots (left :: right :: rest) word permutation family
  have apart : Apart left right :=
    (List.pairwise_cons.mp reordered.1).1 right (List.mem_cons.mpr (Or.inl rfl))
  exact apart value inLeft inRight

theorem covered_letter_piece (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (family : Family roots word)
    (partition : SquarePartition roots word pieces)
    (root : Word Nat) (rootMember : root ∈ roots)
    (value : Nat) (inRoot : value ∈ root.toList)
    (part : Word Nat) (partMember : part ∈ pieces) (inPart : value ∈ part.toList) :
    part = root ++ root := by
  rcases partition.2 part partMember with square | outside
  · obtain ⟨other, otherMember, equal⟩ := square
    have inOther : value ∈ other.toList := by
      simpa only [equal, Word.toList_append, List.mem_append, or_self] using inPart
    have rootsEqual : other = root :=
      common_root_letter_eq roots word other root family otherMember rootMember value inOther inRoot
    simpa only [rootsEqual] using equal
  · exact False.elim (outside value inPart ⟨root, rootMember, inRoot⟩)

/-- Every proper cut of the actual partition has the SAME root square on
both sides. The bridge is obtained from connectedness, not postulated. -/
theorem connected_partition_cut_root (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (connected : Connected word) (family : Family roots word)
    (partition : SquarePartition roots word pieces)
    (coverage : ∀ value, Covered roots value ↔ 2 ≤ word.toList.count value)
    (left right : List (Word Nat)) (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (split : pieces = left ++ right) :
    ∃ root ∈ roots, (root ++ root) ∈ left ∧ (root ++ root) ∈ right := by
  have literal : word.toList = flatten left ++ flatten right := by
    rw [← partition.1, split, FactorBoundaries.flatten_append]
  obtain ⟨value, inLeft, inRight⟩ := connected_cut_overlap word connected
    (flatten left) (flatten right) (flatten_nonempty left leftNonempty)
    (flatten_nonempty right rightNonempty) literal
  have leftCount : 0 < (flatten left).count value := List.count_pos_iff.mpr inLeft
  have rightCount : 0 < (flatten right).count value := List.count_pos_iff.mpr inRight
  have repeated : 2 ≤ word.toList.count value := by
    rw [literal, List.count_append]
    omega
  obtain ⟨root, rootMember, inRoot⟩ := (coverage value).mpr repeated
  obtain ⟨first, firstMember, inFirst⟩ := (mem_flatten value left).mp inLeft
  obtain ⟨last, lastMember, inLast⟩ := (mem_flatten value right).mp inRight
  have firstAll : first ∈ pieces := by
    rw [split]
    exact List.mem_append.mpr (Or.inl firstMember)
  have lastAll : last ∈ pieces := by
    rw [split]
    exact List.mem_append.mpr (Or.inr lastMember)
  have firstEqual := covered_letter_piece roots word pieces family partition
    root rootMember value inRoot first firstAll inFirst
  have lastEqual := covered_letter_piece roots word pieces family partition
    root rootMember value inRoot last lastAll inLast
  refine ⟨root, rootMember, ?_, ?_⟩
  · rw [← firstEqual]
    exact firstMember
  · rw [← lastEqual]
    exact lastMember

theorem connected_first_root (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (connected : Connected word) (family : Family roots word)
    (partition : SquarePartition roots word pieces)
    (coverage : ∀ value, Covered roots value ↔ 2 ≤ word.toList.count value)
    (first : Word Nat) (rest : List (Word Nat)) (split : pieces = first :: rest) :
    ∃ root ∈ roots, first = root ++ root := by
  have literal : word.toList = first.toList ++ flatten rest := by
    rw [← partition.1, split]
    rfl
  have headEqual : word.head = first.head := by
    change word.head :: word.tail = first.head :: (first.tail ++ flatten rest) at literal
    exact (List.cons.inj literal).1
  have repeated : 2 ≤ word.toList.count first.head := by
    rw [← headEqual]
    exact connected_head_repeated word connected
  obtain ⟨root, rootMember, inRoot⟩ := (coverage first.head).mpr repeated
  have firstMember : first ∈ pieces := by
    rw [split]
    exact List.mem_cons.mpr (Or.inl rfl)
  exact ⟨root, rootMember, covered_letter_piece roots word pieces family partition
    root rootMember first.head inRoot first firstMember (word_head_member first)⟩

/-- Last occurrence with an explicit absent suffix, preserving actual order. -/
theorem split_last_member (part : Word Nat) (pieces : List (Word Nat))
    (member : part ∈ pieces) :
    ∃ before after : List (Word Nat), pieces = before ++ part :: after ∧ part ∉ after := by
  classical
  induction pieces with
  | nil => cases member
  | cons first rest ih =>
    by_cases later : part ∈ rest
    · obtain ⟨before, after, split, absent⟩ := ih later
      refine ⟨first :: before, after, ?_, absent⟩
      simp only [List.cons_append, split]
    · have equal : part = first := (List.mem_cons.mp member).resolve_right later
      subst first
      exact ⟨[], rest, rfl, later⟩

/-- A distinct endpoint would give a literal G2 witness across the last
initial-root occurrence. Neither a substring gap nor a simple factor is
discarded in constructing that witness. -/
theorem terminal_initial_root_is_final (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (connected : Connected word) (family : Family roots word)
    (terminal : Terminal roots word) (partition : SquarePartition roots word pieces)
    (coverage : ∀ value, Covered roots value ↔ 2 ≤ word.toList.count value)
    (root : Word Nat) (rootMember : root ∈ roots)
    (tail : List (Word Nat)) (firstSplit : pieces = (root ++ root) :: tail) :
    ∃ initial : List (Word Nat), pieces = initial ++ [root ++ root] := by
  classical
  have member : (root ++ root) ∈ pieces := by
    rw [firstSplit]
    exact List.mem_cons.mpr (Or.inl rfl)
  obtain ⟨before, after, lastSplit, absent⟩ := split_last_member (root ++ root) pieces member
  have afterEmpty : after = [] := by
    apply Classical.byContradiction
    intro nonempty
    have leftNonempty : before ++ [root ++ root] ≠ [] := by
      intro empty
      have size := congrArg List.length empty
      simp only [List.length_append, List.length_cons, List.length_nil] at size
      omega
    have cut : pieces = (before ++ [root ++ root]) ++ after := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using lastSplit
    obtain ⟨other, otherMember, inLeft, inAfter⟩ :=
      connected_partition_cut_root roots word pieces connected family partition coverage
        (before ++ [root ++ root]) after leftNonempty nonempty cut
    have squaresDifferent : (other ++ other) ≠ root ++ root := by
      intro equal
      exact absent (equal ▸ inAfter)
    have different : root ≠ other := by
      intro equal
      exact squaresDifferent (by rw [equal])
    have inBefore : (other ++ other) ∈ before := by
      rcases List.mem_append.mp inLeft with earlier | last
      · exact earlier
      · exact False.elim (squaresDifferent (List.mem_singleton.mp last))
    cases before with
    | nil => cases inBefore
    | cons first middle =>
      have firstEqual : first = root ++ root := by
        have both : (root ++ root) :: tail = first :: (middle ++ (root ++ root) :: after) := by
          simpa only [List.cons_append] using firstSplit.symm.trans lastSplit
        exact (List.cons.inj both).1.symm
      subst first
      have inMiddle : (other ++ other) ∈ middle :=
        (List.mem_cons.mp inBefore).resolve_left squaresDifferent
      obtain ⟨gap1, gap2, middleSplit⟩ := split_member (other ++ other) middle inMiddle
      obtain ⟨gap3, suffix, afterSplit⟩ := split_member (other ++ other) after inAfter
      have crossing : G2 (root ++ root) (other ++ other) word.toList := by
        refine ⟨[], flatten gap1, flatten gap2, flatten gap3, flatten suffix, ?_⟩
        rw [← partition.1, lastSplit, middleSplit, afterSplit]
        simp only [flatten, FactorBoundaries.flatten_append, List.append_assoc, List.nil_append]
      have related : GeneralizedRelated root other word :=
        Or.inr (Or.inr (Or.inl crossing))
      exact (terminal_members roots word terminal root other rootMember otherMember different) related
  refine ⟨before, ?_⟩
  simpa only [afterEmpty] using lastSplit

/-- Condition V for ANY connected terminal actual root-square partition.
This does not assert that the existing normalizer preserves connectedness. -/
theorem connected_terminal_endpoints (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (connected : Connected word) (family : Family roots word)
    (terminal : Terminal roots word) (partition : SquarePartition roots word pieces)
    (coverage : ∀ value, Covered roots value ↔ 2 ≤ word.toList.count value) :
    ∃ root ∈ roots, ∃ tail initial : List (Word Nat),
      pieces = (root ++ root) :: tail ∧ pieces = initial ++ [root ++ root] := by
  have nonempty := partition_nonempty roots word pieces partition
  cases pieces with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
    obtain ⟨root, rootMember, equal⟩ :=
      connected_first_root roots word (first :: rest) connected family partition coverage first rest rfl
    have firstSplit : first :: rest = (root ++ root) :: rest := by rw [equal]
    obtain ⟨initial, lastSplit⟩ := terminal_initial_root_is_final roots word (first :: rest)
      connected family terminal partition coverage root rootMember rest firstSplit
    exact ⟨root, rootMember, rest, initial, firstSplit, lastSplit⟩

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedTerminalEndpoints

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedTerminalEndpoints.connected_cut_overlap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedTerminalEndpoints.connected_head_repeated
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedTerminalEndpoints.common_root_letter_eq
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedTerminalEndpoints.covered_letter_piece
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedTerminalEndpoints.connected_partition_cut_root
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedTerminalEndpoints.connected_first_root
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedTerminalEndpoints.split_last_member
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedTerminalEndpoints.terminal_initial_root_is_final
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedTerminalEndpoints.connected_terminal_endpoints

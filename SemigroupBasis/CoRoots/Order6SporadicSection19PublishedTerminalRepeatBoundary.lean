import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedMaximalSimpleAlignment

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TerminalRepeatBoundary

open MaximalFactors FactorBoundaries BlockAlignment OccurrenceMacro MacroWitnesses
open RootFamily RootBlockPartition SimpleFactorInvariant MaximalSimpleAlignment

/-- An actual positive literal fragment lies in an actual maximal root run.
The existing occurrence-location theorem supplies that containment. -/
theorem perfect_positive_fragment_bound (root word fragment : Word Nat)
    (perfect : CanonicalPerfect root word) (before after : List Nat)
    (split : word.toList = before ++ (fragment.toList ++ after))
    (positive : ∀ value ∈ fragment.toList, supportTag root value = true) :
    fragment.toList.length ≤ (root ++ root).toList.length := by
  have headPositive : supportTag root fragment.head = true :=
    positive fragment.head (word_head_member fragment)
  have uniform : Constant (supportTag root) fragment := by
    intro value member
    exact (positive value member).trans headPositive.symm
  obtain ⟨earlier, later, run, insideBefore, insideAfter,
    parts, inside, _, _, sameTag⟩ :=
    located_occurrence (supportTag root) fragment before after uniform
  have member : run ∈ decompose (supportTag root) word.toList := by
    rw [split, parts]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have runPositive : supportTag root run.head = true := sameTag.trans headPositive
  have runEqual : run = root ++ root := perfect.2 run member runPositive
  have sizeBound : fragment.toList.length ≤ run.toList.length := by
    rw [inside]
    simp only [List.length_append]
    omega
  rw [runEqual] at sizeBound
  exact sizeBound

/-- Perfection forbids two adjacent copies of the same root square, even
without any distinct-root terminality assumption. -/
theorem perfect_no_adjacent_squares (root word : Word Nat)
    (perfect : CanonicalPerfect root word) (before after : List Nat)
    (split : word.toList = before ++
      ((root ++ root).toList ++ ((root ++ root).toList ++ after))) : False := by
  let square : Word Nat := root ++ root
  let four : Word Nat := square ++ square
  have literal : word.toList = before ++ (four.toList ++ after) := by
    simpa only [four, square, Word.toList_append, List.append_assoc] using split
  have positive : ∀ value ∈ four.toList, supportTag root value = true := by
    intro value member
    have rootMember : value ∈ root.toList := by
      simpa only [four, square, Word.toList_append, List.mem_append, or_self] using member
    exact (supportTag_true root value).mpr rootMember
  have sizeBound := perfect_positive_fragment_bound root word four perfect before after literal positive
  have rootPositive : 0 < root.toList.length := by
    cases root with
    | mk first rest => exact Nat.zero_lt_succ rest.length
  simp only [four, square, Word.toList_append, List.length_append] at sizeBound
  omega

/-- An earlier occurrence is explicit. Nothing is required of the first
occurrence of a root square. The predecessor is an actual nonempty word. -/
def RepeatBoundary (roots : List (Word Nat)) (pieces : List (Word Nat)) : Prop :=
  ∀ root ∈ roots, ∀ (before : List (Word Nat)) (previous : Word Nat) (after : List (Word Nat)),
    pieces = before ++ (previous :: (root ++ root) :: after) →
    (root ++ root) ∈ before ++ [previous] → Outside roots previous

theorem terminal_repeat_predecessor (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (family : Family roots word) (terminal : Terminal roots word)
    (partition : SquarePartition roots word pieces) (root : Word Nat) (rootMember : root ∈ roots)
    (before : List (Word Nat)) (previous : Word Nat) (after : List (Word Nat))
    (split : pieces = before ++ (previous :: (root ++ root) :: after))
    (repeated : (root ++ root) ∈ before ++ [previous]) : Outside roots previous := by
  have literal : word.toList = flatten before ++
      (previous.toList ++ ((root ++ root).toList ++ flatten after)) := by
    rw [← partition.1, split, flatten_append]
    rfl
  have adjacentImpossible : previous = root ++ root → False := by
    intro equal
    exact perfect_no_adjacent_squares root word (family.2 root rootMember).2
      (flatten before) (flatten after) (by simpa only [equal] using literal)
  have earlier : (root ++ root) ∈ before := by
    rcases List.mem_append.mp repeated with inside | last
    · exact inside
    · have equal : root ++ root = previous := List.mem_singleton.mp last
      exact False.elim (adjacentImpossible equal.symm)
  have previousMember : previous ∈ pieces := by
    rw [split]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  rcases partition.2 previous previousMember with square | outside
  · obtain ⟨other, otherMember, previousEqual⟩ := square
    by_cases same : other = root
    · subst other
      exact False.elim (adjacentImpossible previousEqual)
    · obtain ⟨earlierParts, middle, beforeSplit⟩ := split_member (root ++ root) before earlier
      have related : GeneralizedRelated root other word := by
        left
        refine ⟨flatten earlierParts, flatten middle, flatten after, ?_⟩
        rw [literal, beforeSplit, flatten_append]
        simp only [flatten, previousEqual, List.append_assoc]
      exact False.elim
        ((terminal_members roots word terminal root other rootMember otherMember (Ne.symm same)) related)
  · exact outside

theorem terminal_repeat_boundary (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (family : Family roots word) (terminal : Terminal roots word)
    (partition : SquarePartition roots word pieces) : RepeatBoundary roots pieces := by
  intro root member before previous after split repeated
  exact terminal_repeat_predecessor roots word pieces family terminal partition
    root member before previous after split repeated

/-- With the actual nonsimple coverage, the preceding factor is explicitly
nonempty and every one of its letters occurs once in the whole word. -/
theorem terminal_repeat_predecessor_simple (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (family : Family roots word) (terminal : Terminal roots word)
    (partition : SquarePartition roots word pieces)
    (coverage : ∀ value, Covered roots value ↔ 2 ≤ word.toList.count value)
    (root : Word Nat) (rootMember : root ∈ roots)
    (before : List (Word Nat)) (previous : Word Nat) (after : List (Word Nat))
    (split : pieces = before ++ (previous :: (root ++ root) :: after))
    (repeated : (root ++ root) ∈ before ++ [previous]) :
    previous.toList ≠ [] ∧ ∀ value ∈ previous.toList, word.toList.count value = 1 := by
  have member : previous ∈ pieces := by
    rw [split]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have outside : Outside roots previous :=
    terminal_repeat_predecessor roots word pieces family terminal partition
      root rootMember before previous after split repeated
  exact ⟨piece_nonempty previous,
    outside_part_simple roots word pieces partition coverage previous member outside⟩

/-- The actual arbitrary-word normalization now also has the repeated-root
boundary, while retaining literal maximal simple-factor alignment. -/
theorem normalize_with_repeat_boundary (word : Word Nat) :
    ∃ normal : Word Nat, ∃ roots : List (Word Nat), ∃ pieces : List (Word Nat),
      Derives basis word normal ∧ Family roots normal ∧ Terminal roots normal ∧
      (∀ value, Covered roots value ↔ 2 ≤ word.toList.count value) ∧
      (∀ value, Covered roots value ↔ 2 ≤ normal.toList.count value) ∧
      SquarePartition roots normal pieces ∧
      NegativeParts (repeatedTag normal) pieces = simpleFactors normal ∧
      NegativeParts (repeatedTag normal) pieces = simpleFactors word ∧
      (∀ part ∈ pieces, (∃ root ∈ roots, part = root ++ root) ∨
        (∀ value ∈ part.toList,
          word.toList.count value = 1 ∧ normal.toList.count value = 1)) ∧
      RepeatBoundary roots pieces := by
  obtain ⟨normal, roots, pieces, derived, family, terminal, original, current,
    partition, alignedNormal, alignedOriginal, kinds⟩ := normalize_with_maximal_simple_factors word
  exact ⟨normal, roots, pieces, derived, family, terminal, original, current,
    partition, alignedNormal, alignedOriginal, kinds,
    terminal_repeat_boundary roots normal pieces family terminal partition⟩

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TerminalRepeatBoundary

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TerminalRepeatBoundary.perfect_positive_fragment_bound
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TerminalRepeatBoundary.perfect_no_adjacent_squares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TerminalRepeatBoundary.terminal_repeat_predecessor
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TerminalRepeatBoundary.terminal_repeat_boundary
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TerminalRepeatBoundary.terminal_repeat_predecessor_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TerminalRepeatBoundary.normalize_with_repeat_boundary

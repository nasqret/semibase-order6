import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedRootBlockPartition

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSimpleAlignment

open MaximalFactors FactorBoundaries BlockAlignment FactorCodec RootFamily
open RootBlockPartition SimpleFactorInvariant

def NegativeParts (classify : Nat → Bool) (pieces : List (Word Nat)) : List (Word Nat) :=
  pieces.filterMap (taggedToken classify)

def MatchesRoots (classify : Nat → Bool) (roots : List (Word Nat)) : Prop :=
  ∀ value, classify value = true ↔ Covered roots value

theorem negative_parts_append (classify : Nat → Bool) (first last : List (Word Nat)) :
    NegativeParts classify (first ++ last) =
      NegativeParts classify first ++ NegativeParts classify last :=
  List.filterMap_append

theorem negative_parts_positive_cons (classify : Nat → Bool) (first : Word Nat)
    (rest : List (Word Nat)) (positive : classify first.head = true) :
    NegativeParts classify (first :: rest) = NegativeParts classify rest := by
  have token : taggedToken classify first = none := if_pos positive
  exact List.filterMap_cons_none token

theorem negative_parts_negative_cons (classify : Nat → Bool) (first : Word Nat)
    (rest : List (Word Nat)) (negative : classify first.head = false) :
    NegativeParts classify (first :: rest) = first :: NegativeParts classify rest := by
  have notPositive : classify first.head ≠ true := by
    intro positive
    have impossible : (false : Bool) = true := negative.symm.trans positive
    cases impossible
  have token : taggedToken classify first = some first := if_neg notPositive
  exact List.filterMap_cons_some token

theorem negative_parts_decompose (classify : Nat → Bool) (word : Word Nat) :
    NegativeParts classify (decompose classify word.toList) =
      (taggedSkeleton classify word.toList).filterMap id := by
  unfold NegativeParts taggedSkeleton
  rw [List.filterMap_map]
  rfl

theorem square_all_positive (classify : Nat → Bool) (roots : List (Word Nat))
    (agreement : MatchesRoots classify roots) (root : Word Nat) (member : root ∈ roots) :
    ∀ value ∈ (root ++ root).toList, classify value = true := by
  intro value inside
  have rootMember : value ∈ root.toList := by
    rw [Word.toList_append] at inside
    rcases List.mem_append.mp inside with first | second
    · exact first
    · exact second
  exact (agreement value).mpr ⟨root, member, rootMember⟩

theorem negative_parts_squares (classify : Nat → Bool) (roots : List (Word Nat))
    (agreement : MatchesRoots classify roots) (pieces : List (Word Nat)) :
    (∀ part ∈ pieces, ∃ root ∈ roots, part = root ++ root) →
      NegativeParts classify pieces = [] := by
  induction pieces with
  | nil =>
      intro _
      rfl
  | cons first rest ih =>
      intro squares
      obtain ⟨root, member, equal⟩ := squares first (List.mem_cons.mpr (Or.inl rfl))
      have positive : classify first.head = true := by
        rw [equal]
        exact square_all_positive classify roots agreement root member
          (root ++ root).head (word_head_member (root ++ root))
      rw [negative_parts_positive_cons classify first rest positive]
      apply ih
      intro part member
      exact squares part (List.mem_cons.mpr (Or.inr member))

/-- Positive refinement is applied to an actual global maximal factor.
Absent roots remain allowed: only present fine-positive runs are constrained. -/
theorem square_covered_positive (classify : Nat → Bool) (roots : List (Word Nat))
    (agreement : MatchesRoots classify roots) (word outer : Word Nat)
    (covered : SquareCovered roots word)
    (member : outer ∈ decompose classify word.toList)
    (positive : classify outer.head = true) : SquareCovered roots outer := by
  intro root rootMember inner innerMember innerPositive
  have contained : ∀ value, supportTag root value = true → classify value = true := by
    intro value present
    exact (agreement value).mpr ⟨root, rootMember, (supportTag_true root value).mp present⟩
  have original : inner ∈ decompose (supportTag root) word.toList :=
    positive_refinement (supportTag root) classify word outer inner
      contained member positive innerMember innerPositive
  exact covered root rootMember inner original innerPositive

/-- A genuinely positive global factor has no outside-root pieces. This uses
both exact coverage and actual constant-factor membership, not just its head. -/
theorem positive_fragment_partition (classify : Nat → Bool) (roots : List (Word Nat))
    (agreement : MatchesRoots classify roots) (word outer : Word Nat)
    (family : Family roots word) (member : outer ∈ decompose classify word.toList)
    (positive : classify outer.head = true) :
    ∃ parts : List (Word Nat), flatten parts = outer.toList ∧
      ∀ part ∈ parts, ∃ root ∈ roots, part = root ++ root := by
  have restricted : SquareCovered roots outer :=
    square_covered_positive classify roots agreement word outer
      (family_square_covered roots word family) member positive
  obtain ⟨parts, partition⟩ := partition_of_square_covered roots outer family.1 restricted
  refine ⟨parts, partition.1, ?_⟩
  intro part partMember
  rcases partition.2 part partMember with square | outside
  · exact square
  · have inOuter : part.head ∈ outer.toList :=
      part_letter_mem outer parts partition.1 part partMember part.head (word_head_member part)
    have constant : Constant classify outer :=
      good_member_constant classify (decompose_good classify word.toList) member
    have present : Covered roots part.head :=
      (agreement part.head).mp ((constant part.head inOuter).trans positive)
    exact False.elim (outside part.head (word_head_member part) present)

theorem negative_fragment_outside (classify : Nat → Bool) (roots : List (Word Nat))
    (agreement : MatchesRoots classify roots) (word outer : Word Nat)
    (member : outer ∈ decompose classify word.toList)
    (negative : classify outer.head = false) : Outside roots outer := by
  intro value inside covered
  have constant : Constant classify outer :=
    good_member_constant classify (decompose_good classify word.toList) member
  have negativeValue : classify value = false := (constant value inside).trans negative
  have positiveValue : classify value = true := (agreement value).mpr covered
  have impossible : (false : Bool) = true := negativeValue.symm.trans positiveValue
  cases impossible

/-- Assemble literal refinements while retaining their ordered negative-word
projection. Positive factors may split into multiple root squares. -/
theorem assemble_aligned_refinements (classify : Nat → Bool) (test : Word Nat → Prop)
    (factors : List (Word Nat)) :
    (∀ factor ∈ factors, ∃ parts : List (Word Nat),
      flatten parts = factor.toList ∧ (∀ part ∈ parts, test part) ∧
      NegativeParts classify parts = NegativeParts classify [factor]) →
    ∃ parts : List (Word Nat), flatten parts = flatten factors ∧
      (∀ part ∈ parts, test part) ∧
      NegativeParts classify parts = NegativeParts classify factors := by
  induction factors with
  | nil =>
      intro _
      refine ⟨[], rfl, ?_, rfl⟩
      intro part impossible
      cases impossible
  | cons factor factors ih =>
      intro each
      obtain ⟨first, firstEqual, firstTest, firstProjection⟩ :=
        each factor (List.mem_cons.mpr (Or.inl rfl))
      have tailEach : ∀ next ∈ factors, ∃ parts : List (Word Nat),
          flatten parts = next.toList ∧ (∀ part ∈ parts, test part) ∧
          NegativeParts classify parts = NegativeParts classify [next] := by
        intro next member
        exact each next (List.mem_cons.mpr (Or.inr member))
      obtain ⟨last, lastEqual, lastTest, lastProjection⟩ := ih tailEach
      refine ⟨first ++ last, ?_, ?_, ?_⟩
      · rw [flatten_append, firstEqual, lastEqual]
        rfl
      · intro part member
        rcases List.mem_append.mp member with firstMember | lastMember
        · exact firstTest part firstMember
        · exact lastTest part lastMember
      · rw [negative_parts_append, firstProjection, lastProjection]
        exact (negative_parts_append classify [factor] factors).symm

/-- The global negative runs are retained intact. Their ordered sequence is
therefore exactly the original maximal-factor sequence, not a refinement. -/
theorem family_maximal_partition (classify : Nat → Bool) (roots : List (Word Nat))
    (agreement : MatchesRoots classify roots) (word : Word Nat) (family : Family roots word) :
    ∃ pieces : List (Word Nat), SquarePartition roots word pieces ∧
      NegativeParts classify pieces = (taggedSkeleton classify word.toList).filterMap id := by
  have each : ∀ outer ∈ decompose classify word.toList, ∃ parts : List (Word Nat),
      flatten parts = outer.toList ∧ (∀ part ∈ parts, RootPiece roots part) ∧
      NegativeParts classify parts = NegativeParts classify [outer] := by
    intro outer member
    cases tag : classify outer.head with
    | true =>
        obtain ⟨parts, equal, squares⟩ :=
          positive_fragment_partition classify roots agreement word outer family member tag
        refine ⟨parts, equal, ?_, ?_⟩
        · intro part partMember
          exact Or.inl (squares part partMember)
        · rw [negative_parts_squares classify roots agreement parts squares,
            negative_parts_positive_cons classify outer [] tag]
          rfl
    | false =>
        refine ⟨[outer], ?_, ?_, rfl⟩
        · simp only [flatten, List.append_nil]
        · intro part partMember
          have equal : part = outer := List.mem_singleton.mp partMember
          subst part
          exact Or.inr (negative_fragment_outside classify roots agreement word outer member tag)
  obtain ⟨pieces, equal, kinds, projection⟩ :=
    assemble_aligned_refinements classify (RootPiece roots) (decompose classify word.toList) each
  refine ⟨pieces, ⟨equal.trans (flatten_decompose classify word.toList), kinds⟩, ?_⟩
  exact projection.trans (negative_parts_decompose classify word)

theorem matches_repeated (roots : List (Word Nat)) (word : Word Nat)
    (coverage : ∀ value, Covered roots value ↔ 2 ≤ word.toList.count value) :
    MatchesRoots (repeatedTag word) roots := by
  intro value
  constructor
  · intro positive
    change decide (2 ≤ word.toList.count value) = true at positive
    exact (coverage value).mpr (of_decide_eq_true positive)
  · intro covered
    change decide (2 ≤ word.toList.count value) = true
    exact decide_eq_true ((coverage value).mp covered)

/-- Every word derives a root-square partition whose negative subsequence
is literally the maximal simple-factor list of both input and normal word.
No canonical uniqueness or semantic comparison is assumed. -/
theorem normalize_with_maximal_simple_factors (word : Word Nat) :
    ∃ normal : Word Nat, ∃ roots : List (Word Nat), ∃ pieces : List (Word Nat),
      Derives basis word normal ∧ Family roots normal ∧ Terminal roots normal ∧
      (∀ value, Covered roots value ↔ 2 ≤ word.toList.count value) ∧
      (∀ value, Covered roots value ↔ 2 ≤ normal.toList.count value) ∧
      SquarePartition roots normal pieces ∧
      NegativeParts (repeatedTag normal) pieces = simpleFactors normal ∧
      NegativeParts (repeatedTag normal) pieces = simpleFactors word ∧
      (∀ part ∈ pieces, (∃ root ∈ roots, part = root ++ root) ∨
        (∀ value ∈ part.toList,
          word.toList.count value = 1 ∧ normal.toList.count value = 1)) := by
  obtain ⟨normal, roots, derived, family, terminal, original, current, counts, skeleton⟩ :=
    normalize_arbitrary_word word
  obtain ⟨pieces, partition, aligned⟩ :=
    family_maximal_partition (repeatedTag normal) roots
      (matches_repeated roots normal current) normal family
  have finalAligned : NegativeParts (repeatedTag normal) pieces = simpleFactors normal := aligned
  have same : simpleFactors word = simpleFactors normal :=
    simple_factors_of_skeleton word normal skeleton
  refine ⟨normal, roots, pieces, derived, family, terminal, original, current, partition,
    finalAligned, finalAligned.trans same.symm, ?_⟩
  intro part member
  rcases partition.2 part member with square | outside
  · exact Or.inl square
  · right
    intro value inside
    have finalSimple : normal.toList.count value = 1 :=
      outside_part_simple roots normal pieces partition current part member outside value inside
    have originalNotRepeated : ¬ 2 ≤ word.toList.count value := by
      intro repeated
      exact outside value inside ((original value).mpr repeated)
    have originalLow : word.toList.count value < 2 := by omega
    have unchanged : normal.toList.count value = word.toList.count value := counts value originalLow
    exact ⟨unchanged.symm.trans finalSimple, finalSimple⟩

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSimpleAlignment

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSimpleAlignment.negative_parts_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSimpleAlignment.negative_parts_positive_cons
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSimpleAlignment.negative_parts_negative_cons
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSimpleAlignment.negative_parts_decompose
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSimpleAlignment.square_all_positive
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSimpleAlignment.negative_parts_squares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSimpleAlignment.square_covered_positive
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSimpleAlignment.positive_fragment_partition
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSimpleAlignment.negative_fragment_outside
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSimpleAlignment.assemble_aligned_refinements
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSimpleAlignment.family_maximal_partition
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSimpleAlignment.matches_repeated
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSimpleAlignment.normalize_with_maximal_simple_factors

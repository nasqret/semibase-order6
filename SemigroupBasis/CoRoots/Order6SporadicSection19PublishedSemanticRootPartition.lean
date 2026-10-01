import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSemanticFormSpans

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticRootPartition

open MaximalFactors RootFamily CanonicalPresentation FirstReturnBridgeCut
open SemanticFormSpans ConnectedTerminalEndpoints

/-- Two marked occurrences in one list cannot each precede the other. -/
theorem exclusive_marked_cuts (first second : α) (before after before' after' : List α)
    (same : before ++ first :: after = before' ++ second :: after')
    (firstAbsent : first ∉ before') (secondAbsent : second ∉ before) : first = second := by
  induction before generalizing before' with
  | nil =>
    cases before' with
    | nil => exact (List.cons.inj same).1
    | cons head tail =>
      have firstHead : first = head := (List.cons.inj same).1
      exact False.elim (firstAbsent (List.mem_cons.mpr (Or.inl firstHead)))
  | cons head tail ih =>
    cases before' with
    | nil =>
      have secondHead : second = head := (List.cons.inj same).1.symm
      exact False.elim (secondAbsent (List.mem_cons.mpr (Or.inl secondHead)))
    | cons head' tail' =>
      have tailSame : tail ++ first :: after = tail' ++ second :: after' :=
        (List.cons.inj same).2
      exact ih tail' tailSame
        (fun member => firstAbsent (List.mem_cons_of_mem head' member))
        (fun member => secondAbsent (List.mem_cons_of_mem head member))

theorem square_member_letter (root : Word Nat) (pieces : List (Word Nat))
    (squareMember : (root ++ root) ∈ pieces) (letter : Nat) (member : letter ∈ root.toList) :
    letter ∈ flatten pieces := by
  apply (mem_flatten letter pieces).mpr
  refine ⟨root ++ root, squareMember, ?_⟩
  rw [Word.toList_append]
  exact List.mem_append.mpr (Or.inl member)

/-- The prefix of a chosen source root excludes every letter of a target root
sharing its support. The initial-root case has the genuinely empty prefix. -/
theorem root_cut_excludes_target (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target)
    (left : Form source) (right : Form target)
    (selected : Word Nat) (selectedMember : selected ∈ left.roots)
    (root : Word Nat) (rootMember : root ∈ right.roots)
    (shared : Nat) (inSelected : shared ∈ selected.toList) (inRoot : shared ∈ root.toList) :
    ∃ before after : List (Word Nat),
      left.first :: expand left.chunks = before ++ (selected ++ selected) :: after ∧
      ∀ letter ∈ root.toList, letter ∉ flatten before := by
  by_cases initial : selected ++ selected = left.first
  · refine ⟨[], expand left.chunks, ?_, ?_⟩
    · simp only [List.nil_append, initial]
    · intro letter _member impossible
      cases impossible
  · obtain ⟨before, inside, tail, split, shape, isolated, uniform⟩ :=
      noninitial_span_invariant source target equalEval left right selected selectedMember initial
    obtain ⟨rest, _initial, starts, _ends⟩ := span_endpoints (selected ++ selected) inside shape
    refine ⟨before, rest ++ tail, ?_, ?_⟩
    · rw [split, starts]
      simp only [List.cons_append]
    · intro letter member inBefore
      have inInside : letter ∈ flatten inside :=
        (uniform root rootMember shared inRoot letter member).mp
          (root_letter_in_span selected inside shape shared inSelected)
      exact isolated letter inInside (by
        rw [FactorBoundaries.flatten_append]
        exact List.mem_append.mpr (Or.inl inBefore))

/-- A target root cannot combine letters from distinct source roots. -/
theorem target_root_cannot_mix (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target)
    (left : Form source) (right : Form target)
    (first second : Word Nat) (firstMember : first ∈ left.roots) (secondMember : second ∈ left.roots)
    (root : Word Nat) (rootMember : root ∈ right.roots)
    (x y : Nat) (inFirst : x ∈ first.toList) (inSecond : y ∈ second.toList)
    (inX : x ∈ root.toList) (inY : y ∈ root.toList) : first = second := by
  obtain ⟨before, after, firstCut, firstExcludes⟩ :=
    root_cut_excludes_target source target equalEval left right first firstMember root rootMember x inFirst inX
  obtain ⟨before', after', secondCut, secondExcludes⟩ :=
    root_cut_excludes_target source target equalEval left right second secondMember root rootMember y inSecond inY
  have firstAbsent : (first ++ first) ∉ before' := fun member =>
    secondExcludes x inX (square_member_letter first before' member x inFirst)
  have secondAbsent : (second ++ second) ∉ before := fun member =>
    firstExcludes y inY (square_member_letter second before member y inSecond)
  have squaresEqual : first ++ first = second ++ second :=
    exclusive_marked_cuts (first ++ first) (second ++ second) before after before' after'
      (firstCut.symm.trans secondCut) firstAbsent secondAbsent
  have firstHeadInSecond : first.head ∈ second.toList := by
    have inSquare : first.head ∈ (first ++ first).toList := by
      rw [Word.toList_append]
      exact List.mem_append.mpr (Or.inl List.mem_cons_self)
    rw [squaresEqual, Word.toList_append] at inSquare
    exact (List.mem_append.mp inSquare).elim id id
  exact common_root_letter_eq left.roots source first second left.family firstMember secondMember
    first.head List.mem_cons_self firstHeadInSecond

theorem target_root_refines_source (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target)
    (left : Form source) (right : Form target)
    (root : Word Nat) (rootMember : root ∈ right.roots) :
    ∃ selected ∈ left.roots, ∀ letter ∈ root.toList, letter ∈ selected.toList := by
  have sourceCovered : Covered left.roots root.head :=
    (SemanticSimpleAdjacency.semantic_covered_iff source target equalEval left right root.head).mpr
      ⟨root, rootMember, List.mem_cons_self⟩
  obtain ⟨selected, selectedMember, headMember⟩ := sourceCovered
  refine ⟨selected, selectedMember, ?_⟩
  intro letter member
  have covered : Covered left.roots letter :=
    (SemanticSimpleAdjacency.semantic_covered_iff source target equalEval left right letter).mpr
      ⟨root, rootMember, member⟩
  obtain ⟨other, otherMember, inOther⟩ := covered
  have equal : selected = other := target_root_cannot_mix source target equalEval left right
    selected other selectedMember otherMember root rootMember root.head letter headMember inOther
    List.mem_cons_self member
  rw [equal]
  exact inOther

/-- Opposite-direction refinement and within-family disjointness give exact
support equality, not just containment in an enclosing span. -/
theorem matching_root_support (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target)
    (left : Form source) (right : Form target)
    (root : Word Nat) (rootMember : root ∈ right.roots) :
    ∃ selected ∈ left.roots, ∀ letter, letter ∈ root.toList ↔ letter ∈ selected.toList := by
  obtain ⟨selected, selectedMember, forward⟩ :=
    target_root_refines_source source target equalEval left right root rootMember
  have reverseEval : SemanticSimpleAdjacency.EqualEval target source := fun valuation => (equalEval valuation).symm
  obtain ⟨other, otherMember, backward⟩ :=
    target_root_refines_source target source reverseEval right left selected selectedMember
  have equal : root = other := common_root_letter_eq right.roots target root other right.family
    rootMember otherMember root.head List.mem_cons_self
    (backward root.head (forward root.head List.mem_cons_self))
  refine ⟨selected, selectedMember, ?_⟩
  intro letter
  constructor
  · exact forward letter
  · intro member
    rw [equal]
    exact backward letter member

theorem root_shape_support_injective (left right : Word Nat)
    (leftShape : RootShape left) (rightShape : RootShape right)
    (same : ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList) : left = right := by
  have permutation : left.toList.Perm right.toList := List.perm_iff_count.mpr (by
    intro letter
    by_cases member : letter ∈ left.toList
    · have onRight : letter ∈ right.toList := (same letter).mp member
      rw [leftShape.1.count, rightShape.1.count, if_pos member, if_pos onRight]
    · have onRight : letter ∉ right.toList := fun h => member ((same letter).mpr h)
      rw [leftShape.1.count, rightShape.1.count, if_neg member, if_neg onRight])
  apply Word.toList_injective
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => Nat.le_antisymm hab hba)
    leftShape.2 rightShape.2 permutation

/-- Actual C8 semantic equality preserves the literal ordered roots as a SET.
No order on the list of roots, canonical gaps, or chunks is asserted here. -/
theorem semantic_root_set (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target)
    (left : Form source) (right : Form target) (root : Word Nat) :
    root ∈ left.roots ↔ root ∈ right.roots := by
  constructor
  · intro member
    have reverseEval : SemanticSimpleAdjacency.EqualEval target source := fun valuation => (equalEval valuation).symm
    obtain ⟨other, otherMember, support⟩ := matching_root_support target source reverseEval right left root member
    have equal := root_shape_support_injective root other (left.family.2 root member).1
      (right.family.2 other otherMember).1 support
    rw [equal]
    exact otherMember
  · intro member
    obtain ⟨other, otherMember, support⟩ := matching_root_support source target equalEval left right root member
    have equal := root_shape_support_injective root other (right.family.2 root member).1
      (left.family.2 other otherMember).1 support
    rw [equal]
    exact otherMember

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticRootPartition

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticRootPartition.exclusive_marked_cuts
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticRootPartition.square_member_letter
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticRootPartition.root_cut_excludes_target
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticRootPartition.target_root_cannot_mix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticRootPartition.target_root_refines_source
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticRootPartition.matching_root_support
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticRootPartition.root_shape_support_injective
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticRootPartition.semantic_root_set

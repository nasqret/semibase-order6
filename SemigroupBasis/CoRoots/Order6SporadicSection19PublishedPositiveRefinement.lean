import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSkeletonTransport

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement

open MaximalFactors FactorBoundaries CanonicalSquareCover BlockAlignment
open OccurrenceMacro MacroWitnesses FactorCodec SquarePermutation

theorem firstOK_of_all {α : Type} (test : α → Prop) (letters : List α)
    (all : ∀ value ∈ letters, test value) : FirstOK test letters := by
  intro first rest split
  apply all first
  rw [split]
  exact List.mem_cons.mpr (Or.inl rfl)

theorem lastOK_of_all {α : Type} (test : α → Prop) (letters : List α)
    (all : ∀ value ∈ letters, test value) : LastOK test letters := by
  apply lastOK_of_witness
  intro before last split
  apply all last
  rw [split]
  exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

theorem firstOK_prefix {α : Type} (test : α → Prop) (left right : List α)
    (whole : FirstOK test (left ++ right)) : FirstOK test left := by
  intro first rest split
  apply whole first (rest ++ right)
  rw [split]
  rfl

theorem lastOK_suffix {α : Type} (test : α → Prop) (left right : List α)
    (whole : LastOK test (left ++ right)) : LastOK test right := by
  apply lastOK_of_witness
  intro before last split
  apply lastOK_witness test (left ++ right) whole (left ++ before) last
  rw [split, List.append_assoc]

theorem lastOK_append_right {α : Type} (test : α → Prop) (left right : List α)
    (nonempty : right ≠ []) (rightOK : LastOK test right) :
    LastOK test (left ++ right) := by
  intro last before split
  have mirrored : right.reverse ++ left.reverse = last :: before := by
    simpa only [List.reverse_append] using split
  cases actual : right.reverse with
  | nil =>
      have reversed := congrArg List.reverse actual
      have empty : right = [] := by
        simpa only [List.reverse_reverse, List.reverse_nil] using reversed
      exact False.elim (nonempty empty)
  | cons first rest =>
      rw [actual] at mirrored
      have equal : first = last := (List.cons.inj mirrored).1
      exact equal ▸ rightOK first rest actual

theorem firstOK_map {α β : Type} (test : α → Prop) (imageTest : β → Prop)
    (image : α → β) (letters : List α) (good : FirstOK test letters)
    (maps : ∀ value, test value → imageTest (image value)) :
    FirstOK imageTest (letters.map image) := by
  intro first rest split
  cases letters with
  | nil => cases split
  | cons value later =>
      have equal : image value = first := (List.cons.inj split).1
      exact equal ▸ maps value (good value later rfl)

theorem lastOK_map {α β : Type} (test : α → Prop) (imageTest : β → Prop)
    (image : α → β) (letters : List α) (good : LastOK test letters)
    (maps : ∀ value, test value → imageTest (image value)) :
    LastOK imageTest (letters.map image) := by
  change FirstOK imageTest (letters.map image).reverse
  rw [← List.map_reverse]
  exact firstOK_map test imageTest image letters.reverse good maps

theorem firstOK_flatten (test : Nat → Prop) (pieces : List (Word Nat))
    (good : FirstOK (fun piece => ∀ value ∈ piece.toList, test value) pieces) :
    FirstOK test (flatten pieces) := by
  intro value rest split
  cases pieces with
  | nil => cases split
  | cons first later =>
      have equal : first.head = value := (List.cons.inj split).1
      exact equal ▸ good first later rfl first.head (word_head_member first)

theorem lastOK_flatten (test : Nat → Prop) (pieces : List (Word Nat))
    (good : LastOK (fun piece => ∀ value ∈ piece.toList, test value) pieces) :
    LastOK test (flatten pieces) := by
  rcases nil_or_last pieces with empty | ending
  · subst pieces
    intro value rest impossible
    cases impossible
  · obtain ⟨before, last, split⟩ := ending
    have all : ∀ value ∈ last.toList, test value :=
      lastOK_witness _ pieces good before last split
    have flat : flatten pieces = flatten before ++ last.toList := by
      rw [split, FactorBoundaries.flatten_append]
      simp only [flatten, List.append_nil]
    rw [flat]
    exact lastOK_append_right test (flatten before) last.toList
      (by intro impossible; cases impossible) (lastOK_of_all test last.toList all)

theorem flatten_singletons (letters : List Nat) :
    flatten (letters.map Word.singleton) = letters := by
  induction letters with
  | nil => rfl
  | cons first rest ih =>
      change first :: flatten (rest.map Word.singleton) = first :: rest
      rw [ih]

/-- Every actual positive fine run is a maximal fine run inside a positive
coarse run. Both original position boundaries, not just a head-letter witness,
are transported to its exact containing coarse occurrence. -/
theorem positive_exhaustive (fine coarse : Nat → Bool) (word inner : Word Nat)
    (contained : ∀ value, fine value = true → coarse value = true)
    (member : inner ∈ decompose fine word.toList) (positive : fine inner.head = true) :
    ∃ outer : Word Nat, outer ∈ decompose coarse word.toList ∧
      coarse outer.head = true ∧ inner ∈ decompose fine outer.toList := by
  obtain ⟨before, after, _, actual, uniform, leftBoundary, rightBoundary⟩ :=
    factor_witness fine word.toList inner member
  have coarsePositive : coarse inner.head = true := contained inner.head positive
  have coarseUniform : Constant coarse inner := by
    intro value inside
    exact (contained value ((uniform value inside).trans positive)).trans coarsePositive.symm
  obtain ⟨earlier, later, outer, insideBefore, insideAfter,
    coarseSplit, innerSplit, leftContext, rightContext, sameTag⟩ :=
    located_occurrence coarse inner (flatten before) (flatten after) coarseUniform
  have outerMember : outer ∈ decompose coarse word.toList := by
    rw [actual, coarseSplit]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  let test : Nat → Prop := fun value => fine value ≠ fine inner.head
  let blockTest : Word Nat → Prop := fun piece => ∀ value ∈ piece.toList, test value
  have leftLetters : LastOK test (flatten before) :=
    lastOK_flatten test before (lastOK_of_witness blockTest before leftBoundary)
  have rightLetters : FirstOK test (flatten after) :=
    firstOK_flatten test after rightBoundary
  have leftInside : LastOK test insideBefore := by
    apply lastOK_suffix test (flatten earlier) insideBefore
    rw [← leftContext]
    exact leftLetters
  have rightInside : FirstOK test insideAfter := by
    apply firstOK_prefix test insideAfter (flatten later)
    rw [← rightContext]
    exact rightLetters
  have singletonTest : ∀ value, test value → blockTest (Word.singleton value) := by
    intro value sign letter inside
    have equal : letter = value := List.mem_singleton.mp inside
    exact equal.symm ▸ sign
  have fineMember : inner ∈ decompose fine outer.toList :=
    canonical_member_of_boundaries fine outer.toList inner
      (insideBefore.map Word.singleton) (insideAfter.map Word.singleton)
      (by simp only [flatten_singletons]; exact innerSplit) uniform
      (lastOK_map test blockTest Word.singleton insideBefore leftInside singletonTest)
      (firstOK_map test blockTest Word.singleton insideAfter rightInside singletonTest)
  exact ⟨outer, outerMember, sameTag.trans coarsePositive, fineMember⟩

theorem positive_member_iff (fine coarse : Nat → Bool) (word inner : Word Nat)
    (contained : ∀ value, fine value = true → coarse value = true)
    (positive : fine inner.head = true) :
    inner ∈ decompose fine word.toList ↔
      ∃ outer : Word Nat, outer ∈ decompose coarse word.toList ∧
        coarse outer.head = true ∧ inner ∈ decompose fine outer.toList := by
  constructor
  · exact fun member => positive_exhaustive fine coarse word inner contained member positive
  · rintro ⟨outer, outerMember, outerPositive, innerMember⟩
    exact positive_refinement fine coarse word outer inner contained
      outerMember outerPositive innerMember positive

theorem tagged_negative_member_iff (classify : Nat → Bool) (letters : List Nat)
    (piece : Word Nat) :
    some piece ∈ taggedSkeleton classify letters ↔
      piece ∈ decompose classify letters ∧ classify piece.head = false := by
  change some piece ∈ (decompose classify letters).map (taggedToken classify) ↔ _
  constructor
  · intro present
    obtain ⟨factor, member, equal⟩ := List.mem_map.mp present
    by_cases positive : classify factor.head = true
    · rw [taggedToken, if_pos positive] at equal
      cases equal
    · have literal : some factor = some piece := by
        simpa only [taggedToken, if_neg positive] using equal
      have identical : factor = piece := Option.some.inj literal
      subst factor
      exact ⟨member, FactorBoundaries.false_of_ne_true _ positive⟩
  · rintro ⟨member, negative⟩
    refine List.mem_map.mpr ⟨piece, member, ?_⟩
    have notPositive : classify piece.head ≠ true := by
      rw [negative]
      decide
    rw [taggedToken, if_neg notPositive]

/-- Literal negative coarse factors determine every positive run whose support
is disjoint from the coarse tag. No ordered-projection shortcut is assumed. -/
theorem positive_transport (fine coarse : Nat → Bool) (word normal piece : Word Nat)
    (excluded : ∀ value, fine value = true → coarse value = false)
    (same : taggedSkeleton coarse word.toList = taggedSkeleton coarse normal.toList)
    (member : piece ∈ decompose fine word.toList) (positive : fine piece.head = true) :
    piece ∈ decompose fine normal.toList := by
  let complement : Nat → Bool := fun value => !(coarse value)
  have contained : ∀ value, fine value = true → complement value = true := by
    intro value sign
    change Bool.not (coarse value) = true
    rw [excluded value sign]
    rfl
  obtain ⟨outer, outerMember, outerPositive, innerMember⟩ :=
    positive_exhaustive fine complement word piece contained member positive
  have oldOuter : outer ∈ decompose coarse word.toList := by
    simpa only [complement, decompose_not] using outerMember
  have negative : coarse outer.head = false := by
    cases tag : coarse outer.head with
    | false => rfl
    | true =>
        have impossible : Bool.not (coarse outer.head) = true := outerPositive
        rw [tag] at impossible
        cases impossible
  have token : some outer ∈ taggedSkeleton coarse word.toList :=
    (tagged_negative_member_iff coarse word.toList outer).mpr ⟨oldOuter, negative⟩
  rw [same] at token
  have newOuter := ((tagged_negative_member_iff coarse normal.toList outer).mp token).1
  have newComplement : outer ∈ decompose complement normal.toList := by
    simpa only [complement, decompose_not] using newOuter
  exact positive_refinement fine complement normal outer piece contained
    newComplement outerPositive innerMember positive

theorem positive_transport_iff (fine coarse : Nat → Bool) (word normal piece : Word Nat)
    (excluded : ∀ value, fine value = true → coarse value = false)
    (same : taggedSkeleton coarse word.toList = taggedSkeleton coarse normal.toList)
    (positive : fine piece.head = true) :
    piece ∈ decompose fine word.toList ↔ piece ∈ decompose fine normal.toList := by
  constructor
  · exact fun member => positive_transport fine coarse word normal piece excluded same member positive
  · exact fun member => positive_transport fine coarse normal word piece excluded same.symm member positive

/-- Includes the nonvacuous square occurrence, not merely the universal
classification of factors that happen to exist. -/
theorem canonical_perfect_transport (root : Word Nat) (coarse : Nat → Bool)
    (word normal : Word Nat)
    (excluded : ∀ value, supportTag root value = true → coarse value = false)
    (same : taggedSkeleton coarse word.toList = taggedSkeleton coarse normal.toList)
    (perfect : CanonicalPerfect root word) : CanonicalPerfect root normal := by
  have squarePositive : supportTag root (root ++ root).head = true :=
    (supportTag_true root root.head).mpr (word_head_member root)
  constructor
  · exact positive_transport (supportTag root) coarse word normal (root ++ root)
      excluded same perfect.1 squarePositive
  · intro piece member positive
    have oldMember := positive_transport (supportTag root) coarse normal word piece
      excluded same.symm member positive
    exact perfect.2 piece oldMember positive

/-- The single actual fused normal preserves EVERY previously perfect root
disjoint from the two merged supports. All compatibility is derived from
disjointness, and every hypothesis refers to the original word. -/
theorem generalized_fusion_preserves_earlier (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (related : GeneralizedRelated leftRoot rightRoot word) :
    ∃ normal : Word Nat, Derives basis word normal ∧
      CanonicalPerfect (sortedRoot (leftRoot ++ rightRoot)) normal ∧
      taggedSkeleton (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList =
        taggedSkeleton (unionTag (supportTag leftRoot) (supportTag rightRoot)) normal.toList ∧
      ∀ earlier : Word Nat,
        (∀ value ∈ earlier.toList, value ∉ leftRoot.toList) →
        (∀ value ∈ earlier.toList, value ∉ rightRoot.toList) →
        CanonicalPerfect earlier word → CanonicalPerfect earlier normal := by
  obtain ⟨normal, derived, mergedPerfect, skeleton⟩ :=
    SkeletonTransport.generalized_sorted_union_preserving leftRoot rightRoot word
      apart leftPerfect rightPerfect related
  refine ⟨normal, derived, mergedPerfect, skeleton, ?_⟩
  intro earlier leftApart rightApart perfect
  apply canonical_perfect_transport earlier
    (unionTag (supportTag leftRoot) (supportTag rightRoot)) word normal _ skeleton perfect
  intro value present
  have member : value ∈ earlier.toList := (supportTag_true earlier value).mp present
  have leftFalse : supportTag leftRoot value = false :=
    FactorBoundaries.false_of_ne_true _ (fun positive =>
      leftApart value member ((supportTag_true leftRoot value).mp positive))
  have rightFalse : supportTag rightRoot value = false :=
    FactorBoundaries.false_of_ne_true _ (fun positive =>
      rightApart value member ((supportTag_true rightRoot value).mp positive))
  unfold unionTag
  rw [leftFalse, rightFalse]
  rfl

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.firstOK_of_all
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.lastOK_of_all
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.firstOK_prefix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.lastOK_suffix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.lastOK_append_right
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.firstOK_map
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.lastOK_map
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.firstOK_flatten
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.lastOK_flatten
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.flatten_singletons
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.positive_exhaustive
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.positive_member_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.tagged_negative_member_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.positive_transport
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.positive_transport_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.canonical_perfect_transport
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PositiveRefinement.generalized_fusion_preserves_earlier

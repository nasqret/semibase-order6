import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSimpleFactorGraph

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorRepresentation

open MaximalFactors FactorBoundaries BlockAlignment FactorCodec
open SimpleFactorInvariant SimpleFactorGraph MaximalSimpleAlignment

theorem firstOK_singletons (test : Nat → Prop) (letters : List Nat)
    (boundary : FirstOK test letters) :
    FirstOK (fun piece : Word Nat => ∀ value ∈ piece.toList, test value)
      (letters.map Word.singleton) := by
  intro first rest split value member
  cases letters with
  | nil => cases split
  | cons letter later =>
    have equal : Word.singleton letter = first := (List.cons.inj split).1
    rw [← equal] at member
    change value ∈ [letter] at member
    have valueEqual : value = letter := List.mem_singleton.mp member
    rw [valueEqual]
    exact boundary letter later rfl

theorem lastOK_singletons (test : Nat → Prop) (letters : List Nat)
    (boundary : LastOK test letters) :
    LastOK (fun piece : Word Nat => ∀ value ∈ piece.toList, test value)
      (letters.map Word.singleton) := by
  change FirstOK (fun piece : Word Nat => ∀ value ∈ piece.toList, test value)
    (letters.map Word.singleton).reverse
  rw [← List.map_reverse]
  exact firstOK_singletons test letters.reverse boundary

theorem firstOK_append_left (test : Nat → Prop) (left right : List Nat)
    (nonempty : left ≠ []) (boundary : FirstOK test left) :
    FirstOK test (left ++ right) := by
  intro first rest split
  cases left with
  | nil => exact False.elim (nonempty rfl)
  | cons letter later =>
    have equal : letter = first := (List.cons.inj split).1
    exact equal ▸ boundary letter later rfl

theorem lastOK_append_right (test : Nat → Prop) (left right : List Nat)
    (nonempty : right ≠ []) (boundary : LastOK test right) :
    LastOK test (left ++ right) := by
  change FirstOK test (left ++ right).reverse
  rw [List.reverse_append]
  have nonemptyReverse : right.reverse ≠ [] := by
    intro empty
    exact nonempty (List.reverse_eq_nil_iff.mp empty)
  exact firstOK_append_left test right.reverse left.reverse nonemptyReverse boundary

theorem lastOK_of_members (test : Nat → Prop) (letters : List Nat)
    (every : ∀ value ∈ letters, test value) : LastOK test letters := by
  intro last earlier split
  apply every last
  apply List.mem_reverse.mp
  rw [split]
  exact List.mem_cons_self

theorem firstOK_flatten (test : Nat → Prop) (pieces : List (Word Nat))
    (boundary : FirstOK (fun piece : Word Nat => ∀ value ∈ piece.toList, test value) pieces) :
    FirstOK test (flatten pieces) := by
  intro first rest split
  cases pieces with
  | nil => cases split
  | cons piece later =>
    have equal : piece.head = first := (List.cons.inj split).1
    exact equal ▸ boundary piece later rfl piece.head (word_head_member piece)

theorem lastOK_flatten (test : Nat → Prop) (pieces : List (Word Nat))
    (boundary : LastOK (fun piece : Word Nat => ∀ value ∈ piece.toList, test value) pieces) :
    LastOK test (flatten pieces) := by
  rcases nil_or_last pieces with empty | witness
  · subst pieces
    intro last earlier split
    cases split
  · obtain ⟨earlier, last, split⟩ := witness
    have every : ∀ value ∈ last.toList, test value :=
      lastOK_witness _ pieces boundary earlier last split
    rw [split, FactorBoundaries.flatten_append]
    change LastOK test (flatten earlier ++ (last.toList ++ []))
    rw [List.append_nil]
    exact lastOK_append_right test (flatten earlier) last.toList (piece_nonempty last)
      (lastOK_of_members test last.toList every)

/-- A simple letter occurs only once, so local exterior boundaries exclude
extensions at every possible occurrence of this same literal factor. -/
theorem maximal_of_context_boundaries (whole : List Nat) (piece : Word Nat)
    (before after : List Nat) (literal : whole = before ++ piece.toList ++ after)
    (simple : SimpleLetters whole piece.toList)
    (leftBoundary : LastOK (fun value => whole.count value ≠ 1) before)
    (rightBoundary : FirstOK (fun value => whole.count value ≠ 1) after) :
    MaximalSimple whole piece.toList := by
  have once : whole.count piece.head = 1 := simple piece.head (word_head_member piece)
  have marked : whole = before ++ piece.head :: (piece.tail ++ after) := by
    simpa only [Word.toList, List.append_assoc, List.cons_append] using literal
  have absent := (split_no_member whole piece.head before (piece.tail ++ after) marked once).1
  refine ⟨piece_nonempty piece, simple, ⟨before, after, literal⟩, ?_, ?_⟩
  · intro letter letterOnce extension
    obtain ⟨outerBefore, outerAfter, extensionLiteral⟩ := extension
    have extensionMarked : whole = (outerBefore ++ [letter]) ++
        piece.head :: (piece.tail ++ outerAfter) := by
      simpa only [Word.toList, List.append_assoc, List.cons_append, List.nil_append]
        using extensionLiteral
    have extensionAbsent := (split_no_member whole piece.head (outerBefore ++ [letter])
      (piece.tail ++ outerAfter) extensionMarked once).1
    have beforeEqual : before = outerBefore ++ [letter] :=
      (unique_splits piece.head before (outerBefore ++ [letter]) (piece.tail ++ after)
        (piece.tail ++ outerAfter) absent extensionAbsent
        (marked.symm.trans extensionMarked)).1
    exact (lastOK_witness _ before leftBoundary outerBefore letter beforeEqual) letterOnce
  · intro letter letterOnce extension
    obtain ⟨outerBefore, outerAfter, extensionLiteral⟩ := extension
    have extensionMarked : whole = outerBefore ++
        piece.head :: (piece.tail ++ letter :: outerAfter) := by
      simpa only [Word.toList, List.append_assoc, List.cons_append, List.nil_append]
        using extensionLiteral
    have extensionAbsent := (split_no_member whole piece.head outerBefore
      (piece.tail ++ letter :: outerAfter) extensionMarked once).1
    have tailEqual : piece.tail ++ after = piece.tail ++ letter :: outerAfter :=
      (unique_splits piece.head before outerBefore (piece.tail ++ after)
        (piece.tail ++ letter :: outerAfter) absent extensionAbsent
        (marked.symm.trans extensionMarked)).2
    have afterEqual : after = letter :: outerAfter := List.append_inj_right tailEqual rfl
    exact rightBoundary letter outerAfter afterEqual letterOnce

theorem maximal_context_boundaries (whole : List Nat) (piece : Word Nat)
    (before after : List Nat) (literal : whole = before ++ piece.toList ++ after)
    (maximal : MaximalSimple whole piece.toList) :
    LastOK (fun value => whole.count value ≠ 1) before ∧
    FirstOK (fun value => whole.count value ≠ 1) after := by
  constructor
  · apply lastOK_of_witness
    intro earlier letter split once
    apply maximal.2.2.2.1 letter once
    refine ⟨earlier, after, ?_⟩
    rw [literal, split]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · intro letter later split once
    apply maximal.2.2.2.2 letter once
    refine ⟨before, later, ?_⟩
    rw [literal, split]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem repeated_false_of_once (word : Word Nat) (letter : Nat)
    (once : word.toList.count letter = 1) : repeatedTag word letter = false := by
  change decide (2 ≤ word.toList.count letter) = false
  exact decide_eq_false (by omega)

theorem repeated_false_iff_once (word : Word Nat) (letter : Nat)
    (present : letter ∈ word.toList) :
    repeatedTag word letter = false ↔ word.toList.count letter = 1 := by
  constructor
  · intro negative
    change decide (2 ≤ word.toList.count letter) = false at negative
    have below : ¬ 2 ≤ word.toList.count letter := of_decide_eq_false negative
    have positive : 0 < word.toList.count letter := List.count_pos_iff.mpr present
    omega
  · exact repeated_false_of_once word letter

/-- A selected negative decompose run is globally maximal simple, not merely
a constant word with a simple head or a factor of some selected run. -/
theorem decompose_negative_maximal (word piece : Word Nat)
    (member : piece ∈ decompose (repeatedTag word) word.toList)
    (negative : repeatedTag word piece.head = false) :
    MaximalSimple word.toList piece.toList := by
  obtain ⟨before, after, _partsEqual, rendered, uniform, leftBoundary, rightBoundary⟩ :=
    factor_witness (repeatedTag word) word.toList piece member
  have simple : SimpleLetters word.toList piece.toList := by
    intro value inside
    have present : value ∈ word.toList := by
      rw [rendered]
      exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl inside)))
    exact (repeated_false_iff_once word value present).mp ((uniform value inside).trans negative)
  have leftCount : LastOK (fun previous : Word Nat =>
      ∀ value ∈ previous.toList, word.toList.count value ≠ 1) before := by
    apply lastOK_of_witness
    intro earlier last split value inside once
    exact leftBoundary earlier last split value inside
      ((repeated_false_of_once word value once).trans negative.symm)
  have rightCount : FirstOK (fun next : Word Nat =>
      ∀ value ∈ next.toList, word.toList.count value ≠ 1) after := by
    intro next later split value inside once
    exact rightBoundary next later split value inside
      ((repeated_false_of_once word value once).trans negative.symm)
  have literal : word.toList = flatten before ++ piece.toList ++ flatten after := by
    simpa only [List.append_assoc] using rendered
  exact maximal_of_context_boundaries word.toList piece (flatten before) (flatten after)
    literal simple (lastOK_flatten _ before leftCount) (firstOK_flatten _ after rightCount)

/-- Global maximality gives actual count-changing boundaries. Singleton
contexts feed these exact boundaries to the existing canonical-run theorem. -/
theorem maximal_decompose_member (word piece : Word Nat)
    (maximal : MaximalSimple word.toList piece.toList) :
    piece ∈ decompose (repeatedTag word) word.toList := by
  obtain ⟨before, after, literal⟩ := maximal.2.2.1
  have simple : SimpleLetters word.toList piece.toList := maximal.2.1
  have negative : repeatedTag word piece.head = false :=
    repeated_false_of_once word piece.head (simple piece.head (word_head_member piece))
  have uniform : Constant (repeatedTag word) piece := by
    intro value inside
    exact (repeated_false_of_once word value (simple value inside)).trans negative.symm
  have closed := maximal_context_boundaries word.toList piece before after literal maximal
  have leftTag : LastOK (fun value =>
      repeatedTag word value ≠ repeatedTag word piece.head) before := by
    apply lastOK_of_witness
    intro earlier letter split equal
    have inBefore : letter ∈ before := by
      rw [split]
      exact List.mem_append_right earlier List.mem_cons_self
    have present : letter ∈ word.toList := by
      rw [literal]
      exact List.mem_append_left after (List.mem_append_left piece.toList inBefore)
    have once := (repeated_false_iff_once word letter present).mp (equal.trans negative)
    exact (lastOK_witness _ before closed.1 earlier letter split) once
  have rightTag : FirstOK (fun value =>
      repeatedTag word value ≠ repeatedTag word piece.head) after := by
    intro letter later split equal
    have inAfter : letter ∈ after := by
      rw [split]
      exact List.mem_cons_self
    have present : letter ∈ word.toList := by
      rw [literal]
      exact List.mem_append_right (before ++ piece.toList) inAfter
    have once := (repeated_false_iff_once word letter present).mp (equal.trans negative)
    exact closed.2 letter later split once
  have actual : word.toList = flatten (before.map Word.singleton) ++
      (piece.toList ++ flatten (after.map Word.singleton)) := by
    simpa only [PositiveRefinement.flatten_singletons, List.append_assoc] using literal
  exact canonical_member_of_boundaries (repeatedTag word) word.toList piece
    (before.map Word.singleton) (after.map Word.singleton) actual uniform
    (lastOK_singletons _ before leftTag) (firstOK_singletons _ after rightTag)

theorem simpleFactors_mem_iff_decompose (word piece : Word Nat) :
    piece ∈ simpleFactors word ↔
      piece ∈ decompose (repeatedTag word) word.toList ∧
      repeatedTag word piece.head = false := by
  change piece ∈ (taggedSkeleton (repeatedTag word) word.toList).filterMap id ↔ _
  rw [← negative_parts_decompose (repeatedTag word) word]
  unfold NegativeParts
  constructor
  · intro member
    obtain ⟨candidate, inside, token⟩ := List.mem_filterMap.mp member
    by_cases positive : repeatedTag word candidate.head = true
    · rw [taggedToken, if_pos positive] at token
      cases token
    · have someEqual : some candidate = some piece := by
        simpa only [taggedToken, if_neg positive] using token
      have equal : candidate = piece := Option.some.inj someEqual
      subst candidate
      exact ⟨inside, false_of_ne_true _ positive⟩
  · intro ⟨inside, negative⟩
    apply List.mem_filterMap.mpr
    refine ⟨piece, inside, ?_⟩
    have notPositive : repeatedTag word piece.head ≠ true := by
      intro positive
      have impossible : (false : Bool) = true := negative.symm.trans positive
      cases impossible
    unfold taggedToken
    exact if_neg notPositive

/-- Exact adapter for the already-defined factor list; no replacement
definition and no caller-supplied representation assumption. -/
theorem simpleFactors_mem_iff (word piece : Word Nat) :
    piece ∈ simpleFactors word ↔ MaximalSimple word.toList piece.toList := by
  constructor
  · intro member
    obtain ⟨inside, negative⟩ := (simpleFactors_mem_iff_decompose word piece).mp member
    exact decompose_negative_maximal word piece inside negative
  · intro maximal
    apply (simpleFactors_mem_iff_decompose word piece).mpr
    exact ⟨maximal_decompose_member word piece maximal,
      repeated_false_of_once word piece.head (maximal.2.1 piece.head (word_head_member piece))⟩

/-- DX's exact vertex/edge hypotheses now transfer membership in the ACTUAL
stored maximal-simple-factor list. No assertion about list order is made. -/
theorem simpleFactors_set_transfer (source target : Word Nat)
    (sameSimple : SameSimple source.toList target.toList)
    (sameEdges : SameEdges source.toList target.toList) (piece : Word Nat) :
    piece ∈ simpleFactors source ↔ piece ∈ simpleFactors target := by
  rw [simpleFactors_mem_iff source piece, simpleFactors_mem_iff target piece]
  exact maximal_simple_iff source.toList target.toList piece.toList sameSimple sameEdges

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorRepresentation

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorRepresentation.maximal_of_context_boundaries
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorRepresentation.maximal_context_boundaries
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorRepresentation.repeated_false_iff_once
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorRepresentation.decompose_negative_maximal
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorRepresentation.maximal_decompose_member
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorRepresentation.simpleFactors_mem_iff_decompose
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorRepresentation.simpleFactors_mem_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorRepresentation.simpleFactors_set_transfer

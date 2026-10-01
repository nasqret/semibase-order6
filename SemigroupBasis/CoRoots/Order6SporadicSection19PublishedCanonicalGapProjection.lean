import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSimpleFactorRepresentation

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalGapProjection

open MaximalFactors FactorBoundaries CanonicalSquareCover BlockAlignment
open FactorCodec SimpleFactorInvariant MaximalSimpleAlignment CanonicalPresentation
open SimpleFactorGraph SimpleFactorRepresentation

/-- Flatten each actual gap, omit empty gaps, and retain the original order. -/
def gapProjection : List Chunk → List (Word Nat)
  | [] => []
  | entry :: rest => MaximalSquareCover.optionalPieces (flatten entry.1) ++ gapProjection rest

theorem negative_insert_positive (classify : Nat → Bool) (letter : Nat)
    (pieces : List (Word Nat)) (positive : classify letter = true) :
    NegativeParts classify (insertLetter classify letter pieces) = NegativeParts classify pieces := by
  cases pieces with
  | nil =>
    change NegativeParts classify [Word.singleton letter] = NegativeParts classify []
    exact negative_parts_positive_cons classify (Word.singleton letter) [] positive
  | cons first rest =>
    by_cases same : classify letter = classify first.head
    · rw [insertLetter, if_pos same]
      have firstPositive : classify first.head = true := same.symm.trans positive
      rw [negative_parts_positive_cons classify (⟨letter, first.toList⟩ : Word Nat) rest positive,
        negative_parts_positive_cons classify first rest firstPositive]
    · rw [insertLetter, if_neg same]
      exact negative_parts_positive_cons classify (Word.singleton letter) (first :: rest) positive

theorem negative_decompose_positive_prefix (classify : Nat → Bool)
    (positivePart after : List Nat) :
    (∀ letter ∈ positivePart, classify letter = true) →
      NegativeParts classify (decompose classify (positivePart ++ after)) =
        NegativeParts classify (decompose classify after) := by
  induction positivePart with
  | nil =>
    intro _positive
    rfl
  | cons letter later ih =>
    intro positive
    have firstPositive : classify letter = true := positive letter List.mem_cons_self
    have laterPositive : ∀ value ∈ later, classify value = true := by
      intro value member
      exact positive value (List.mem_cons_of_mem letter member)
    change NegativeParts classify (insertLetter classify letter
      (decompose classify (later ++ after))) = NegativeParts classify (decompose classify after)
    rw [negative_insert_positive classify letter _ firstPositive]
    exact ih laterPositive

/-- A negative gap before an actual positive word is one complete negative
run, including the case that the gap has no letters at all. -/
theorem negative_decompose_gap_before_positive (classify : Nat → Bool)
    (gap : List Nat) (first : Word Nat) (after : List Nat)
    (negative : ∀ letter ∈ gap, classify letter = false)
    (firstPositive : classify first.head = true) :
    NegativeParts classify (decompose classify (gap ++ (first.toList ++ after))) =
      MaximalSquareCover.optionalPieces gap ++
        NegativeParts classify (decompose classify (first.toList ++ after)) := by
  cases gap with
  | nil =>
    simp only [List.nil_append, MaximalSquareCover.optionalPieces]
  | cons letter later =>
    have firstNegative : classify letter = false := negative letter List.mem_cons_self
    have uniform : ∀ value ∈ later, classify value = classify letter := by
      intro value member
      exact (negative value (List.mem_cons_of_mem letter member)).trans firstNegative.symm
    have boundary : SeparatedHead classify letter
        (decompose classify (first.toList ++ after)) := by
      cases shape : decompose classify (first.toList ++ after) with
      | nil => trivial
      | cons leading remaining =>
        have equalHead : leading.head = first.head :=
          decompose_first_head classify first.head (first.tail ++ after) leading remaining shape
        have leadingPositive : classify leading.head = true :=
          (congrArg classify equalHead).trans firstPositive
        intro equal
        have impossible : (false : Bool) = true :=
          firstNegative.symm.trans (equal.trans leadingPositive)
        cases impossible
    have packed : decompose classify ((letter :: later) ++ (first.toList ++ after)) =
        (⟨letter, later⟩ : Word Nat) :: decompose classify (first.toList ++ after) := by
      rw [decompose_append]
      exact foldr_run classify letter later (decompose classify (first.toList ++ after))
        uniform boundary
    calc
      NegativeParts classify (decompose classify ((letter :: later) ++ (first.toList ++ after))) =
          NegativeParts classify ((⟨letter, later⟩ : Word Nat) ::
            decompose classify (first.toList ++ after)) := congrArg (NegativeParts classify) packed
      _ = (⟨letter, later⟩ : Word Nat) ::
          NegativeParts classify (decompose classify (first.toList ++ after)) :=
        negative_parts_negative_cons classify (⟨letter, later⟩ : Word Nat)
          (decompose classify (first.toList ++ after)) firstNegative
      _ = MaximalSquareCover.optionalPieces (letter :: later) ++
          NegativeParts classify (decompose classify (first.toList ++ after)) := rfl

/-- Different positive square words may merge across empty gaps. Their
negative projection nevertheless retains each whole nonempty gap exactly. -/
theorem framed_gap_projection (classify : Nat → Bool) (chunks : List Chunk) :
    ∀ first : Word Nat,
      (∀ value ∈ first.toList, classify value = true) →
      (∀ entry ∈ chunks, ∀ value ∈ entry.2.toList, classify value = true) →
      (∀ entry ∈ chunks, ∀ value ∈ flatten entry.1, classify value = false) →
      NegativeParts classify (decompose classify (first.toList ++ render chunks)) =
        gapProjection chunks := by
  induction chunks with
  | nil =>
    intro first firstPositive _squaresPositive _gapsNegative
    exact negative_decompose_positive_prefix classify first.toList [] firstPositive
  | cons entry rest ih =>
    rcases entry with ⟨gap, square⟩
    intro first firstPositive squaresPositive gapsNegative
    have squarePositive : ∀ value ∈ square.toList, classify value = true :=
      squaresPositive (gap, square) List.mem_cons_self
    have gapNegative : ∀ value ∈ flatten gap, classify value = false :=
      gapsNegative (gap, square) List.mem_cons_self
    have restSquares : ∀ entry ∈ rest, ∀ value ∈ entry.2.toList, classify value = true := by
      intro entry member value inside
      exact squaresPositive entry (List.mem_cons_of_mem (gap, square) member) value inside
    have restGaps : ∀ entry ∈ rest, ∀ value ∈ flatten entry.1, classify value = false := by
      intro entry member value inside
      exact gapsNegative entry (List.mem_cons_of_mem (gap, square) member) value inside
    calc
      NegativeParts classify (decompose classify
          (first.toList ++ render ((gap, square) :: rest))) =
          NegativeParts classify (decompose classify (render ((gap, square) :: rest))) :=
        negative_decompose_positive_prefix classify first.toList
          (render ((gap, square) :: rest)) firstPositive
      _ = MaximalSquareCover.optionalPieces (flatten gap) ++
          NegativeParts classify (decompose classify (square.toList ++ render rest)) :=
        negative_decompose_gap_before_positive classify (flatten gap) square (render rest)
          gapNegative (squarePositive square.head (word_head_member square))
      _ = MaximalSquareCover.optionalPieces (flatten gap) ++ gapProjection rest :=
        congrArg (fun words => MaximalSquareCover.optionalPieces (flatten gap) ++ words)
          (ih square squarePositive restSquares restGaps)
      _ = gapProjection ((gap, square) :: rest) := rfl

theorem root_square_positive (word : Word Nat) (roots : List (Word Nat)) (piece : Word Nat)
    (coverage : ∀ value, RootFamily.Covered roots value ↔ 2 ≤ word.toList.count value)
    (square : RootSquare roots piece) :
    ∀ value ∈ piece.toList, repeatedTag word value = true := by
  obtain ⟨root, member, equal⟩ := square
  rw [equal]
  exact square_all_positive (repeatedTag word) roots (matches_repeated roots word coverage) root member

/-- Ordered gap reification WITHIN an actual canonical Form; this is not
an assertion that semantically equal forms have the same gap order. -/
theorem form_gap_words (word : Word Nat) (form : Form word) :
    simpleFactors word = gapProjection form.chunks := by
  have firstPositive : ∀ value ∈ form.first.toList, repeatedTag word value = true :=
    root_square_positive word form.roots form.first form.coverage form.first_square
  have squarePositive : ∀ entry ∈ form.chunks, ∀ value ∈ entry.2.toList,
      repeatedTag word value = true := by
    intro entry member
    exact root_square_positive word form.roots entry.2 form.coverage (form.chunk_good entry member).2
  have gapNegative : ∀ entry ∈ form.chunks, ∀ value ∈ flatten entry.1,
      repeatedTag word value = false := by
    intro entry member value inside
    exact repeated_false_of_once word value (form.gaps_simple entry member value inside)
  calc
    simpleFactors word = NegativeParts (repeatedTag word)
        (decompose (repeatedTag word) word.toList) :=
      (negative_parts_decompose (repeatedTag word) word).symm
    _ = NegativeParts (repeatedTag word)
        (decompose (repeatedTag word) (form.first.toList ++ render form.chunks)) :=
      congrArg (fun letters => NegativeParts (repeatedTag word) (decompose (repeatedTag word) letters))
        form.literal
    _ = gapProjection form.chunks := framed_gap_projection (repeatedTag word) form.chunks
      form.first firstPositive squarePositive gapNegative

theorem optional_gap_mem_iff (letters : List Nat) (piece : Word Nat) :
    piece ∈ MaximalSquareCover.optionalPieces letters ↔ letters = piece.toList := by
  cases letters with
  | nil =>
    constructor
    · intro member
      cases member
    · intro equal
      exact False.elim (piece_nonempty piece equal.symm)
  | cons first later =>
    change piece ∈ [(⟨first, later⟩ : Word Nat)] ↔ first :: later = piece.toList
    constructor
    · intro member
      have equal : piece = (⟨first, later⟩ : Word Nat) := List.mem_singleton.mp member
      exact (congrArg Word.toList equal).symm
    · intro equal
      apply List.mem_singleton.mpr
      cases piece with
      | mk head tail =>
        rcases List.cons.inj equal with ⟨headEqual, tailEqual⟩
        cases headEqual
        cases tailEqual
        rfl

theorem gapProjection_mem_iff (chunks : List Chunk) (piece : Word Nat) :
    piece ∈ gapProjection chunks ↔ ∃ entry ∈ chunks, flatten entry.1 = piece.toList := by
  induction chunks with
  | nil =>
    constructor
    · intro member
      cases member
    · rintro ⟨entry, member, _equal⟩
      cases member
  | cons entry rest ih =>
    constructor
    · intro member
      change piece ∈ MaximalSquareCover.optionalPieces (flatten entry.1) ++ gapProjection rest at member
      rcases List.mem_append.mp member with first | later
      · exact ⟨entry, List.mem_cons_self, (optional_gap_mem_iff (flatten entry.1) piece).mp first⟩
      · obtain ⟨other, inside, equal⟩ := ih.mp later
        exact ⟨other, List.mem_cons_of_mem entry inside, equal⟩
    · rintro ⟨other, member, equal⟩
      change piece ∈ MaximalSquareCover.optionalPieces (flatten entry.1) ++ gapProjection rest
      rcases List.mem_cons.mp member with same | later
      · subst other
        exact List.mem_append.mpr (Or.inl ((optional_gap_mem_iff (flatten entry.1) piece).mpr equal))
      · exact List.mem_append.mpr (Or.inr (ih.mpr ⟨other, later, equal⟩))

theorem form_nonempty_gap_iff (word : Word Nat) (form : Form word) (piece : Word Nat) :
    piece ∈ simpleFactors word ↔ ∃ entry ∈ form.chunks, flatten entry.1 = piece.toList := by
  rw [form_gap_words word form]
  exact gapProjection_mem_iff form.chunks piece

theorem form_gap_word_set_transfer (source target : Word Nat)
    (left : Form source) (right : Form target)
    (sameSimple : SameSimple source.toList target.toList)
    (sameEdges : SameEdges source.toList target.toList) (piece : Word Nat) :
    (∃ entry ∈ left.chunks, flatten entry.1 = piece.toList) ↔
      ∃ entry ∈ right.chunks, flatten entry.1 = piece.toList :=
  (form_nonempty_gap_iff source left piece).symm.trans
    ((simpleFactors_set_transfer source target sameSimple sameEdges piece).trans
      (form_nonempty_gap_iff target right piece))

/-- Nonempty canonical gap SET membership transfers from the exact
simple-letter and literal-edge data; the empty list is explicitly excluded. -/
theorem nonempty_gap_set_transfer (source target : Word Nat)
    (left : Form source) (right : Form target)
    (sameSimple : SameSimple source.toList target.toList)
    (sameEdges : SameEdges source.toList target.toList) (gap : List Nat) (nonempty : gap ≠ []) :
    (∃ entry ∈ left.chunks, flatten entry.1 = gap) ↔
      ∃ entry ∈ right.chunks, flatten entry.1 = gap := by
  cases gap with
  | nil => exact False.elim (nonempty rfl)
  | cons first later =>
    exact form_gap_word_set_transfer source target left right sameSimple sameEdges (⟨first, later⟩ : Word Nat)

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalGapProjection

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalGapProjection.negative_insert_positive
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalGapProjection.negative_decompose_positive_prefix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalGapProjection.negative_decompose_gap_before_positive
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalGapProjection.framed_gap_projection
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalGapProjection.form_gap_words
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalGapProjection.gapProjection_mem_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalGapProjection.form_nonempty_gap_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalGapProjection.nonempty_gap_set_transfer

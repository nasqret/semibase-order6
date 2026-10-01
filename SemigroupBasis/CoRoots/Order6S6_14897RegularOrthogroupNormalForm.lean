import SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupListSyntax
import SemigroupBasis.CoRoots.S5_1092Normalization
import SemigroupBasis.Examples.AffineParityFour
import SemigroupBasis.Examples.CyclicTwo

namespace SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup

open SemigroupBasis
open SemigroupBasis.Examples

/-- The marker sequence extracted by the affine right-to-left scan. -/
def affineBarrierSequence (letters : List Nat) : List Nat :=
  affineParityMarkers (affineParityNormalSegments letters)

theorem mem_lastOccurrenceSequence_iff
    (selected : Nat) :
    forall letters : List Nat,
      Iff
        (selected ∈
          SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence letters)
        (selected ∈ letters)
  | [] => by
      simp [SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence]
  | letter :: rest => by
      have induction := mem_lastOccurrenceSequence_iff selected rest
      by_cases present : letter ∈ rest
      · by_cases equal : selected = letter
        · subst selected
          simp [SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence,
            present, induction]
        · simp [SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence,
            present, equal, induction]
      · by_cases equal : selected = letter
        · subst selected
          simp [SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence,
            present, induction]
        · simp [SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence,
            present, equal, induction]

/-- Affine markers are precisely last occurrences, in their source order. -/
theorem affineBarrierSequence_eq_lastOccurrenceSequence :
    forall letters : List Nat,
      affineBarrierSequence letters =
        SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence letters
  | [] => rfl
  | [letter] => rfl
  | letter :: next :: rest => by
      have induction :=
        affineBarrierSequence_eq_lastOccurrenceSequence
          (next :: rest)
      cases segmentsEq :
          affineParityNormalSegments (next :: rest) with
      | nil =>
          exact False.elim <|
            affineParityNormalSegments_cons_ne_nil
              next rest segmentsEq
      | cons segment segments =>
          have markerEq :
              affineParityMarkers (segment :: segments) =
                SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence
                  (next :: rest) := by
            simpa [affineBarrierSequence, segmentsEq] using induction
          have markerEqExpanded :
              segment.marker :: affineParityMarkers segments =
                SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence
                  (next :: rest) := by
            simpa only [affineParityMarkers] using markerEq
          by_cases present :
              letter ∈ affineParityMarkers (segment :: segments)
          · have presentInRest : letter ∈ next :: rest := by
              apply
                (mem_lastOccurrenceSequence_iff
                  letter (next :: rest)).mp
              simpa [markerEq] using present
            rw [affineBarrierSequence, affineParityNormalSegments, segmentsEq]
            simp only [if_pos present]
            simp only [affineParityMarkers]
            rw [markerEqExpanded]
            simp [SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence,
              presentInRest]
          · have absentInRest : letter ∉ next :: rest := by
              intro member
              apply present
              rw [markerEq]
              exact
                (mem_lastOccurrenceSequence_iff
                  letter (next :: rest)).mpr member
            rw [affineBarrierSequence, affineParityNormalSegments, segmentsEq]
            simp only [if_neg present]
            simp only [affineParityMarkers]
            rw [markerEqExpanded]
            simp [SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence,
              absentInRest]

theorem mem_affineBarrierSequence_iff
    (selected : Nat) (letters : List Nat) :
    Iff (selected ∈ affineBarrierSequence letters)
      (selected ∈ letters) := by
  rw [affineBarrierSequence_eq_lastOccurrenceSequence]
  exact mem_lastOccurrenceSequence_iff selected letters

/-- Duplicate-free representative of the total parity vector. -/
def oddParitySupport (letters : List Nat) : List Nat :=
  parityReduce letters

/-- The complete right-to-left affine segment normal form. Unlike the marker
sequence alone, this retains the parity block attached to every barrier. -/
def affineNormalList (letters : List Nat) : List Nat :=
  affineParityRender (affineParityNormalSegments letters)

theorem mem_affineNormalList_of_mem
    {selected : Nat} {letters : List Nat}
    (member : selected ∈ letters) :
    selected ∈ affineNormalList letters := by
  apply affineParityMarker_mem_render
  change selected ∈ affineBarrierSequence letters
  exact (mem_affineBarrierSequence_iff selected letters).mpr member

theorem mem_affineNormalList_iff
    (selected : Nat) (letters : List Nat) :
    Iff (selected ∈ affineNormalList letters)
      (selected ∈ letters) := by
  constructor
  · intro member
    have normal :=
      affineParityNormalSegments_normal letters
    have markerMember :
        selected ∈
          affineParityMarkers
            (affineParityNormalSegments letters) :=
      (normal.mem_render_iff_marker selected).mp member
    apply (mem_affineBarrierSequence_iff selected letters).mp
    simpa [affineBarrierSequence] using markerMember
  · exact fun member => mem_affineNormalList_of_mem member

/-- The dual affine normal form, obtained by scanning from left to right. -/
def reverseAffineNormalList (letters : List Nat) : List Nat :=
  (affineNormalList letters.reverse).reverse

theorem mem_reverseAffineNormalList_of_mem
    {selected : Nat} {letters : List Nat}
    (member : selected ∈ letters) :
    selected ∈ reverseAffineNormalList letters := by
  have reversedMember : selected ∈ letters.reverse := by
    simpa using member
  have normalMember :=
    mem_affineNormalList_of_mem reversedMember
  simpa [reverseAffineNormalList] using normalMember

theorem mem_reverseAffineNormalList_iff
    (selected : Nat) (letters : List Nat) :
    Iff (selected ∈ reverseAffineNormalList letters)
      (selected ∈ letters) := by
  simpa only [reverseAffineNormalList, List.mem_reverse,
    mem_affineNormalList_iff]

/-- Complete bidirectional affine normal form: the reversed affine profile,
the total odd support, and the forward affine profile. The two affine blocks,
not merely their marker sequences, are required for completeness. -/
def regularOrthogroupNormalList (letters : List Nat) : List Nat :=
  reverseAffineNormalList letters ++
    oddParitySupport letters ++ affineNormalList letters

theorem regularOrthogroupNormalList_eq_affine_blocks
    (letters : List Nat) :
    regularOrthogroupNormalList letters =
      reverseAffineNormalList letters ++
        parityReduce letters ++ affineNormalList letters :=
  rfl

end SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup

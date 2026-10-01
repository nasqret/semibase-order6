import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006BlockSpine

/-!
# Rank006: the lower canonical skeleton of an arbitrary square

A square cannot have an exact separator cut: its multiplicities are even,
whereas such a cut requires a globally unique occurrence. The independent
S4_69 normalizer therefore has exactly one separator-free block. Its labels
are sorted, distinct and have precisely the root's support. The derivation
to doubles below lives ONLY in the seven-law lower calculus, never Sigma+.
-/

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SquareSkeleton

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006PeriodMacros
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Semantics

theorem square_normal_segments (root : Word Nat) :
    ∃ quadratic : List Nat,
      uniqueSeparatorFourNormalSegments (square root) = [⟨quadratic, none⟩] := by
  have canonical := uniqueSeparatorFourNormalSegments_canonical (square root)
  have normalList := separatorNormalWord_toList (square root)
  have normalSound := (separatorDerivesNormalWord (square root)).sound
    uniqueSeparatorFourBasis_models
  cases segments : uniqueSeparatorFourNormalSegments (square root) with
  | nil =>
      have impossible : (separatorNormalWord (square root)).toList = [] := by
        simpa only [uniqueSeparatorFourNormalRender, segments,
          uniqueSeparatorCanonicalRender, List.flatMap_nil] using normalList
      cases separatorNormalWord (square root) with
      | mk head tail => simp [Word.toList] at impossible
  | cons segment rest =>
      rw [segments] at canonical
      have noSeparator : segment.separator = none := by
        cases candidate : segment.separator with
        | none => rfl
        | some separator =>
            have cut := uniqueSeparatorCanonical_firstExactCut canonical candidate
            have wordCut : UniqueSeparatorFourExactCut
                (separatorNormalWord (square root)).toList
                (uniqueSeparatorCanonicalRenderDoubles segment.quadratic)
                separator (uniqueSeparatorCanonicalRender rest) := by
              simpa only [normalList, uniqueSeparatorFourNormalRender, segments] using cut
            obtain ⟨leftPart, rightPart, transported, _, _⟩ :=
              uniqueSeparatorFourEqualEval_transportExactCut
                (separatorNormalWord (square root)) (square root)
                (fun valuation => (normalSound valuation).symm) wordCut
            have countOne := transported.2.1
            simp only [square, Word.toList_append, List.count_append] at countOne
            omega
      have terminal : rest = [] := canonical.2.2.1 [] segment rest rfl noSeparator
      subst rest
      refine ⟨segment.quadratic, ?_⟩
      cases segment with
      | mk quadratic separator =>
          simp only at noSeparator
          subst separator
          rfl

noncomputable def squareQuadratic (root : Word Nat) : List Nat :=
  Classical.choose (square_normal_segments root)

theorem square_normal_segments_eq (root : Word Nat) :
    uniqueSeparatorFourNormalSegments (square root) = [⟨squareQuadratic root, none⟩] :=
  Classical.choose_spec (square_normal_segments root)

theorem square_quadratic_canonical (root : Word Nat) :
    UniqueSeparatorCanonical [⟨squareQuadratic root, none⟩] := by
  rw [← square_normal_segments_eq]
  exact uniqueSeparatorFourNormalSegments_canonical (square root)

theorem square_quadratic_ne_nil (root : Word Nat) : squareQuadratic root ≠ [] := by
  intro empty
  have nonempty := (square_quadratic_canonical root).2.2.2
    ⟨squareQuadratic root, none⟩ (by simp) empty
  simp at nonempty

theorem square_quadratic_nodup (root : Word Nat) : (squareQuadratic root).Nodup := by
  simpa [uniqueSeparatorCanonicalLabels, UniqueSeparatorCanonicalSegment.labels] using
    (square_quadratic_canonical root).1

theorem square_quadratic_sorted (root : Word Nat) :
    (squareQuadratic root).Pairwise (· ≤ ·) :=
  (square_quadratic_canonical root).2.1 ⟨squareQuadratic root, none⟩ (by simp)

theorem square_quadratic_support (root : Word Nat) (letter : Nat) :
    letter ∈ squareQuadratic root ↔ letter ∈ root.toList := by
  have supported := uniqueSeparatorFourEqualEval_support_iff
    (square root) (separatorNormalWord (square root))
    ((separatorDerivesNormalWord (square root)).sound uniqueSeparatorFourBasis_models) letter
  rw [separatorNormalWord_toList] at supported
  simp only [uniqueSeparatorFourNormalRender, square_normal_segments_eq] at supported
  simpa only [square, Word.toList_append, List.mem_append, or_self,
    uniqueSeparatorCanonicalRender, List.flatMap_cons, List.flatMap_nil,
    UniqueSeparatorCanonicalSegment.render, Option.toList_none,
    List.append_nil, uniqueSeparatorCanonicalRenderDoubles_mem_iff] using supported.symm

/-- This is a LOWER derivation; using it directly at Sigma+ would be unsound. -/
theorem square_derives_quadratic_lower (root : Word Nat) :
    UniqueSeparatorListDerives (square root).toList
      (uniqueSeparatorCanonicalRenderDoubles (squareQuadratic root)) := by
  simpa only [uniqueSeparatorFourNormalRender, square_normal_segments_eq,
    uniqueSeparatorCanonicalRender, List.flatMap_cons, List.flatMap_nil,
    UniqueSeparatorCanonicalSegment.render, Option.toList_none, List.append_nil] using
    uniqueSeparatorFour_derivesNormal (square root)

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SquareSkeleton

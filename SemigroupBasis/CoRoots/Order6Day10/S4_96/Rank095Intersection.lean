import SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095BufferParity
import SemigroupBasis.Subdirect

/-! Unrestricted exact B5 completeness for S4_96 direct / S5_506 direct.
Affine normalization is used only in its own complete calculus. The displayed
B5 normalization retains every removed pair in an explicit square buffer.
After the affine renderers are aligned, actual mod-four semantics identifies
the parity of those buffers. No semigroup cancellation or bounded descriptor
test is used as a proof, and no additional displayed law is assumed. -/

namespace SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095Intersection

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095Macros
open SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095BufferNormal
open SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095BufferParity

abbrev basis := Rank095Macros.basis
abbrev leftTable := Rank095Macros.leftTable
abbrev rightTable := Rank095Macros.rightTable

theorem affineNormal_eval (word : Word Nat) (valuation : Nat → Fin 4) :
    affineParityListEval valuation (affineParityRender (affineParityNormalSegments word.toList)) =
      leftTable.semigroup.eval valuation word := by
  have normalized := affineParityDerivesNormal word
  cases shape : affineParityNormalSegments word.toList with
  | nil =>
      have empty := (normalSegments_eq_nil_iff word.toList).mp shape
      cases word with
      | mk head tail => simp [Word.toList] at empty
  | cons segment rest =>
      rw [shape] at normalized
      have evaluated := normalized.sound affineParityFourBasis_models valuation
      change affineParityListEval valuation
          (affineParityRender (segment :: rest)) =
        affineParityFour.semigroup.eval valuation word
      simpa [affineParityEval_eq_listEval, affineParityRenderWord_toList] using evaluated.symm

theorem affineSegmentsPerm_of_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    AffineParitySegmentsPerm (affineParityNormalSegments identity.lhs.toList)
      (affineParityNormalSegments identity.rhs.toList) := by
  have leftNormal := affineParityNormalSegments_normal identity.lhs.toList
  have rightNormal := affineParityNormalSegments_normal identity.rhs.toList
  have equalEval : ∀ valuation : Nat → Fin 4,
      affineParityListEval valuation (affineParityRender (affineParityNormalSegments identity.lhs.toList)) =
        affineParityListEval valuation (affineParityRender (affineParityNormalSegments identity.rhs.toList)) := by
    intro valuation
    exact (affineNormal_eval identity.lhs valuation).trans
      ((valid valuation).trans (affineNormal_eval identity.rhs valuation).symm)
  apply affineParitySegmentsPerm_of_invariants leftNormal rightNormal
    (affineParityMarkers_eq_of_eval_eq leftNormal rightNormal equalEval)
  · intro tested
    have bits := congrArg affineParityTranslationBit (equalEval (affineParityTotalValuation tested))
    simpa [affineParityListEval_total_bit] using bits
  · intro tested marker _
    have bits := congrArg affineParityTranslationBit (equalEval (affineParitySuffixValuation tested marker))
    simpa [affineParityListEval_suffix_bit] using bits

def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup →
    identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem complete : Complete := by
  intro identity leftValid rightValid
  obtain ⟨leftBuffer, leftDerived, leftGuard⟩ := bufferedNormal identity.lhs.toList
  obtain ⟨rightBuffer, rightDerived, rightGuard⟩ := bufferedNormal identity.rhs.toList
  have leftNormal := affineParityNormalSegments_normal identity.lhs.toList
  have rightNormal := affineParityNormalSegments_normal identity.rhs.toList
  have permutation := affineSegmentsPerm_of_valid identity leftValid
  have sameMarkers := segmentPermutation_markers permutation
  have renderDerived := segmentPermutationDerives permutation leftNormal rightNormal
  have aligned : D identity.lhs.toList
      (doubleLetters leftBuffer ++ affineParityRender (affineParityNormalSegments identity.rhs.toList)) :=
    leftDerived.trans (renderDerived.prepend (doubleLetters leftBuffer))
  have leftAlignedGuard : ∀ x, x ∈ leftBuffer →
      x ∈ affineParityRender (affineParityNormalSegments identity.rhs.toList) := by
    intro x member
    apply affineParityMarker_mem_render
    rw [← sameMarkers]
    exact leftGuard x member
  have rightRenderGuard : ∀ x, x ∈ rightBuffer →
      x ∈ affineParityRender (affineParityNormalSegments identity.rhs.toList) := by
    intro x member
    exact affineParityMarker_mem_render (rightGuard x member)
  have factorCounts := CoRoots.S5_505Family.S5_506.valid_count_mod_four identity rightValid
  have leftCounts := derives_count_mod_four aligned
  have rightCounts := derives_count_mod_four rightDerived
  have sameCounts : ∀ x,
      (doubleLetters leftBuffer ++ affineParityRender (affineParityNormalSegments identity.rhs.toList)).count x % 4 =
        (doubleLetters rightBuffer ++ affineParityRender (affineParityNormalSegments identity.rhs.toList)).count x % 4 := by
    intro x
    exact (leftCounts x).symm.trans ((factorCounts x).trans (rightCounts x))
  have sameParity := bufferParity_of_modFour leftBuffer rightBuffer
    (affineParityRender (affineParityNormalSegments identity.rhs.toList)) sameCounts
  have bufferDerived := buffersOfSameParity leftBuffer rightBuffer
    (affineParityRender (affineParityNormalSegments identity.rhs.toList))
    leftAlignedGuard rightRenderGuard sameParity
  exact listDerives_to_word (aligned.trans (bufferDerived.trans rightDerived.symm))

theorem derives_iff_joint_valid (identity : Identity Nat) :
    Derives basis identity.lhs identity.rhs ↔
      identity.SatisfiedBy leftTable.semigroup ∧ identity.SatisfiedBy rightTable.semigroup := by
  constructor
  · intro derivation
    exact ⟨fun valuation => derivation.sound modelsLeft valuation,
      fun valuation => derivation.sound modelsRight valuation⟩
  · intro valid
    exact complete identity valid.1 valid.2

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := complete

abbrev FinitePair (target : FiniteTable) :=
  SubdirectPair target.semigroup leftTable.semigroup rightTable.semigroup

theorem basisForOfFinitePair (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup basis := intersectionBasis.basisFor pair

theorem basisForOppositeOfFinitePair (target : FiniteTable)
    (pair : SubdirectPair target.semigroup.opposite leftTable.semigroup.opposite rightTable.semigroup.opposite) :
    BasisFor target.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor pair

end SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095Intersection

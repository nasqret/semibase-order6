import SemigroupBasis.CoRoots.S5_415PairedInduction

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-- The sole remaining global word-problem obligation: every pair of words
with the exact Brandt endpoint-connectivity signature is derivable from
Trahtman's three laws. This proposition is deliberately a definition, not an
axiom. -/
def BrandtDerivationalCompleteness : Prop :=
  ∀ left right : Word Nat,
    SameBrandtSignature left right →
      Derives basis left right

/-- Exact paired normal-form obligation.  The hypothesis concerns both words;
in particular it does not claim that an incoming pivot path in one word can
retarget that word's literal head. -/
def PairedNormalizedDecompositionCompleteness : Type :=
  ∀ left right : Word Nat,
    SameBrandtSignature left right →
      PairedBrandtDecomposition
        (normalizeBrandtWord left) (normalizeBrandtWord right)

/-- It suffices to solve the Brandt signature problem on the outputs of the
total recursive normalizer. -/
theorem derivationalCompleteness_of_normalizedBridge
    (bridge :
      ∀ left right : Word Nat,
        SameBrandtSignature left right →
          Derives basis (normalizeBrandtWord left)
            (normalizeBrandtWord right)) :
    BrandtDerivationalCompleteness := by
  intro left right same
  exact (derivesNormalizeBrandtWord left).trans <|
    (bridge left right same).trans
      (derivesNormalizeBrandtWord right).symm

/-- Conversely, a complete derivational solution supplies the normalized
bridge, so this is an exact restriction of the remaining search domain. -/
theorem normalizedBridge_of_derivationalCompleteness
    (complete : BrandtDerivationalCompleteness) :
    ∀ left right : Word Nat,
      SameBrandtSignature left right →
        Derives basis (normalizeBrandtWord left)
          (normalizeBrandtWord right) := by
  intro left right same
  exact (derivesNormalizeBrandtWord left).symm.trans <|
    (complete left right same).trans
      (derivesNormalizeBrandtWord right)

/-- The remaining global obligation is exactly the Brandt signature bridge on
the outputs of `normalizeBrandtWord`; normalization itself is now internal to
the derivation system. -/
theorem derivationalCompleteness_iff_normalizedBridge :
    BrandtDerivationalCompleteness ↔
      (∀ left right : Word Nat,
        SameBrandtSignature left right →
          Derives basis (normalizeBrandtWord left)
            (normalizeBrandtWord right)) :=
  ⟨normalizedBridge_of_derivationalCompleteness,
    derivationalCompleteness_of_normalizedBridge⟩

/-- Constructing the paired decomposition closes the normalized bridge via
`derivesOfRetargetedCommonAnchor`. -/
theorem derivationalCompleteness_of_pairedNormalizedDecomposition
    (pairedComplete : PairedNormalizedDecompositionCompleteness) :
    BrandtDerivationalCompleteness :=
  derivationalCompleteness_of_normalizedBridge <| by
    intro left right same
    exact (pairedComplete left right same).derives

/-- Conversely, full derivational completeness can choose the normalized
left word itself as the right-hand retarget.  Thus the paired decomposition
is an exact residual proposition, not an additional assumption. -/
def pairedNormalizedDecomposition_of_derivationalCompleteness
    (complete : BrandtDerivationalCompleteness) :
    PairedNormalizedDecompositionCompleteness := by
  intro left right same
  have normalizedSame := normalizedWords_sameBrandtSignature same
  have reverseSame :
      SameBrandtSignature
        (normalizeBrandtWord right) (normalizeBrandtWord left) := by
    apply valid_sameBrandtSignature
      (identity := Identity.mk
        (normalizeBrandtWord right) (normalizeBrandtWord left))
    intro valuation
    exact
      (valid_of_sameBrandtSignature
        (identity := Identity.mk
          (normalizeBrandtWord left) (normalizeBrandtWord right))
        normalizedSame valuation).symm
  exact
    { retargeted := normalizeBrandtWord left
      rightRetarget := complete
        (normalizeBrandtWord right) (normalizeBrandtWord left)
        reverseSame
      commonHead := rfl
      gaps := optionalGapDerivesForall₂_refl _
      trailing := TrailingLettersDerives.refl _ }

theorem derivationalCompleteness_iff_pairedNormalizedDecomposition :
    BrandtDerivationalCompleteness ↔
      Nonempty PairedNormalizedDecompositionCompleteness :=
  ⟨fun complete =>
      ⟨pairedNormalizedDecomposition_of_derivationalCompleteness complete⟩,
    fun paired =>
      paired.elim derivationalCompleteness_of_pairedNormalizedDecomposition⟩

/-- The corrected semantic-retarget route closes the global derivational
obligation by strong support induction.  Its certificate always contains an
actual right-word derivative, including when the two literal heads already
agree. -/
theorem derivationalCompleteness_of_pairedSemanticRetarget
    (complete : PairedSemanticRetargetCompleteness) :
    BrandtDerivationalCompleteness := by
  intro left right same
  exact derives_of_pairedSemanticRetargetCompleteness complete same

def pairedNormalizedDecomposition_of_pairedSemanticRetarget
    (complete : PairedSemanticRetargetCompleteness) :
    PairedNormalizedDecompositionCompleteness :=
  pairedNormalizedDecomposition_of_derivationalCompleteness
    (derivationalCompleteness_of_pairedSemanticRetarget complete)

/-- `BasisFor` is exactly the explicit endpoint-connectivity derivational
obligation once the unconditional table semantics and finite law checks are
installed. -/
theorem basisFor_iff_derivationalCompleteness :
    BasisFor Generated.Catalogue.S5_415.table.semigroup basis ↔
      BrandtDerivationalCompleteness := by
  constructor
  · intro complete left right same
    exact complete.2 ⟨left, right⟩
      ((satisfiedBy_iff_sameBrandtSignature ⟨left, right⟩).mpr same)
  · intro derivesAll
    refine ⟨catalogueModels, ?_⟩
    intro identity valid
    exact derivesAll identity.lhs identity.rhs
      ((satisfiedBy_iff_sameBrandtSignature identity).mp valid)

theorem basisFor_iff_pairedNormalizedDecomposition :
    BasisFor Generated.Catalogue.S5_415.table.semigroup basis ↔
      Nonempty PairedNormalizedDecompositionCompleteness :=
  basisFor_iff_derivationalCompleteness.trans
    derivationalCompleteness_iff_pairedNormalizedDecomposition

theorem basis_complete_of_derivationalCompleteness
    (complete : BrandtDerivationalCompleteness) :
    BasisFor Generated.Catalogue.S5_415.table.semigroup basis :=
  basisFor_iff_derivationalCompleteness.mpr complete

theorem opposite_basis_complete_of_derivationalCompleteness
    (complete : BrandtDerivationalCompleteness) :
    BasisFor Generated.Catalogue.S5_415.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using
    (basis_complete_of_derivationalCompleteness complete).oppositeReversed

/-- Conditional representative endpoint with a name that cannot be mistaken
for a completed kernel theorem. -/
theorem representative_basis_of_derivationalCompleteness
    (complete : BrandtDerivationalCompleteness) :
    BasisFor Generated.Catalogue.S5_415.table.semigroup basis :=
  basis_complete_of_derivationalCompleteness complete

/-- Conditional opposite endpoint with the literal reverse-word basis. -/
theorem opposite_basis_of_derivationalCompleteness
    (complete : BrandtDerivationalCompleteness) :
    BasisFor Generated.Catalogue.S5_415.table.semigroup.opposite
      (reversedBasis basis) := by
  simpa [oppositeBasis] using
    opposite_basis_complete_of_derivationalCompleteness complete

end SemigroupBasis.CoRoots.S5_415

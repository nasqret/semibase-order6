import SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4Normalization
import SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4Semantics
import SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4Uniqueness

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4

open SemigroupBasis

/-!
# Lee--Zhang Proposition 20.7 / E4: completeness assembly

The all-simple branch is reconstructed directly from support, first letter,
and `FSS`.  In the non-simple branch, both words pass through the public
`ReducedValid` normalizer.  The published E4 semantics supplies exactly the
four invariants of Lemma 20.8 for the normalized identity, and reduced
canonical uniqueness makes the two target words literally equal.
-/

/-- Every identity of the exact published table E4 follows from the frozen
64-member expansion of (20.6a)--(20.6f). -/
theorem publishedDerives
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have originalInvariant := publishedValidInvariant identity valid
  by_cases leftNonSimple :
      ∃ letter, NonSimple identity.lhs.toList letter
  · obtain ⟨multiple, leftMultiple⟩ := leftNonSimple
    have rightMultiple :
        NonSimple identity.rhs.toList multiple :=
      (originalInvariant.nonSimple multiple).mp leftMultiple
    obtain ⟨leftTarget, leftForm, leftReduced,
        leftRender, leftReduction⟩ :=
      existsCanonicalWordReduction identity.lhs leftMultiple
    obtain ⟨rightTarget, rightForm, rightReduced,
        rightRender, rightReduction⟩ :=
      existsCanonicalWordReduction identity.rhs rightMultiple
    let normalizedIdentity : Identity Nat :=
      ⟨leftTarget, rightTarget⟩
    have normalizedValid :
        normalizedIdentity.SatisfiedBy publishedTable.semigroup := by
      intro valuation
      have leftSound :=
        leftReduction.sound publishedModels valuation
      have rightSound :=
        rightReduction.sound publishedModels valuation
      exact leftSound.symm.trans ((valid valuation).trans rightSound)
    have normalizedInvariant :
        SameInvariant leftTarget.toList rightTarget.toList := by
      simpa [normalizedIdentity] using
        publishedValidInvariant normalizedIdentity normalizedValid
    have canonicalInvariant :
        SameInvariant (renderCanonical leftForm)
          (renderCanonical rightForm) := by
      rw [← leftRender, ← rightRender]
      exact normalizedInvariant
    have renderedEq :
        renderCanonical leftForm = renderCanonical rightForm :=
      renderCanonical_eq_of_sameInvariant
        leftReduced rightReduced canonicalInvariant
    have targetEq : leftTarget = rightTarget := by
      apply Word.toList_injective
      exact leftRender.trans (renderedEq.trans rightRender.symm)
    subst rightTarget
    exact leftReduction.trans rightReduction.symm
  · have leftSimple : AllSimple identity.lhs.toList := by
      intro letter member
      rcases simple_or_nonSimple_of_mem member with simple | multiple
      · exact simple
      · exact (leftNonSimple ⟨letter, multiple⟩).elim
    have rightSimple : AllSimple identity.rhs.toList := by
      intro letter member
      have leftMember :=
        (originalInvariant.support letter).mpr member
      exact
        (originalInvariant.simple letter).mp
          (leftSimple letter leftMember)
    have listsEq : identity.lhs.toList = identity.rhs.toList :=
      list_eq_of_allSimple_sameInvariant
        leftSimple rightSimple originalInvariant
    have wordsEq : identity.lhs = identity.rhs :=
      Word.toList_injective listsEq
    rw [wordsEq]
    exact Derives.refl _

/-- The direct Proposition 20.7 expansion is an unrestricted identity basis
for the exact published E4 table. -/
theorem publishedBasisFor : BasisFor publishedTable.semigroup basis :=
  ⟨publishedModels, publishedDerives⟩

end SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4

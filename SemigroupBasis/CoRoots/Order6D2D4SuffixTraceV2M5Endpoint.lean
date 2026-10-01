import SemigroupBasis.CoRoots.Order6D2D4SuffixTraceV2M4Bridge

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6D2D4SuffixTrace.V2

open SemigroupBasis
open SemigroupBasis.CoRoots
open SemigroupBasis.CoRoots.Order6D2D4SuffixTrace

/-! # Step-2 v2 M5: D2/D4 endpoint assembly -/

/-- The sealed `S5_610` carrier inside D2, with zero-based image
`[0, 1, 3, 4, 5]`. -/
def s5_610EmbeddingD2 :
    Embedding Generated.Catalogue.S5_610.table.semigroup d2G where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨1, by decide⟩
    else if value.val = 2 then ⟨3, by decide⟩
    else if value.val = 3 then ⟨4, by decide⟩
    else ⟨5, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The same sealed `S5_610` carrier inside D4. -/
def s5_610EmbeddingD4 :
    Embedding Generated.Catalogue.S5_610.table.semigroup d4G where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨1, by decide⟩
    else if value.val = 2 then ⟨3, by decide⟩
    else if value.val = 3 then ⟨4, by decide⟩
    else ⟨5, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private theorem cappedMultiplicity_eq_two_iff
    (word : Word Nat) (letter : Nat) :
    S5_107.cappedMultiplicity word letter = 2 ↔
      2 ≤ word.toList.count letter := by
  unfold S5_107.cappedMultiplicity
  simp only [Nat.min_def]
  split <;> omega

private theorem base_multiple
    {left right : Word Nat}
    (base :
      S5_381Invariant.SameSimpleSequenceLastGapInitialSignature left right)
    (letter : Nat) :
    2 ≤ left.toList.count letter ↔
      2 ≤ right.toList.count letter := by
  rw [← cappedMultiplicity_eq_two_iff left letter,
    ← cappedMultiplicity_eq_two_iff right letter,
    base.capped letter]

private theorem d2_base
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy d2G) :
    S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
      identity.lhs identity.rhs :=
  S5_381FamilyInvariant.S5_610.valid_sameSignature identity
    (s5_610EmbeddingD2.pullback_identity identity valid)

private theorem d4_base
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy d4G) :
    S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
      identity.lhs identity.rhs :=
  S5_381FamilyInvariant.S5_610.valid_sameSignature identity
    (s5_610EmbeddingD4.pullback_identity identity valid)

private theorem prepend_valid
    {S : Type} (G : Semigroup S)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G)
    (letter : Nat) :
    (Identity.mk (prependLetter letter identity.lhs)
      (prependLetter letter identity.rhs)).SatisfiedBy G := by
  intro valuation
  simp only [prependLetter, Semigroup.eval_append]
  exact congrArg
    (G.mul (G.eval valuation (Word.singleton letter)))
    (valid valuation)

private theorem d2_sameFSL_of_valid
    (identity : Identity Nat) (valid : identity.SatisfiedBy d2G) :
    SameFSL identity.lhs identity.rhs := by
  have base := d2_base identity valid
  intro x y
  constructor
  · intro leftFSL
    have leftXSimple : S5_107.SimpleIn identity.lhs x := leftFSL.1
    have leftYMultiple : 2 ≤ identity.lhs.toList.count y := leftFSL.2.1
    have rightXSimple : S5_107.SimpleIn identity.rhs x :=
      (base.simple x).mp leftXSimple
    have rightYMultiple : 2 ≤ identity.rhs.toList.count y :=
      (base_multiple base y).mp leftYMultiple
    have leftOne : d2G.eval (fslValuation x y) identity.lhs = 1 :=
      (d2_eval_eq_one_iff_fsl identity.lhs x y
        leftXSimple leftYMultiple).mpr leftFSL
    have rightOne : d2G.eval (fslValuation x y) identity.rhs = 1 := by
      calc
        d2G.eval (fslValuation x y) identity.rhs =
            d2G.eval (fslValuation x y) identity.lhs :=
          (valid (fslValuation x y)).symm
        _ = 1 := leftOne
    exact (d2_eval_eq_one_iff_fsl identity.rhs x y
      rightXSimple rightYMultiple).mp rightOne
  · intro rightFSL
    have rightXSimple : S5_107.SimpleIn identity.rhs x := rightFSL.1
    have rightYMultiple : 2 ≤ identity.rhs.toList.count y := rightFSL.2.1
    have leftXSimple : S5_107.SimpleIn identity.lhs x :=
      (base.simple x).mpr rightXSimple
    have leftYMultiple : 2 ≤ identity.lhs.toList.count y :=
      (base_multiple base y).mpr rightYMultiple
    have rightOne : d2G.eval (fslValuation x y) identity.rhs = 1 :=
      (d2_eval_eq_one_iff_fsl identity.rhs x y
        rightXSimple rightYMultiple).mpr rightFSL
    have leftOne : d2G.eval (fslValuation x y) identity.lhs = 1 := by
      calc
        d2G.eval (fslValuation x y) identity.lhs =
            d2G.eval (fslValuation x y) identity.rhs :=
          valid (fslValuation x y)
        _ = 1 := rightOne
    exact (d2_eval_eq_one_iff_fsl identity.lhs x y
      leftXSimple leftYMultiple).mp leftOne

private theorem d4_sameFSL_of_valid
    (identity : Identity Nat) (valid : identity.SatisfiedBy d4G) :
    SameFSL identity.lhs identity.rhs := by
  have base := d4_base identity valid
  intro x y
  constructor
  · intro leftFSL
    have leftXSimple : S5_107.SimpleIn identity.lhs x := leftFSL.1
    have leftYMultiple : 2 ≤ identity.lhs.toList.count y := leftFSL.2.1
    have rightXSimple : S5_107.SimpleIn identity.rhs x :=
      (base.simple x).mp leftXSimple
    have rightYMultiple : 2 ≤ identity.rhs.toList.count y :=
      (base_multiple base y).mp leftYMultiple
    have leftSomeY : SomeYAfterX identity.lhs x y := by
      rcases leftFSL with ⟨_, _, before, after, split, _⟩
      exact ⟨before, y :: after, by simpa using split, by simp⟩
    have leftNotLast :
        ¬ S5_793Invariant.MultipleLastBeforeSimple identity.lhs y x :=
      (someYAfterX_iff_not_multipleLastBeforeSimple identity.lhs x y
        leftXSimple leftYMultiple).mp leftSomeY
    have rightNotLast :
        ¬ S5_793Invariant.MultipleLastBeforeSimple identity.rhs y x := by
      intro rightLast
      exact leftNotLast ((base.lastGap y x).mpr rightLast)
    have rightSomeY : SomeYAfterX identity.rhs x y :=
      (someYAfterX_iff_not_multipleLastBeforeSimple identity.rhs x y
        rightXSimple rightYMultiple).mpr rightNotLast
    have leftOne : d4G.eval (fslValuation x y) identity.lhs = 1 :=
      (d4_eval_eq_one_iff_fsl identity.lhs x y
        leftXSimple leftYMultiple leftSomeY).mpr leftFSL
    have rightOne : d4G.eval (fslValuation x y) identity.rhs = 1 := by
      calc
        d4G.eval (fslValuation x y) identity.rhs =
            d4G.eval (fslValuation x y) identity.lhs :=
          (valid (fslValuation x y)).symm
        _ = 1 := leftOne
    exact (d4_eval_eq_one_iff_fsl identity.rhs x y
      rightXSimple rightYMultiple rightSomeY).mp rightOne
  · intro rightFSL
    have rightXSimple : S5_107.SimpleIn identity.rhs x := rightFSL.1
    have rightYMultiple : 2 ≤ identity.rhs.toList.count y := rightFSL.2.1
    have leftXSimple : S5_107.SimpleIn identity.lhs x :=
      (base.simple x).mpr rightXSimple
    have leftYMultiple : 2 ≤ identity.lhs.toList.count y :=
      (base_multiple base y).mpr rightYMultiple
    have rightSomeY : SomeYAfterX identity.rhs x y := by
      rcases rightFSL with ⟨_, _, before, after, split, _⟩
      exact ⟨before, y :: after, by simpa using split, by simp⟩
    have rightNotLast :
        ¬ S5_793Invariant.MultipleLastBeforeSimple identity.rhs y x :=
      (someYAfterX_iff_not_multipleLastBeforeSimple identity.rhs x y
        rightXSimple rightYMultiple).mp rightSomeY
    have leftNotLast :
        ¬ S5_793Invariant.MultipleLastBeforeSimple identity.lhs y x := by
      intro leftLast
      exact rightNotLast ((base.lastGap y x).mp leftLast)
    have leftSomeY : SomeYAfterX identity.lhs x y :=
      (someYAfterX_iff_not_multipleLastBeforeSimple identity.lhs x y
        leftXSimple leftYMultiple).mpr leftNotLast
    have rightOne : d4G.eval (fslValuation x y) identity.rhs = 1 :=
      (d4_eval_eq_one_iff_fsl identity.rhs x y
        rightXSimple rightYMultiple rightSomeY).mpr rightFSL
    have leftOne : d4G.eval (fslValuation x y) identity.lhs = 1 := by
      calc
        d4G.eval (fslValuation x y) identity.lhs =
            d4G.eval (fslValuation x y) identity.rhs :=
          valid (fslValuation x y)
        _ = 1 := rightOne
    exact (d4_eval_eq_one_iff_fsl identity.lhs x y
      leftXSimple leftYMultiple leftSomeY).mp leftOne

/-- Every D2-valid identity preserves the literal frozen descriptor. -/
theorem d2_valid_frozenDescriptor_eq
    (identity : Identity Nat) (valid : identity.SatisfiedBy d2G) :
    descriptor identity.lhs = descriptor identity.rhs := by
  have base := d2_base identity valid
  have fsl := d2_sameFSL_of_valid identity valid
  have prefixFSL : ∀ letter,
      SameFSL (prependLetter letter identity.lhs)
        (prependLetter letter identity.rhs) := by
    intro letter
    exact d2_sameFSL_of_valid
      (Identity.mk (prependLetter letter identity.lhs)
        (prependLetter letter identity.rhs))
      (prepend_valid d2G identity valid letter)
  have fss := sameFSS_of_prefixFSL base prefixFSL
  exact frozenDescriptor_eq_of_base_fsl_fss base fsl fss

/-- Every D4-valid identity preserves the literal frozen descriptor. -/
theorem d4_valid_frozenDescriptor_eq
    (identity : Identity Nat) (valid : identity.SatisfiedBy d4G) :
    descriptor identity.lhs = descriptor identity.rhs := by
  have base := d4_base identity valid
  have fsl := d4_sameFSL_of_valid identity valid
  have prefixFSL : ∀ letter,
      SameFSL (prependLetter letter identity.lhs)
        (prependLetter letter identity.rhs) := by
    intro letter
    exact d4_sameFSL_of_valid
      (Identity.mk (prependLetter letter identity.lhs)
        (prependLetter letter identity.rhs))
      (prepend_valid d4G identity valid letter)
  have fss := sameFSS_of_prefixFSL base prefixFSL
  exact frozenDescriptor_eq_of_base_fsl_fss base fsl fss

end SemigroupBasis.CoRoots.Order6D2D4SuffixTrace.V2

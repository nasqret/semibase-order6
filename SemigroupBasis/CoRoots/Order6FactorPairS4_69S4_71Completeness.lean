import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71Prelude
import SemigroupBasis.CoRoots.S5_378
import SemigroupBasis.CoRoots.S5_381Invariant

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

open SemigroupBasis
open SemigroupBasis.Examples

private def singletonProbe (selected : Nat) : Nat → Fin 4 :=
  fun letter => if letter = selected then 1 else 0

private theorem uniqueSeparatorFold_zero
    (valuation : Nat → Fin 4) (letters : List Nat) :
    letters.foldl
        (fun current letter =>
          uniqueSeparatorFourMul current (valuation letter))
        (0 : Fin 4) =
      0 := by
  induction letters with
  | nil => rfl
  | cons letter tail inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [show
        uniqueSeparatorFourMul 0 (valuation letter) = (0 : Fin 4) by
          simp [uniqueSeparatorFourMul]]
      exact inductionHypothesis

private theorem singletonProbe_eval_eq_zero_of_tail_ne_nil
    (selected : Nat) (word : Word Nat)
    (tailNe : word.tail ≠ [])
    (onlySelected :
      ∀ letter, letter ∈ word.toList → letter = selected) :
    uniqueSeparatorFour.semigroup.eval
        (singletonProbe selected) word =
      (0 : Fin 4) := by
  rcases word with ⟨head, tail⟩
  cases tail with
  | nil =>
      exact (tailNe rfl).elim
  | cons second rest =>
      have headEq : head = selected :=
        onlySelected head (by simp [Word.toList])
      have secondEq : second = selected :=
        onlySelected second (by simp [Word.toList])
      cases headEq
      cases secondEq
      change
        rest.foldl
            (fun current letter =>
              uniqueSeparatorFourMul current
                (singletonProbe selected letter))
            (uniqueSeparatorFourMul
              (singletonProbe selected selected)
              (singletonProbe selected selected)) =
          0
      rw [show singletonProbe selected selected = (1 : Fin 4) by
        simp [singletonProbe]]
      rw [show uniqueSeparatorFourMul 1 1 = (0 : Fin 4) by decide]
      exact uniqueSeparatorFold_zero (singletonProbe selected) rest

private theorem right_eq_of_left_singleton
    (left right : Word Nat)
    (leftSingleton : left.tail = [])
    (factorValid :
      ∀ valuation : Nat → Fin 4,
        SemigroupBasis.Generated.S4_69.table.semigroup.eval
            valuation left =
          SemigroupBasis.Generated.S4_69.table.semigroup.eval
            valuation right) :
    right = left := by
  have canonicalValid :
      ∀ valuation : Nat → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation left =
          uniqueSeparatorFour.semigroup.eval valuation right := by
    simpa [SemigroupBasis.Generated.S4_69.table] using factorValid
  have sameSupport :=
    uniqueSeparatorFourEqualEval_support_iff
      left right canonicalValid
  have rightLetters :
      ∀ letter, letter ∈ right.toList → letter = left.head := by
    intro letter member
    have leftMember : letter ∈ left.toList :=
      (sameSupport letter).mpr member
    simpa [Word.toList, leftSingleton] using leftMember
  have rightSingleton : right.tail = [] := by
    apply Decidable.byContradiction
    intro rightLong
    have rightZero :=
      singletonProbe_eval_eq_zero_of_tail_ne_nil
        left.head right rightLong rightLetters
    have leftOne :
        uniqueSeparatorFour.semigroup.eval
            (singletonProbe left.head) left =
          (1 : Fin 4) := by
      simp [Semigroup.eval, leftSingleton, singletonProbe]
    have evaluated := canonicalValid (singletonProbe left.head)
    rw [leftOne, rightZero] at evaluated
    exact (by decide : (1 : Fin 4) ≠ 0) evaluated
  have headEq : right.head = left.head :=
    rightLetters right.head (by simp [Word.toList])
  apply Word.toList_injective
  simp [Word.toList, leftSingleton, rightSingleton, headEq]

private theorem simpleInitial_forward_of_uniqueSeparatorEqualEval
    (source target : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation source =
          uniqueSeparatorFour.semigroup.eval valuation target)
    (letter : Nat)
    (sourceInitial :
      SemigroupBasis.CoRoots.S5_107.SimpleInitial source letter) :
    SemigroupBasis.CoRoots.S5_107.SimpleInitial target letter := by
  have sourceCut :
      UniqueSeparatorFourExactCut
        source.toList [] letter source.tail := by
    rcases source with ⟨head, tail⟩
    rcases sourceInitial with ⟨countOne, headEq⟩
    change head = letter at headEq
    subst head
    exact
      ⟨by simp [Word.toList], countOne,
        by simp [UniqueSeparatorFourSupportsDisjoint]⟩
  obtain
    ⟨targetLeft, targetRight, targetCut,
      targetLeftSupport, _targetRightSupport⟩ :=
    uniqueSeparatorFourEqualEval_transportExactCut
      source target equalEval sourceCut
  have targetLeftEmpty : targetLeft = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro tested member
    have emptyMember : tested ∈ ([] : List Nat) :=
      (targetLeftSupport tested).mp member
    simpa using emptyMember
  have targetHead : target.head = letter := by
    have split := targetCut.1
    rw [targetLeftEmpty] at split
    have heads := congrArg List.head? split
    simpa [Word.toList] using heads
  exact ⟨targetCut.2.1, targetHead⟩

private theorem s4_69Valid_simpleInitial_iff
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_69.table.semigroup)
    (letter : Nat) :
    SemigroupBasis.CoRoots.S5_107.SimpleInitial
        identity.lhs letter ↔
      SemigroupBasis.CoRoots.S5_107.SimpleInitial
        identity.rhs letter := by
  have semanticValid :
      ∀ valuation : Nat → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation identity.lhs =
          uniqueSeparatorFour.semigroup.eval valuation identity.rhs := by
    simpa [SemigroupBasis.Generated.S4_69.table] using valid
  constructor
  · exact
      simpleInitial_forward_of_uniqueSeparatorEqualEval
        identity.lhs identity.rhs semanticValid letter
  · exact
      simpleInitial_forward_of_uniqueSeparatorEqualEval
        identity.rhs identity.lhs
          (fun valuation => (semanticValid valuation).symm)
          letter

private theorem separatorSimpleSignature_of_factor_valid
    (identity : Identity Nat)
    (s4_69Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_69.table.semigroup)
    (s4_71Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_71.table.semigroup) :
    SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
      identity.lhs identity.rhs := by
  have semanticSeparatorValid :
      identity.SatisfiedBy uniqueSeparatorFour.semigroup := by
    simpa [SemigroupBasis.Generated.S4_69.table] using s4_69Valid
  refine ⟨?_, ?_, ?_⟩
  · intro letter
    exact
      uniqueSeparatorFourValid_support_iff
        identity semanticSeparatorValid letter
  · intro separator leftSupport rightSupport
    simpa only [SemigroupBasis.CoRoots.S5_378.ExactCutSignature] using
      uniqueSeparatorFourEqualEval_exactCut_iff
        identity.lhs identity.rhs semanticSeparatorValid
        separator leftSupport rightSupport
  · intro letter
    have capped :=
      SemigroupBasis.CoRoots.S5_793Invariant.s4_71Valid_cappedMultiplicity
        identity s4_71Valid letter
    unfold SemigroupBasis.CoRoots.S5_378.GloballySimple
    rw [← SemigroupBasis.CoRoots.S5_107.cappedMultiplicity_eq_one_iff,
      ← SemigroupBasis.CoRoots.S5_107.cappedMultiplicity_eq_one_iff,
      capped]

private theorem blockInitialSignature_of_factor_valid
    (identity : Identity Nat)
    (s4_69Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_69.table.semigroup)
    (s4_71Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_71.table.semigroup) :
    SemigroupBasis.CoRoots.S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
        identity.lhs identity.rhs := by
  have capped :
      ∀ letter,
        SemigroupBasis.CoRoots.S5_107.cappedMultiplicity
            identity.lhs letter =
          SemigroupBasis.CoRoots.S5_107.cappedMultiplicity
            identity.rhs letter :=
    fun letter =>
      SemigroupBasis.CoRoots.S5_793Invariant.s4_71Valid_cappedMultiplicity
        identity s4_71Valid letter
  exact
    ⟨s4_71Valid, capped,
      fun x y =>
        SemigroupBasis.CoRoots.S5_793Invariant.s4_71Valid_simplePrecedes
            identity s4_71Valid capped x y,
      fun x y =>
        SemigroupBasis.CoRoots.S5_793Invariant.s4_71Valid_multipleLastBeforeSimple
            identity s4_71Valid capped x y,
      fun letter =>
        s4_69Valid_simpleInitial_iff
          identity s4_69Valid letter⟩

/-- The exact joint invariant available from the two factors. The
separator component records support and every exact `S4_69` cut; the
block component records the capped multiplicities, simple-variable order,
last gaps, and simple initial marker retained by `S4_71` and `S4_69`. -/
structure SameJointSignature (left right : Word Nat) : Prop where
  separator :
    SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
      left right
  block :
    SemigroupBasis.CoRoots.S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
      left right

namespace SameJointSignature

theorem refl (word : Word Nat) :
    SameJointSignature word word :=
  ⟨⟨fun _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ => Iff.rfl⟩,
    SemigroupBasis.CoRoots.S5_381Invariant.SameSimpleSequenceLastGapInitialSignature.refl
      word⟩

theorem symm {left right : Word Nat}
    (same : SameJointSignature left right) :
    SameJointSignature right left :=
  ⟨⟨fun letter => (same.separator.support letter).symm,
      fun separator leftSupport rightSupport =>
        (same.separator.exactCuts
          separator leftSupport rightSupport).symm,
      fun letter => (same.separator.globallySimple letter).symm⟩,
    SemigroupBasis.CoRoots.S5_381Invariant.SameSimpleSequenceLastGapInitialSignature.symm
      same.block⟩

theorem trans {left middle right : Word Nat}
    (first : SameJointSignature left middle)
    (second : SameJointSignature middle right) :
    SameJointSignature left right :=
  ⟨⟨fun letter =>
        (first.separator.support letter).trans
          (second.separator.support letter),
      fun separator leftSupport rightSupport =>
        (first.separator.exactCuts
          separator leftSupport rightSupport).trans
            (second.separator.exactCuts
              separator leftSupport rightSupport),
      fun letter =>
        (first.separator.globallySimple letter).trans
          (second.separator.globallySimple letter)⟩,
    SemigroupBasis.CoRoots.S5_381Invariant.SameSimpleSequenceLastGapInitialSignature.trans
      first.block second.block⟩

end SameJointSignature

theorem sameJointSignature_of_factor_valid
    (identity : Identity Nat)
    (s4_69Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_69.table.semigroup)
    (s4_71Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_71.table.semigroup) :
    SameJointSignature identity.lhs identity.rhs :=
  ⟨separatorSimpleSignature_of_factor_valid
      identity s4_69Valid s4_71Valid,
    blockInitialSignature_of_factor_valid
      identity s4_69Valid s4_71Valid⟩

/-- The sole motif-8 residual: the exact joint signature is
derivationally sufficient for non-singleton words. All raw `S4_69`
semantics have been replaced by support and exact-cut data; the retained
`S4_71` block certificate is the one consumed by the established block
normalizers. -/
def JointSignatureCanonicalization : Prop :=
  ∀ {left right : Word Nat},
    left.tail ≠ [] →
      right.tail ≠ [] →
        SameJointSignature left right →
          Derives basis left right

/-- The original long-word obligation, now discharged from the isolated
joint-signature canonicalization kernel. -/
def LongWordDerivationalObligation : Prop :=
  ∀ identity : Identity Nat,
    identity.lhs.tail ≠ [] →
      identity.rhs.tail ≠ [] →
        identity.SatisfiedBy
            SemigroupBasis.Generated.S4_69.table.semigroup →
          identity.SatisfiedBy
              SemigroupBasis.Generated.S4_71.table.semigroup →
            Derives basis identity.lhs identity.rhs

theorem longWordDerivationalObligation
    (canonicalize : JointSignatureCanonicalization) :
    LongWordDerivationalObligation := by
  intro identity leftLong rightLong s4_69Valid s4_71Valid
  exact
    canonicalize leftLong rightLong
      (sameJointSignature_of_factor_valid
        identity s4_69Valid s4_71Valid)

/-- Joint-signature canonicalization suffices for unrestricted joint
derivability; singleton-sided identities are rigid in `S4_69`. -/
theorem derivesOfFactorValid
    (canonicalize : JointSignatureCanonicalization) :
    ∀ identity : Identity Nat,
      identity.SatisfiedBy
          SemigroupBasis.Generated.S4_69.table.semigroup →
        identity.SatisfiedBy
            SemigroupBasis.Generated.S4_71.table.semigroup →
          Derives basis identity.lhs identity.rhs := by
  intro identity s4_69Valid s4_71Valid
  by_cases leftSingleton : identity.lhs.tail = []
  · have rightEq :=
      right_eq_of_left_singleton
        identity.lhs identity.rhs leftSingleton s4_69Valid
    rw [rightEq]
    exact Derives.refl _
  · by_cases rightSingleton : identity.rhs.tail = []
    · have leftEq :=
        right_eq_of_left_singleton
          identity.rhs identity.lhs rightSingleton
            (fun valuation => (s4_69Valid valuation).symm)
      rw [leftEq]
      exact Derives.refl _
    · exact
        longWordDerivationalObligation canonicalize
          identity leftSingleton rightSingleton
          s4_69Valid s4_71Valid

/-- Package the isolated joint-normalization proof as the factor
intersection basis. -/
def factorIntersectionBasis
    (canonicalize : JointSignatureCanonicalization) :
    IntersectionBasis
      SemigroupBasis.Generated.S4_69.table.semigroup
      SemigroupBasis.Generated.S4_71.table.semigroup basis :=
  intersectionBasisOfCompleteness (derivesOfFactorValid canonicalize)

end SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

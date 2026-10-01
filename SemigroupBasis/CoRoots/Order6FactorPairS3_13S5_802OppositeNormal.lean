import SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802OppositeGuardedLift
import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_13
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802Opposite

open SemigroupBasis
open SemigroupBasis.Examples

abbrev leftFactor :=
  SemigroupBasis.Generated.S3_13.table.semigroup

abbrev rightFactor :=
  SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup.opposite

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def oppositeFiniteTable (table : FiniteTable) : FiniteTable where
  order := table.order
  mul := fun left right => table.mul right left
  assoc := fun left middle right =>
    (table.assoc right middle left).symm

private theorem oppositeFiniteTable_semigroup (table : FiniteTable) :
    (oppositeFiniteTable table).semigroup =
      table.semigroup.opposite := by
  rfl

theorem modelsLeft : Models leftFactor basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_13.table basis toFinThree (by decide)

theorem modelsRight : Models rightFactor basis := by
  change Models
    SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup.opposite basis
  rw [← oppositeFiniteTable_semigroup
    SemigroupBasis.Generated.Catalogue.S5_802.table]
  exact FiniteCertificate.checkModels_sound
    (oppositeFiniteTable
      SemigroupBasis.Generated.Catalogue.S5_802.table)
    basis toFinThree (by decide)

private theorem oppositeBasisModelsCommutativeExponentThree :
    Models commutativeExponentThree.semigroup
      SemigroupBasis.CoRoots.S5_794.oppositeBasis :=
  FiniteCertificate.checkModels_sound
    commutativeExponentThree
    SemigroupBasis.CoRoots.S5_794.oppositeBasis
    SemigroupBasis.CoRoots.S5_794.toFinFour (by decide)

/-- The precise information contributed by the two factors.  The left normal
band fixes head and support.  The complete opposite-`S5_802` presentation,
tested in the exponent-three detector, fixes multiplicity capped at two. -/
structure JointInvariant (left right : Word Nat) : Prop where
  head : left.head = right.head
  support : forall letter, letter ∈ left.toList ↔ letter ∈ right.toList
  capped : forall letter,
    min (left.toList.count letter) 2 =
      min (right.toList.count letter) 2

theorem invariantOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    JointInvariant identity.lhs identity.rhs := by
  have leftNormalValid :
      identity.SatisfiedBy leftNormalBandThree.semigroup := by
    simpa [leftFactor, SemigroupBasis.Generated.S3_13.table,
      leftNormalBandThree] using leftValid
  have sourceDerivation :=
    SemigroupBasis.CoRoots.S5_794Family.S5_802.oppositeBasisFor.2
      identity rightValid
  have countValid :=
    sourceDerivation.sound
      oppositeBasisModelsCommutativeExponentThree
  exact
    ⟨leftNormalBandValid_head_eq identity leftNormalValid,
      leftNormalBandValid_support_eq identity leftNormalValid,
      exponentValid_capped_count_eq identity countValid⟩

namespace JointInvariant

theorem countOne_iff {left right : Word Nat}
    (same : JointInvariant left right) :
    left.toList.count left.head = 1 ↔
      right.toList.count right.head = 1 := by
  constructor
  · intro leftOne
    have capped := same.capped left.head
    have rightOne : right.toList.count left.head = 1 := by
      omega
    simpa [same.head] using rightOne
  · intro rightOne
    have capped := same.capped right.head
    have leftOne : left.toList.count right.head = 1 := by
      omega
    simpa [same.head] using leftOne

end JointInvariant

private theorem head_not_mem_tail_of_count_one
    (word : Word Nat)
    (countOne : word.toList.count word.head = 1) :
    word.head ∉ word.tail := by
  cases word with
  | mk head tail =>
      intro member
      have positive : 0 < tail.count head :=
        List.count_pos_iff.mpr member
      simp only [Word.toList, List.count_cons_self] at countOne
      omega

private theorem head_mem_tail_of_count_ne_one
    (word : Word Nat)
    (countNotOne : word.toList.count word.head ≠ 1) :
    word.head ∈ word.tail := by
  apply Decidable.byContradiction
  intro absent
  apply countNotOne
  cases word with
  | mk head tail =>
      simp [Word.toList, List.count_eq_zero.mpr absent]

private theorem tail_nil_of_invariant
    {left right : Word Nat}
    (same : JointInvariant left right)
    (rightHeadSimple : right.toList.count right.head = 1)
    (leftTailEmpty : left.tail = []) :
    right.tail = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter member
  have rightMember : letter ∈ right.toList := by
    cases right
    simp [Word.toList, member]
  have leftMember : letter ∈ left.toList :=
    (same.support letter).2 rightMember
  have letterIsLeftHead : letter = left.head := by
    cases left with
    | mk leftHead leftTail =>
        change leftTail = [] at leftTailEmpty
        subst leftTail
        simpa [Word.toList] using leftMember
  have letterIsRightHead : letter = right.head :=
    letterIsLeftHead.trans same.head
  have rightHeadInTail : right.head ∈ right.tail := by
    simpa [letterIsRightHead] using member
  cases right with
  | mk head tail =>
      have positive : 0 < tail.count head :=
        List.count_pos_iff.mpr rightHeadInTail
      simp only [Word.toList, List.count_cons_self] at rightHeadSimple
      omega

private theorem tail_nil_iff_of_invariant
    {left right : Word Nat}
    (same : JointInvariant left right)
    (leftHeadSimple : left.toList.count left.head = 1)
    (rightHeadSimple : right.toList.count right.head = 1) :
    left.tail = [] ↔ right.tail = [] := by
  constructor
  · exact tail_nil_of_invariant same rightHeadSimple
  · exact tail_nil_of_invariant
      ⟨same.head.symm,
        fun letter => (same.support letter).symm,
        fun letter => (same.capped letter).symm⟩
      leftHeadSimple

private theorem listDerivesDuplicateInitial
    (head : Nat) {tail : List Nat}
    (headInTail : head ∈ tail) :
    SemigroupBasis.CoRoots.S5_107.ListDerives basis
      (head :: tail) (head :: head :: tail) := by
  rcases List.append_of_mem headInTail with
    ⟨before, after, rfl⟩
  cases before with
  | nil =>
      have expanded :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesPowerExpansion (Word.singleton head))
      simpa [Word.toList_append, List.append_assoc] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.append expanded after
  | cons middleHead middleTail =>
      let middle :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons
          middleHead middleTail
      have expanded :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesLeftDuplication (Word.singleton head) middle)
      simpa [middle, SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.toList_append, List.append_assoc] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.append expanded after

private theorem derivesDuplicateInitial
    (word : Word Nat)
    (headInTail : word.head ∈ word.tail) :
    Derives basis word (Word.singleton word.head ++ word) := by
  cases word with
  | mk head tail =>
      have listDerivation :=
        listDerivesDuplicateInitial head headInTail
      simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.singleton, Word.append] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.toWord listDerivation

private theorem foldl_eval_congr
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat -> S) :
    forall (letters : List Nat) (initial : S),
      (forall letter, letter ∈ letters ->
        leftValuation letter = rightValuation letter) ->
      letters.foldl
          (fun value letter =>
            semigroup.mul value (leftValuation letter))
          initial =
        letters.foldl
          (fun value letter =>
            semigroup.mul value (rightValuation letter))
          initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (List.Mem.head rest)]
      apply foldl_eval_congr semigroup
      intro tested member
      exact agree tested (List.Mem.tail letter member)

private theorem eval_congr_on_support
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat -> S)
    (word : Word Nat)
    (agree :
      forall letter, letter ∈ word.toList ->
        leftValuation letter = rightValuation letter) :
    semigroup.eval leftValuation word =
      semigroup.eval rightValuation word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [agree head (by simp [Word.toList])]
      apply foldl_eval_congr semigroup
      intro letter member
      exact agree letter (List.Mem.tail head member)

private theorem rightFactor_left_identity (value : Fin 5) :
    rightFactor.mul (4 : Fin 5) value = value := by
  apply Fin.ext
  revert value
  decide

/-- Assigning the common simple head to the identity of the opposite monoid
cancels it and exposes a valid suffix identity. -/
private theorem right_suffix_valid
    (head : Nat) (left right : Word Nat)
    (headNotLeft : head ∉ left.toList)
    (headNotRight : head ∉ right.toList)
    (wholeValid :
      (Identity.mk
        (Word.singleton head ++ left)
        (Word.singleton head ++ right)).SatisfiedBy rightFactor) :
    (Identity.mk left right).SatisfiedBy rightFactor := by
  intro valuation
  let lifted : Nat -> Fin 5 :=
    fun letter => if letter = head then 4 else valuation letter
  have leftAgree :
      rightFactor.eval valuation left =
        rightFactor.eval lifted left := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ head := by
      intro equal
      subst letter
      exact headNotLeft member
    simp [lifted, different]
  have rightAgree :
      rightFactor.eval valuation right =
        rightFactor.eval lifted right := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ head := by
      intro equal
      subst letter
      exact headNotRight member
    simp [lifted, different]
  have evaluated := wholeValid lifted
  simp only [Semigroup.eval_append, Semigroup.eval_singleton] at evaluated
  have liftedHead : lifted head = (4 : Fin 5) := by
    simp [lifted]
  rw [liftedHead, rightFactor_left_identity,
    rightFactor_left_identity] at evaluated
  exact leftAgree.trans <| evaluated.trans rightAgree.symm

/-- Unrestricted completeness of the eight-law Sigma for the intersection of
the left-normal-band head theory and opposite `S5_802`.  The proof is a
relative deduction argument over the complete lower-order presentation, not a
bounded identity inventory. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives basis identity.lhs identity.rhs := by
  have same := invariantOfFactorValid identity leftValid rightValid
  have countIff := same.countOne_iff
  by_cases leftHeadSimple :
      identity.lhs.toList.count identity.lhs.head = 1
  · have rightHeadSimple :
        identity.rhs.toList.count identity.rhs.head = 1 :=
      countIff.mp leftHeadSimple
    have tailsEmpty :=
      tail_nil_iff_of_invariant
        same leftHeadSimple rightHeadSimple
    cases identity with
    | mk left right =>
        cases left with
        | mk leftHead leftTail =>
            cases right with
            | mk rightHead rightTail =>
                have headsEqual : leftHead = rightHead := same.head
                subst rightHead
                cases leftTail with
                | nil =>
                    have rightEmpty : rightTail = [] :=
                      tailsEmpty.mp rfl
                    subst rightTail
                    exact Derives.refl _
                | cons leftSuffixHead leftSuffixTail =>
                    cases rightTail with
                    | nil =>
                        have impossible :
                            leftSuffixHead :: leftSuffixTail = [] :=
                          tailsEmpty.mpr rfl
                        contradiction
                    | cons rightSuffixHead rightSuffixTail =>
                        let leftSuffix : Word Nat :=
                          Word.mk leftSuffixHead leftSuffixTail
                        let rightSuffix : Word Nat :=
                          Word.mk rightSuffixHead rightSuffixTail
                        have leftHeadAbsent :
                            leftHead ∉ leftSuffix.toList := by
                          simpa [leftSuffix, Word.toList] using
                            head_not_mem_tail_of_count_one
                              (Word.mk leftHead
                                (leftSuffixHead :: leftSuffixTail))
                              leftHeadSimple
                        have rightHeadAbsent :
                            leftHead ∉ rightSuffix.toList := by
                          simpa [rightSuffix, Word.toList] using
                            head_not_mem_tail_of_count_one
                              (Word.mk leftHead
                                (rightSuffixHead :: rightSuffixTail))
                              rightHeadSimple
                        have wholeValid :
                            (Identity.mk
                              (Word.singleton leftHead ++ leftSuffix)
                              (Word.singleton leftHead ++ rightSuffix)).SatisfiedBy
                                rightFactor := by
                          simpa [leftSuffix, rightSuffix, Word.singleton,
                            Word.append] using rightValid
                        have suffixValid :=
                          right_suffix_valid leftHead leftSuffix rightSuffix
                            leftHeadAbsent rightHeadAbsent wholeValid
                        have sourceDerivation :=
                          SemigroupBasis.CoRoots.S5_794Family.S5_802.oppositeBasisFor.2
                            (Identity.mk leftSuffix rightSuffix) suffixValid
                        have lifted :=
                          liftOppositeBasisUnderPrefixIdentity
                            sourceDerivation (Word.singleton leftHead)
                        simpa [leftSuffix, rightSuffix, Word.singleton,
                          Word.append] using lifted
  · have rightHeadNotSimple :
        identity.rhs.toList.count identity.rhs.head ≠ 1 := by
      intro rightSimple
      exact leftHeadSimple (countIff.mpr rightSimple)
    have leftHeadInTail : identity.lhs.head ∈ identity.lhs.tail :=
      head_mem_tail_of_count_ne_one identity.lhs leftHeadSimple
    have rightHeadInTail : identity.rhs.head ∈ identity.rhs.tail :=
      head_mem_tail_of_count_ne_one identity.rhs rightHeadNotSimple
    have leftDuplicate :=
      derivesDuplicateInitial identity.lhs leftHeadInTail
    have rightDuplicate :=
      derivesDuplicateInitial identity.rhs rightHeadInTail
    have sourceDerivation :=
      SemigroupBasis.CoRoots.S5_794Family.S5_802.oppositeBasisFor.2
        identity rightValid
    have lifted :=
      liftOppositeBasisUnderPrefixIdentity sourceDerivation
        (Word.singleton identity.lhs.head)
    have guarded :
        Derives basis
          (Word.singleton identity.lhs.head ++ identity.lhs)
          (Word.singleton identity.rhs.head ++ identity.rhs) := by
      simpa [same.head] using lifted
    exact leftDuplicate.trans <|
      guarded.trans rightDuplicate.symm

def intersectionBasis : IntersectionBasis leftFactor rightFactor basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

end SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802Opposite

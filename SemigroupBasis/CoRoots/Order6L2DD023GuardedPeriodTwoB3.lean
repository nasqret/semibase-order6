import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_443Family
import SemigroupBasis.CoRoots.S5_793Invariant
import SemigroupBasis.Generated.S2_4
import SemigroupBasis.Subdirect

/-!
# The guarded period-two B3 intersection root for L2D delivery d023

This module wraps the unrestricted opposite-oriented Edmunds period-two
calculus behind a nonempty guard.  The literal three-law basis is

* `xx = xxxx`,
* `xxy = xyx`, and
* `xyyzz = xzyyz`.

The right-hand signature is validity in `S5_614^op`; the left-zero factor
adds exactly equality of the literal heads.  No bounded search result is used
in the unrestricted proof.
-/

namespace SemigroupBasis.CoRoots.Order6L2DD023GuardedPeriodTwoB3

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def xyyzz : Word Nat := w 0 [1, 1, 2, 2]
def xzyyz : Word Nat := w 0 [2, 1, 1, 2]

def powerLaw : Identity Nat := Identity.mk xx xxxx
def gatherLaw : Identity Nat := Identity.mk xxy xyx
def guardedSquareSwapLaw : Identity Nat := Identity.mk xyyzz xzyyz

/-- The exact direct three-law basis accepted for d023. -/
def B3 : List (Identity Nat) :=
  [powerLaw, gatherLaw, guardedSquareSwapLaw]

/-- The exact intersection invariant: the unrestricted `S5_614^op` theory
plus the common literal head supplied by the `S2_4` left-zero factor. -/
structure SameGuardedPeriodTwoSignature
    (left right : Word Nat) : Prop where
  core :
    (Identity.mk left right).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup.opposite
  head : left.head = right.head

/-! ## Literal B3 rewrite moves -/

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

private theorem basisPowerLaw :
    Derives B3 powerLaw.lhs powerLaw.rhs :=
  Derives.fromBasis (e := powerLaw) (List.Mem.head _)

private theorem basisGatherLaw :
    Derives B3 gatherLaw.lhs gatherLaw.rhs :=
  Derives.fromBasis (e := gatherLaw) <|
    List.Mem.tail _ (List.Mem.head _)

private theorem basisGuardedSquareSwapLaw :
    Derives B3 guardedSquareSwapLaw.lhs guardedSquareSwapLaw.rhs :=
  Derives.fromBasis (e := guardedSquareSwapLaw) <|
    List.Mem.tail _ <| List.Mem.tail _ (List.Mem.head _)

/-- Expand two copies of any nonempty word to four copies. -/
theorem derivesPowerExpansion (word : Word Nat) :
    Derives B3
      (word ++ word)
      (((word ++ word) ++ word) ++ word) := by
  have substituted :=
    Derives.subst basisPowerLaw
      (instantiateThreeWords word word word)
  simpa [powerLaw, xx, xxxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- The second B3 law gathers a second copy across a nonempty middle word. -/
theorem derivesGather (repeated middle : Word Nat) :
    Derives B3
      ((repeated ++ repeated) ++ middle)
      ((repeated ++ middle) ++ repeated) := by
  have substituted :=
    Derives.subst basisGatherLaw
      (instantiateThreeWords repeated middle middle)
  simpa [gatherLaw, xxy, xyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- The literal third B3 law with arbitrary nonempty word images. -/
theorem derivesGuardedSquareStep
    (ctx left right : Word Nat) :
    Derives B3
      (ctx ++ ((left ++ left) ++ (right ++ right)))
      (ctx ++ (((right ++ (left ++ left)) ++ right))) := by
  have substituted :=
    Derives.subst basisGuardedSquareSwapLaw
      (instantiateThreeWords ctx left right)
  simpa [guardedSquareSwapLaw, xyyzz, xzyyz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Double blocks commute behind an arbitrary nonempty protected prefix.
The third law performs the guarded switch and the reverse of the second law
regathers the displaced right block. -/
theorem derivesGuardedSquareCommutation
    (ctx left right : Word Nat) :
    Derives B3
      (ctx ++ ((left ++ left) ++ (right ++ right)))
      (ctx ++ ((right ++ right) ++ (left ++ left))) := by
  have switched := derivesGuardedSquareStep ctx left right
  have gathered :=
    Derives.prepend ctx (derivesGather right (left ++ left))
  exact switched.trans <| by
    simpa only [Word.append_assoc] using gathered.symm

/-! ## Guarded replay of the Edmunds calculus -/

private theorem bindAppend
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bindBind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bindSingleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem edmundsBasis_eq_reversedS5_443Basis :
    edmundsPeriodTwoBlocksBasis =
      reversedBasis S5_443Family.basis := by
  decide

private theorem edmundsBasisForS5_614op :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup.opposite
      edmundsPeriodTwoBlocksBasis := by
  rw [edmundsBasis_eq_reversedS5_443Basis]
  exact S5_443Family.S5_614.opposite_basis_complete

/-- Replay every opposite-oriented Edmunds derivation behind a protected
nonempty prefix, while allowing an additional word substitution. -/
theorem liftEdmundsUnderPrefix
    {left right : Word Nat}
    (derivation : Derives edmundsPeriodTwoBlocksBasis left right)
    (ctx : Word Nat) (substitution : Nat → Word Nat) :
    Derives B3
      (ctx ++ left.bind substitution)
      (ctx ++ right.bind substitution) := by
  induction derivation generalizing ctx substitution with
  | fromBasis member =>
      simp only [edmundsPeriodTwoBlocksBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · change Derives B3
          (ctx ++ (substitution 0 ++ substitution 0))
          (ctx ++ (((substitution 0 ++ substitution 0) ++
            substitution 0) ++ substitution 0))
        exact Derives.prepend ctx
          (derivesPowerExpansion (substitution 0))
      · change Derives B3
          (ctx ++ ((substitution 0 ++ substitution 1) ++
            substitution 0))
          (ctx ++ ((substitution 0 ++ substitution 0) ++
            substitution 1))
        simpa only [Word.append_assoc] using
          Derives.prepend ctx
            (derivesGather (substitution 0) (substitution 1)).symm
      · simpa only [edmundsPeriodTwoBlocksCommutationLaw,
          edmundsPeriodTwoBlocksYYXX, edmundsPeriodTwoBlocksXXYY,
          Word.bind, List.foldl_cons, List.foldl_nil,
          Word.append_assoc] using
          derivesGuardedSquareCommutation
            ctx (substitution 1) (substitution 0)
  | refl =>
      exact Derives.refl _
  | symm _ inductionHypothesis =>
      exact (inductionHypothesis ctx substitution).symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact
        (firstHypothesis ctx substitution).trans
          (secondHypothesis ctx substitution)
  | prepend pre _ inductionHypothesis =>
      simpa [bindAppend, Word.append_assoc] using
        inductionHypothesis
          (ctx ++ pre.bind substitution) substitution
  | appendRight _ post inductionHypothesis =>
      simpa [bindAppend, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis ctx substitution)
          (post.bind substitution)
  | subst _ first inductionHypothesis =>
      simpa [bindBind] using
        inductionHypothesis ctx
          (fun letter => (first letter).bind substitution)

/-! ## Direct B3 soundness -/

private theorem edmundsDerivesPowerLaw :
    Derives edmundsPeriodTwoBlocksBasis xx xxxx := by
  change Derives edmundsPeriodTwoBlocksBasis
    edmundsPeriodTwoBlocksXX edmundsPeriodTwoBlocksXXXX
  exact Derives.fromBasis
    (e := edmundsPeriodTwoBlocksPowerLaw) (List.Mem.head _)

private theorem edmundsDerivesGatherLaw :
    Derives edmundsPeriodTwoBlocksBasis xxy xyx := by
  change Derives edmundsPeriodTwoBlocksBasis
    edmundsPeriodTwoBlocksXXY edmundsPeriodTwoBlocksXYX
  exact (Derives.fromBasis
    (e := edmundsPeriodTwoBlocksGatherLaw) <|
      List.Mem.tail _ (List.Mem.head _)).symm

private theorem edmundsDerivesGuardedSquareSwapLaw :
    Derives edmundsPeriodTwoBlocksBasis xyyzz xzyyz := by
  let xWord := Word.singleton 0
  let yWord := Word.singleton 1
  let zWord := Word.singleton 2
  have swapped :=
    Derives.prepend xWord <|
      edmundsPeriodTwoBlocksDerivesDoubleDoubleCommutation
        yWord zWord
  have gathered :=
    Derives.prepend xWord <|
      edmundsPeriodTwoBlocksDerivesGather zWord (yWord ++ yWord)
  have derivation := swapped.trans gathered.symm
  simpa [xWord, yWord, zWord, xyyzz, xzyyz, w,
    Word.singleton, Word.append, Word.append_assoc] using derivation

theorem modelsS2_4 :
    Models SemigroupBasis.Generated.S2_4.table.semigroup B3 := by
  rw [SemigroupBasis.Generated.S2_4.table_eq_catalogue_model]
  intro identity member valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval]
  simp only [B3, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem modelsS5_614op :
    Models
      SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup.opposite
      B3 := by
  intro identity member
  simp only [B3, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact edmundsDerivesPowerLaw.sound edmundsBasisForS5_614op.1
  · exact edmundsDerivesGatherLaw.sound edmundsBasisForS5_614op.1
  · exact
      edmundsDerivesGuardedSquareSwapLaw.sound
        edmundsBasisForS5_614op.1

/-! ## Signature consequences -/

private theorem periodTwoFromTwoExponent_eq_zero_iff (n : Nat) :
    periodTwoFromTwoExponent n = 0 ↔ n = 0 := by
  unfold periodTwoFromTwoExponent
  split <;> omega

private theorem periodTwoFromTwoExponent_eq_one_iff (n : Nat) :
    periodTwoFromTwoExponent n = 1 ↔ n = 1 := by
  unfold periodTwoFromTwoExponent
  split <;> omega

namespace SameGuardedPeriodTwoSignature

theorem symm {left right : Word Nat}
    (same : SameGuardedPeriodTwoSignature left right) :
    SameGuardedPeriodTwoSignature right left where
  core := fun valuation => (same.core valuation).symm
  head := same.head.symm

theorem exponent {left right : Word Nat}
    (same : SameGuardedPeriodTwoSignature left right)
    (letter : Nat) :
    periodTwoFromTwoExponent (left.toList.count letter) =
      periodTwoFromTwoExponent (right.toList.count letter) :=
  S5_443Family.S5_614Semantics.valid_exponent_eq
    (Identity.mk left right) same.core letter

theorem absent {left right : Word Nat}
    (same : SameGuardedPeriodTwoSignature left right)
    (letter : Nat) :
    letter ∉ left.toList ↔ letter ∉ right.toList := by
  have exponentEqual := same.exponent letter
  constructor
  · intro leftAbsent
    have leftExponentZero :
        periodTwoFromTwoExponent (left.toList.count letter) = 0 :=
      (periodTwoFromTwoExponent_eq_zero_iff _).2
        (List.count_eq_zero.mpr leftAbsent)
    have rightExponentZero :
        periodTwoFromTwoExponent (right.toList.count letter) = 0 :=
      exponentEqual.symm.trans leftExponentZero
    exact List.count_eq_zero.mp <|
      (periodTwoFromTwoExponent_eq_zero_iff _).1 rightExponentZero
  · intro rightAbsent
    have rightExponentZero :
        periodTwoFromTwoExponent (right.toList.count letter) = 0 :=
      (periodTwoFromTwoExponent_eq_zero_iff _).2
        (List.count_eq_zero.mpr rightAbsent)
    have leftExponentZero :
        periodTwoFromTwoExponent (left.toList.count letter) = 0 :=
      exponentEqual.trans rightExponentZero
    exact List.count_eq_zero.mp <|
      (periodTwoFromTwoExponent_eq_zero_iff _).1 leftExponentZero

theorem support {left right : Word Nat}
    (same : SameGuardedPeriodTwoSignature left right)
    (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := by
  simpa using not_congr (same.absent letter)

theorem simple {left right : Word Nat}
    (same : SameGuardedPeriodTwoSignature left right)
    (letter : Nat) :
    left.toList.count letter = 1 ↔
      right.toList.count letter = 1 := by
  have exponentEqual := same.exponent letter
  constructor
  · intro leftSimple
    have leftExponentOne :
        periodTwoFromTwoExponent (left.toList.count letter) = 1 :=
      (periodTwoFromTwoExponent_eq_one_iff _).2 leftSimple
    have rightExponentOne :
        periodTwoFromTwoExponent (right.toList.count letter) = 1 :=
      exponentEqual.symm.trans leftExponentOne
    exact
      (periodTwoFromTwoExponent_eq_one_iff _).1 rightExponentOne
  · intro rightSimple
    have rightExponentOne :
        periodTwoFromTwoExponent (right.toList.count letter) = 1 :=
      (periodTwoFromTwoExponent_eq_one_iff _).2 rightSimple
    have leftExponentOne :
        periodTwoFromTwoExponent (left.toList.count letter) = 1 :=
      exponentEqual.trans rightExponentOne
    exact
      (periodTwoFromTwoExponent_eq_one_iff _).1 leftExponentOne

end SameGuardedPeriodTwoSignature

/-- Factor validity produces exactly the guarded period-two signature. -/
theorem sameGuardedPeriodTwoSignature_of_factorValidity
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup.opposite) :
    SameGuardedPeriodTwoSignature identity.lhs identity.rhs := by
  have leftZeroValid :
      identity.SatisfiedBy leftZeroTwo.semigroup := by
    rw [← SemigroupBasis.Generated.S2_4.table_eq_catalogue_model]
    exact leftValid
  exact
    ⟨rightValid,
      S5_793Invariant.leftZeroValid_head_eq identity leftZeroValid⟩

/-! ## Head-boundary lemmas -/

private theorem foldlEvalCongr
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat → S) :
    ∀ (letters : List Nat) (initial : S),
      (∀ letter, letter ∈ letters →
        leftValuation letter = rightValuation letter) →
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
      apply foldlEvalCongr semigroup
      intro tested member
      exact agree tested (List.Mem.tail letter member)

private theorem evalCongrOnSupport
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat → S)
    (word : Word Nat)
    (agree :
      ∀ letter, letter ∈ word.toList →
        leftValuation letter = rightValuation letter) :
    semigroup.eval leftValuation word =
      semigroup.eval rightValuation word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [agree head (by simp [Word.toList])]
      apply foldlEvalCongr semigroup
      intro letter member
      exact agree letter (List.Mem.tail head member)

private theorem suffixValidOfSimplePrefix
    (semigroup : Semigroup S) (one : S)
    (leftIdentity : ∀ value, semigroup.mul one value = value)
    (head : Nat) (left right : Word Nat)
    (headNotLeft : head ∉ left.toList)
    (headNotRight : head ∉ right.toList)
    (wholeValid :
      (Identity.mk
        (Word.singleton head ++ left)
        (Word.singleton head ++ right)).SatisfiedBy semigroup) :
    (Identity.mk left right).SatisfiedBy semigroup := by
  intro valuation
  let lifted : Nat → S :=
    fun letter => if letter = head then one else valuation letter
  have leftAgree :
      semigroup.eval valuation left =
        semigroup.eval lifted left := by
    apply evalCongrOnSupport
    intro letter member
    have different : letter ≠ head := by
      intro equality
      subst letter
      exact headNotLeft member
    simp [lifted, different]
  have rightAgree :
      semigroup.eval valuation right =
        semigroup.eval lifted right := by
    apply evalCongrOnSupport
    intro letter member
    have different : letter ≠ head := by
      intro equality
      subst letter
      exact headNotRight member
    simp [lifted, different]
  have evaluated := wholeValid lifted
  simp only [Semigroup.eval_append, Semigroup.eval_singleton] at evaluated
  have liftedHead : lifted head = one := by
    simp [lifted]
  rw [liftedHead, leftIdentity, leftIdentity] at evaluated
  exact leftAgree.trans <| evaluated.trans rightAgree.symm

private theorem s5_614opLeftIdentity (value : Fin 5) :
    SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup.opposite.mul
        (4 : Fin 5) value = value := by
  apply Fin.ext
  revert value
  decide

private theorem headNotMemTailOfCountOne
    (word : Word Nat)
    (countOne : word.toList.count word.head = 1) :
    word.head ∉ word.tail := by
  have countZero : word.tail.count word.head = 0 := by
    cases word with
    | mk head tail =>
        simpa [Word.toList] using countOne
  exact List.count_eq_zero.mp countZero

private theorem headMemTailOfCountNeOne
    (word : Word Nat)
    (countNotOne : word.toList.count word.head ≠ 1) :
    word.head ∈ word.tail := by
  apply Decidable.byContradiction
  intro absent
  apply countNotOne
  cases word with
  | mk head tail =>
      simp [Word.toList, List.count_eq_zero.mpr absent]

private theorem headCountOneIff
    {left right : Word Nat}
    (same : SameGuardedPeriodTwoSignature left right) :
    left.toList.count left.head = 1 ↔
      right.toList.count right.head = 1 := by
  have simpleIff := same.simple left.head
  simpa [same.head] using simpleIff

private theorem tailNilOfSameSignature
    {left right : Word Nat}
    (same : SameGuardedPeriodTwoSignature left right)
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
    have headOrTail :
        letter = left.head ∨ letter ∈ left.tail := by
      simpa [Word.toList] using leftMember
    rcases headOrTail with equality | inTail
    · exact equality
    · simp [leftTailEmpty] at inTail
  have letterIsRightHead : letter = right.head :=
    letterIsLeftHead.trans same.head
  have rightHeadInTail : right.head ∈ right.tail := by
    simpa [letterIsRightHead] using member
  exact
    (headNotMemTailOfCountOne right rightHeadSimple) rightHeadInTail

private theorem tailNilIffOfSameSignature
    {left right : Word Nat}
    (same : SameGuardedPeriodTwoSignature left right)
    (leftHeadSimple : left.toList.count left.head = 1)
    (rightHeadSimple : right.toList.count right.head = 1) :
    left.tail = [] ↔ right.tail = [] := by
  constructor
  · exact tailNilOfSameSignature
      same rightHeadSimple
  · exact tailNilOfSameSignature
      same.symm leftHeadSimple

/-! ## Repeated-head padding -/

private theorem derivesAddInitialPairAcross
    (head : Nat) (middle : Word Nat) :
    Derives B3
      ((Word.singleton head ++ middle) ++ Word.singleton head)
      ((Word.singleton head ++ Word.singleton head) ++
        ((Word.singleton head ++ middle) ++ Word.singleton head)) := by
  have gathered :=
    (derivesGather (Word.singleton head) middle).symm
  have expanded :=
    Derives.appendRight
      (derivesPowerExpansion (Word.singleton head)) middle
  have restored :=
    Derives.prepend
      (Word.singleton head ++ Word.singleton head)
      (derivesGather (Word.singleton head) middle)
  have expanded' :
      Derives B3
        ((Word.singleton head ++ Word.singleton head) ++ middle)
        ((Word.singleton head ++ Word.singleton head) ++
          ((Word.singleton head ++ Word.singleton head) ++ middle)) := by
    simpa only [Word.append_assoc] using expanded
  exact gathered.trans <| expanded'.trans <| by
    simpa only [Word.append_assoc] using restored

private abbrev ListDerives := S5_107.ListDerives B3

private theorem listDerivesAddInitialPair
    (head : Nat) (tail : List Nat)
    (headInTail : head ∈ tail) :
    ListDerives
      (head :: tail) ([head, head] ++ head :: tail) := by
  rcases List.append_of_mem headInTail with
    ⟨before, after, rfl⟩
  cases before with
  | nil =>
      have expanded :=
        S5_107.ListDerives.ofWord
          (derivesPowerExpansion (Word.singleton head))
      simpa [Word.toList_append, List.append_assoc] using
        expanded.append after
  | cons middleHead middleTail =>
      let middle := S5_107.listWordOfCons middleHead middleTail
      have expanded :=
        S5_107.ListDerives.ofWord
          (derivesAddInitialPairAcross head middle)
      simpa [middle, S5_107.listWordOfCons,
        Word.toList_append, Word.singleton, List.append_assoc] using
        expanded.append after

theorem derivesAddInitialPair
    (word : Word Nat) (headInTail : word.head ∈ word.tail) :
    Derives B3 word
      ((Word.singleton word.head ++ Word.singleton word.head) ++ word) := by
  cases word with
  | mk head tail =>
      have listDerivation :=
        listDerivesAddInitialPair head tail headInTail
      simpa [S5_107.listWordOfCons, Word.singleton,
        Word.append, List.append_assoc] using
        S5_107.ListDerives.toWord listDerivation

/-! ## Unrestricted guarded completeness -/

/-- Equal guarded period-two signatures are derivably equal in the exact
direct B3 orientation. -/
theorem derivesOfSameGuardedPeriodTwoSignature
    {left right : Word Nat}
    (same : SameGuardedPeriodTwoSignature left right) :
    Derives B3 left right := by
  have countIff := headCountOneIff same
  by_cases leftHeadSimple : left.toList.count left.head = 1
  · have rightHeadSimple : right.toList.count right.head = 1 :=
      countIff.mp leftHeadSimple
    have tailsEmpty :=
      tailNilIffOfSameSignature
        same leftHeadSimple rightHeadSimple
    cases left with
    | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
        have headsEqual : leftHead = rightHead := same.head
        subst rightHead
        cases leftTail with
        | nil =>
          have rightEmpty : rightTail = [] := tailsEmpty.mp rfl
          subst rightTail
          exact Derives.refl _
        | cons leftSecond leftRest =>
          cases rightTail with
          | nil =>
            have impossible : leftSecond :: leftRest = [] :=
              tailsEmpty.mpr rfl
            contradiction
          | cons rightSecond rightRest =>
            let leftSuffix : Word Nat :=
              Word.mk leftSecond leftRest
            let rightSuffix : Word Nat :=
              Word.mk rightSecond rightRest
            have leftHeadAbsent :
                leftHead ∉ leftSuffix.toList := by
              change leftHead ∉ leftSecond :: leftRest
              exact headNotMemTailOfCountOne
                (Word.mk leftHead (leftSecond :: leftRest))
                leftHeadSimple
            have rightHeadAbsent :
                leftHead ∉ rightSuffix.toList := by
              change leftHead ∉ rightSecond :: rightRest
              exact headNotMemTailOfCountOne
                (Word.mk leftHead (rightSecond :: rightRest))
                rightHeadSimple
            have wholeCore :
                (Identity.mk
                  (Word.singleton leftHead ++ leftSuffix)
                  (Word.singleton leftHead ++ rightSuffix)).SatisfiedBy
                    SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup.opposite := by
              simpa [leftSuffix, rightSuffix, Word.singleton,
                Word.append] using same.core
            have suffixCore :=
              suffixValidOfSimplePrefix
                SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup.opposite
                (4 : Fin 5) s5_614opLeftIdentity
                leftHead leftSuffix rightSuffix
                leftHeadAbsent rightHeadAbsent wholeCore
            have suffixDerivation :=
              edmundsBasisForS5_614op.2
                (Identity.mk leftSuffix rightSuffix) suffixCore
            have lifted :=
              liftEdmundsUnderPrefix suffixDerivation
                (Word.singleton leftHead) Word.singleton
            rw [bindSingleton, bindSingleton] at lifted
            simpa [leftSuffix, rightSuffix, Word.singleton,
              Word.append] using lifted
  · have rightHeadNotSimple :
        right.toList.count right.head ≠ 1 := by
      intro rightSimple
      exact leftHeadSimple (countIff.mpr rightSimple)
    have leftHeadInTail : left.head ∈ left.tail :=
      headMemTailOfCountNeOne left leftHeadSimple
    have rightHeadInTail : right.head ∈ right.tail :=
      headMemTailOfCountNeOne right rightHeadNotSimple
    have leftExpanded := derivesAddInitialPair left leftHeadInTail
    have rightExpanded := derivesAddInitialPair right rightHeadInTail
    have coreDerivation :=
      edmundsBasisForS5_614op.2
        (Identity.mk left right) same.core
    let guardPrefix :=
      Word.singleton left.head ++ Word.singleton left.head
    have lifted :=
      liftEdmundsUnderPrefix coreDerivation guardPrefix Word.singleton
    rw [bindSingleton, bindSingleton] at lifted
    have guarded :
        Derives B3
          (guardPrefix ++ left) (guardPrefix ++ right) := by
      simpa [guardPrefix, same.head] using lifted
    have rightContracted :
        Derives B3 (guardPrefix ++ right) right := by
      simpa [guardPrefix, same.head] using rightExpanded.symm
    exact leftExpanded.trans <| guarded.trans rightContracted

theorem derivesOfS2_4S5_614opValid
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup.opposite) :
    Derives B3 identity.lhs identity.rhs :=
  derivesOfSameGuardedPeriodTwoSignature <|
    sameGuardedPeriodTwoSignature_of_factorValidity
      identity leftValid rightValid

/-- The exact unrestricted intersection root used by d023. -/
def intersectionBasisS2_4S5_614op :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup.opposite
      B3 where
  leftModels := modelsS2_4
  rightModels := modelsS5_614op
  complete := derivesOfS2_4S5_614opValid

end SemigroupBasis.CoRoots.Order6L2DD023GuardedPeriodTwoB3

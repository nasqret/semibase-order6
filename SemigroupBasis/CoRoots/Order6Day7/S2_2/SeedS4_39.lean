import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415BrandtParityBridge
import SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank042
import SemigroupBasis.Examples.FirstLetterThreeNilpotentFour

/-!
# Unrestricted cyclic-two / first-letter-three-nilpotent rank-042 seed

The exact `S4_39` factor has three semantic strata: singleton words,
literal ordered quadratic words, and words of length at least three, whose
only retained variable is the literal head.  The actual cyclic-two factor
independently supplies every occurrence parity.

Frozen `xxx = xyy` exchanges a square behind a preserved head; frozen
`xxxyz = xyz` removes a head-square only while two nonempty blocks remain;
and frozen `xyz = xzy` permutes blocks behind the actual head.  These typed
edges lift the COMPLETE cyclic normalizer behind one fixed head and ahead
of two protected nonempty guards, preserving every derivation constructor.

Any long word receives two extra copies of its head, moved to the end.  The
guarded cyclic lift then identifies exactly the long-word suffixes with the
same parity.  The exact lower-factor separators handle short words without
claiming invalid singleton/quadratic contractions.  Both authenticated
six-element classes receive representative and opposite endpoints without
an owner premise.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank042.Seed

open SemigroupBasis
open SemigroupBasis.Examples

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | index + 3 => Word.singleton (index + 3)

/-- Consume fable msg-0325's mandatory FIRST checkpoint literally. -/
theorem rank040DoubledSandwichCheckpoint :
    Derives
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.basis
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.law10.lhs
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.law10.rhs :=
  Derives.fromBasis (by
    simp [SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.basis])

/-- The same checkpoint is already valid for arbitrary nonempty words. -/
theorem rank040DoubledSandwichCheckpoint_unrestricted
    (first second : Word Nat) :
    Derives
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.basis
      ((first ++ second) ++ first)
      ((((((first ++ second) ++ first) ++ second) ++ first) ++ second) ++
        first) :=
  SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.BrandtParityBridge.derivesJointSandwichExpansion
    first second

/-- The frozen head-square exchange is parity neutral on both factors. -/
theorem derivesHeadSquareExchange (head repeated : Word Nat) :
    Derives basis
      ((head ++ head) ++ head)
      ((head ++ repeated) ++ repeated) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 0]) (Word.mk 0 [1, 1]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted := Derives.subst primitive
    (instantiateThree head repeated repeated)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Remove a head-square only while two genuine nonempty guards remain. -/
theorem derivesGuardedHeadSquareContraction
    (head firstGuard secondGuard : Word Nat) :
    Derives basis
      ((((head ++ head) ++ head) ++ firstGuard) ++ secondGuard)
      ((head ++ firstGuard) ++ secondGuard) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 0, 1, 2])
        (Word.mk 0 [1, 2]) :=
    Derives.fromBasis (e := law02) (by simp [basis])
  have substituted := Derives.subst primitive
    (instantiateThree head firstGuard secondGuard)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Arbitrary blocks commute strictly BEHIND the retained nonempty head. -/
theorem derivesHeadProtectedSwap
    (head first second : Word Nat) :
    Derives basis
      ((head ++ first) ++ second)
      ((head ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2]) (Word.mk 0 [2, 1]) :=
    Derives.fromBasis (e := law04) (by simp [basis])
  have substituted := Derives.subst primitive
    (instantiateThree head first second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Cyclic square cancellation is sound only inside the fixed-head,
two-guard context.  The actual short-word stratum is never erased. -/
theorem derivesHeadProtectedCyclicCancellation
    (head repeated remaining firstGuard secondGuard : Word Nat) :
    Derives basis
      (((((head ++ repeated) ++ repeated) ++ remaining) ++ firstGuard) ++
        secondGuard)
      (((head ++ remaining) ++ firstGuard) ++ secondGuard) := by
  have exchange :=
    Derives.appendRight
      (derivesHeadSquareExchange head repeated).symm
      ((remaining ++ firstGuard) ++ secondGuard)
  have contraction :=
    derivesGuardedHeadSquareContraction head remaining
      (firstGuard ++ secondGuard)
  have exchangeAligned :
      Derives basis
        (((((head ++ repeated) ++ repeated) ++ remaining) ++ firstGuard) ++
          secondGuard)
        ((((head ++ head) ++ head) ++ remaining) ++
          (firstGuard ++ secondGuard)) := by
    simpa [Word.append_assoc] using exchange
  simpa [Word.append_assoc] using exchangeAligned.trans contraction

private theorem bind_append
    (first second : Word Nat) (substitution : Nat → Word Nat) :
    (first ++ second).bind substitution =
      first.bind substitution ++ second.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp

/-- C1 structural transport of the COMPLETE cyclic normalizer, after one
retained head and before two nonempty guards; every derivation constructor
and arbitrary substitution is preserved. -/
theorem liftCyclicAfterHeadBeforePair
    {left right : Word Nat}
    (derivation : Derives cyclicTwoBasis left right)
    (head firstGuard secondGuard : Word Nat)
    (substitution : Nat → Word Nat) :
    Derives basis
      (((head ++ left.bind substitution) ++ firstGuard) ++ secondGuard)
      (((head ++ right.bind substitution) ++ firstGuard) ++ secondGuard) := by
  induction derivation generalizing head firstGuard secondGuard substitution with
  | fromBasis member =>
      simp only [cyclicTwoBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [cyclicCommutativityLaw, cyclicXY, cyclicYX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.appendRight
            (derivesHeadProtectedSwap
              head (substitution 0) (substitution 1))
            (firstGuard ++ secondGuard)
      · simpa [cyclicCancellationLaw, cyclicXXY, cyclicY,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          derivesHeadProtectedCyclicCancellation head
            (substitution 0) (substitution 1)
            firstGuard secondGuard
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact (induction head firstGuard secondGuard substitution).symm
  | trans _ _ first second =>
      exact
        (first head firstGuard secondGuard substitution).trans
          (second head firstGuard secondGuard substitution)
  | prepend front _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction
          (head ++ front.bind substitution)
          firstGuard secondGuard substitution
  | appendRight _ suffix induction =>
      simpa [bind_append, Word.append_assoc] using
        induction head
          (suffix.bind substitution ++ firstGuard)
          secondGuard substitution
  | subst _ next induction =>
      simpa [bind_bind] using
        induction head firstGuard secondGuard
          (fun letter => (next letter).bind substitution)

/-- A word already in the genuine long stratum can gain two protected
copies of its ACTUAL head at the far right, without crossing a short stratum. -/
theorem derivesInsertTerminalHeadPair
    (head middle final : Word Nat) :
    Derives basis
      ((head ++ middle) ++ final)
      ((((head ++ middle) ++ final) ++ head) ++ head) := by
  have inserted :=
    (derivesGuardedHeadSquareContraction head middle final).symm
  have moved :=
    derivesHeadProtectedSwap head (head ++ head) (middle ++ final)
  have insertedAligned :
      Derives basis
        ((head ++ middle) ++ final)
        ((head ++ (head ++ head)) ++ (middle ++ final)) := by
    simpa [Word.append_assoc] using inserted
  simpa [Word.append_assoc] using insertedAligned.trans moved

/-- The actual cyclic factor forces exactly the suffix parity vector once
the true lower-factor head has been identified. -/
theorem suffixParity_of_sameHead
    (head : Nat) (left right : Word Nat)
    (wholeParity :
      ∀ letter,
        (head :: left.toList).count letter % 2 =
          (head :: right.toList).count letter % 2) :
    ∀ letter,
      left.toList.count letter % 2 = right.toList.count letter % 2 := by
  intro letter
  have parity := wholeParity letter
  by_cases same : letter = head
  · subst letter
    simp only [List.count_cons_self] at parity
    omega
  · simpa [List.count_cons_of_ne (Ne.symm same)] using parity

/-- Exact unrestricted derivation for any two genuine long words with the
same ACTUAL head and the same cyclic occurrence-parity vector. -/
theorem derivesLongOfSameHeadParity
    (head leftFirst leftSecond rightFirst rightSecond : Nat)
    (leftRest rightRest : List Nat)
    (sameParity :
      ∀ letter,
        (head :: leftFirst :: leftSecond :: leftRest).count letter % 2 =
          (head :: rightFirst :: rightSecond :: rightRest).count letter % 2) :
    Derives basis
      (Word.mk head (leftFirst :: leftSecond :: leftRest))
      (Word.mk head (rightFirst :: rightSecond :: rightRest)) := by
  let leftSuffix : Word Nat := ⟨leftFirst, leftSecond :: leftRest⟩
  let rightSuffix : Word Nat := ⟨rightFirst, rightSecond :: rightRest⟩
  have suffixParity :
      SemigroupBasis.CoRoots.S5_441Invariant.SameOccurrenceParity
        leftSuffix rightSuffix := by
    apply suffixParity_of_sameHead head leftSuffix rightSuffix
    simpa [leftSuffix, rightSuffix, Word.toList] using sameParity
  have catalogueValid :=
    SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.BrandtParityBridge.leftValid_of_sameOccurrenceParity
      (Identity.mk leftSuffix rightSuffix) suffixParity
  have cyclicValid :
      (Identity.mk leftSuffix rightSuffix).SatisfiedBy cyclicTwo.semigroup := by
    rw [← SemigroupBasis.CoRoots.S5_441Invariant.catalogueS2_2_table_eq_cyclicTwo]
    exact catalogueValid
  have cyclicDerivation :=
    cyclicTwoBasis_complete.2 (Identity.mk leftSuffix rightSuffix) cyclicValid
  have guarded :=
    liftCyclicAfterHeadBeforePair cyclicDerivation
      (Word.singleton head) (Word.singleton head)
      (Word.singleton head) Word.singleton
  rw [bind_singleton, bind_singleton] at guarded
  have leftInsert :=
    derivesInsertTerminalHeadPair
      (Word.singleton head) (Word.singleton leftFirst)
      (Word.mk leftSecond leftRest)
  have rightInsert :=
    derivesInsertTerminalHeadPair
      (Word.singleton head) (Word.singleton rightFirst)
      (Word.mk rightSecond rightRest)
  simpa [leftSuffix, rightSuffix, Word.singleton, Word.append,
    List.append_assoc] using
    leftInsert.trans (guarded.trans rightInsert.symm)

private theorem rightValid_as_model
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.SatisfiedBy firstLetterThreeNilpotentFour.semigroup := by
  exact valid

/-- Publicly expose the imported long-word evaluator with ordinary `Word.mk`
syntax; the upstream presentation uses a private word constructor. -/
private theorem rightModel_long_eval
    (valuation : Nat → Fin 4)
    (head first second : Nat) (remaining : List Nat) :
    firstLetterThreeNilpotentFour.semigroup.eval valuation
        (Word.mk head (first :: second :: remaining)) =
      if valuation head = (3 : Fin 4) then (3 : Fin 4) else (0 : Fin 4) := by
  exact firstLetterThreeNilpotentEval_long
    valuation head first second remaining

/-- The frozen pair is genuinely complete on EVERY Nat-variable identity;
the singleton and ordered-quadratic cases remain literal, and the long case
uses the unrestricted protected cyclic transport. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have rightModel := rightValid_as_model identity rightValid
  have parity :=
    SemigroupBasis.CoRoots.S5_441Invariant.sameOccurrenceParity_of_s2_2_valid
      identity leftValid
  cases identity with
  | mk left right =>
      cases left with
      | mk leftHead leftTail =>
          cases right with
          | mk rightHead rightTail =>
              cases leftTail with
              | nil =>
                  cases rightTail with
                  | nil =>
                      have heads : leftHead = rightHead := by
                        apply Decidable.byContradiction
                        intro different
                        let valuation : Nat → Fin 4 := fun letter =>
                          if letter = leftHead then (3 : Fin 4) else (0 : Fin 4)
                        have evaluated := rightModel valuation
                        change valuation leftHead = valuation rightHead
                          at evaluated
                        simp [valuation, Ne.symm different] at evaluated
                      subst rightHead
                      exact Derives.refl _
                  | cons rightFirst rightRemaining =>
                      cases rightRemaining with
                      | nil =>
                          have evaluated := rightModel (fun _ => (2 : Fin 4))
                          change (2 : Fin 4) = 1 at evaluated
                          omega
                      | cons rightSecond rightRest =>
                          have evaluated := rightModel (fun _ => (2 : Fin 4))
                          have longEval :=
                            rightModel_long_eval
                              (fun _ => (2 : Fin 4))
                              rightHead rightFirst rightSecond rightRest
                          change
                            (2 : Fin 4) =
                              firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (Word.mk rightHead
                                  (rightFirst :: rightSecond :: rightRest))
                            at evaluated
                          rw [longEval] at evaluated
                          simp at evaluated
              | cons leftFirst leftRemaining =>
                  cases leftRemaining with
                  | nil =>
                      cases rightTail with
                      | nil =>
                          have evaluated := rightModel (fun _ => (2 : Fin 4))
                          change (1 : Fin 4) = 2 at evaluated
                          omega
                      | cons rightFirst rightRemaining =>
                          cases rightRemaining with
                          | nil =>
                              have same :=
                                firstLetterThreeNilpotentValidPair_eq rightModel
                              rcases same with ⟨heads, seconds⟩
                              subst rightHead
                              subst rightFirst
                              exact Derives.refl _
                          | cons rightSecond rightRest =>
                              have evaluated :=
                                rightModel (fun _ => (2 : Fin 4))
                              have longEval :=
                                rightModel_long_eval
                                  (fun _ => (2 : Fin 4))
                                  rightHead rightFirst rightSecond rightRest
                              change
                                (1 : Fin 4) =
                                  firstLetterThreeNilpotentFour.semigroup.eval
                                    (fun _ => (2 : Fin 4))
                                    (Word.mk rightHead
                                      (rightFirst :: rightSecond :: rightRest))
                                at evaluated
                              rw [longEval] at evaluated
                              simp at evaluated
                  | cons leftSecond leftRest =>
                      cases rightTail with
                      | nil =>
                          have evaluated := rightModel (fun _ => (2 : Fin 4))
                          have longEval :=
                            rightModel_long_eval
                              (fun _ => (2 : Fin 4))
                              leftHead leftFirst leftSecond leftRest
                          change
                            firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (Word.mk leftHead
                                  (leftFirst :: leftSecond :: leftRest)) =
                              (2 : Fin 4)
                            at evaluated
                          rw [longEval] at evaluated
                          simp at evaluated
                      | cons rightFirst rightRemaining =>
                          cases rightRemaining with
                          | nil =>
                              have evaluated :=
                                rightModel (fun _ => (2 : Fin 4))
                              have longEval :=
                                rightModel_long_eval
                                  (fun _ => (2 : Fin 4))
                                  leftHead leftFirst leftSecond leftRest
                              change
                                firstLetterThreeNilpotentFour.semigroup.eval
                                    (fun _ => (2 : Fin 4))
                                    (Word.mk leftHead
                                      (leftFirst :: leftSecond :: leftRest)) =
                                  (1 : Fin 4)
                                at evaluated
                              rw [longEval] at evaluated
                              simp at evaluated
                          | cons rightSecond rightRest =>
                              have heads : leftHead = rightHead := by
                                apply Decidable.byContradiction
                                intro different
                                let valuation : Nat → Fin 4 := fun letter =>
                                  if letter = leftHead then 3 else 0
                                have evaluated := rightModel valuation
                                change
                                  firstLetterThreeNilpotentFour.semigroup.eval
                                      valuation
                                      (Word.mk leftHead
                                        (leftFirst :: leftSecond :: leftRest)) =
                                    firstLetterThreeNilpotentFour.semigroup.eval
                                      valuation
                                      (Word.mk rightHead
                                        (rightFirst :: rightSecond :: rightRest))
                                  at evaluated
                                rw [rightModel_long_eval,
                                  rightModel_long_eval] at evaluated
                                simp [valuation, Ne.symm different] at evaluated
                              subst rightHead
                              exact derivesLongOfSameHeadParity
                                leftHead leftFirst leftSecond
                                rightFirst rightSecond leftRest rightRest
                                (by
                                  intro letter
                                  simpa [Word.toList] using parity letter)

/-- Unrestricted factor-pair completeness, with NO additional owner premise. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derivesOfFactorValid

/-- Reviewed quotient normalization only after actual pair completeness. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_5496_representative_basis :
    BasisFor S6_5496.table.semigroup basis :=
  S6_5496.representative_basis_of_normalizer normalizer

theorem s6_5496_opposite_basis :
    BasisFor S6_5496.table.semigroup.opposite (reversedBasis basis) :=
  S6_5496.opposite_basis_of_normalizer normalizer

theorem s6_5507_representative_basis :
    BasisFor S6_5507.table.semigroup basis :=
  S6_5507.representative_basis_of_normalizer normalizer

theorem s6_5507_opposite_basis :
    BasisFor S6_5507.table.semigroup.opposite (reversedBasis basis) :=
  S6_5507.opposite_basis_of_normalizer normalizer

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank042.Seed

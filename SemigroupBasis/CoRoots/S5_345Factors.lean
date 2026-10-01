import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.Examples.LeftRegularBandThree
import SemigroupBasis.CoRoots.S5_345Syntax
import SemigroupBasis.Generated.CatalogueOrder5Part03
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_345Factors

open SemigroupBasis
open SemigroupBasis.Examples

private def semanticLrbListEval
    (valuation : Nat → Fin 3) (xs : List Nat) : Fin 3 :=
  xs.foldl
    (fun current x => leftRegularBandThreeMul current (valuation x)) 1

private theorem semanticLrbEval_eq_listEval
    (valuation : Nat → Fin 3) (w : Word Nat) :
    leftRegularBandThree.semigroup.eval valuation w =
      semanticLrbListEval valuation w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              leftRegularBandThreeMul current (valuation x))
            (valuation head) =
          tail.foldl
            (fun current x =>
              leftRegularBandThreeMul current (valuation x))
            (leftRegularBandThreeMul 1 (valuation head))
      rw [show leftRegularBandThreeMul 1 (valuation head) =
          valuation head by
        simp [leftRegularBandThreeMul]]

private theorem semanticLrbFold_left_zero
    (valuation : Nat → Fin 3) (a : Fin 3) (ha : a ≠ 1)
    (xs : List Nat) :
    xs.foldl
        (fun current x => leftRegularBandThreeMul current (valuation x)) a =
      a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [show leftRegularBandThreeMul a (valuation x) = a by
        simp [leftRegularBandThreeMul, ha]]
      exact ih

private theorem semanticLrbListEval_cons_of_ne_one
    (valuation : Nat → Fin 3) (x : Nat) (xs : List Nat)
    (hx : valuation x ≠ 1) :
    semanticLrbListEval valuation (x :: xs) = valuation x := by
  unfold semanticLrbListEval
  simp only [List.foldl_cons]
  rw [show leftRegularBandThreeMul 1 (valuation x) = valuation x by
    simp [leftRegularBandThreeMul]]
  exact semanticLrbFold_left_zero valuation (valuation x) hx xs

private theorem semanticLrbListEval_cons_of_eq_one
    (valuation : Nat → Fin 3) (x : Nat) (xs : List Nat)
    (hx : valuation x = 1) :
    semanticLrbListEval valuation (x :: xs) =
      semanticLrbListEval valuation xs := by
  simp [semanticLrbListEval, leftRegularBandThreeMul, hx]

private theorem semanticLrbFold_congr
    (v₁ v₂ : Nat → Fin 3) :
    ∀ (xs : List Nat) (acc : Fin 3),
      (∀ x, x ∈ xs → v₁ x = v₂ x) →
      xs.foldl
          (fun current x =>
            leftRegularBandThreeMul current (v₁ x)) acc =
        xs.foldl
          (fun current x =>
            leftRegularBandThreeMul current (v₂ x)) acc
  | [], _, _ => rfl
  | x :: xs, acc, agree => by
      simp only [List.foldl_cons]
      rw [agree x (List.Mem.head xs)]
      exact semanticLrbFold_congr v₁ v₂ xs
        (leftRegularBandThreeMul acc (v₂ x))
        (fun y hy => agree y (List.Mem.tail x hy))

private theorem semanticLrbListEval_congr
    (v₁ v₂ : Nat → Fin 3) (xs : List Nat)
    (agree : ∀ x, x ∈ xs → v₁ x = v₂ x) :
    semanticLrbListEval v₁ xs = semanticLrbListEval v₂ xs :=
  semanticLrbFold_congr v₁ v₂ xs 1 agree

private theorem semanticLrbNodup_eq_of_eval_eq :
    ∀ {xs ys : List Nat},
      xs.Nodup →
      ys.Nodup →
      (∀ valuation : Nat → Fin 3,
        semanticLrbListEval valuation xs =
          semanticLrbListEval valuation ys) →
      xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, equalEval => by
      let valuation : Nat → Fin 3 :=
        fun z => if z = y then 0 else 1
      have h := equalEval valuation
      have rightValue :
          semanticLrbListEval valuation (y :: ys) = 0 := by
        simpa [valuation] using
          semanticLrbListEval_cons_of_ne_one
            valuation y ys (by simp [valuation])
      have leftValue : semanticLrbListEval valuation [] = 1 := rfl
      rw [leftValue, rightValue] at h
      exact False.elim ((by decide : (1 : Fin 3) ≠ 0) h)
  | x :: xs, [], _, _, equalEval => by
      let valuation : Nat → Fin 3 :=
        fun z => if z = x then 0 else 1
      have h := equalEval valuation
      have leftValue :
          semanticLrbListEval valuation (x :: xs) = 0 := by
        simpa [valuation] using
          semanticLrbListEval_cons_of_ne_one
            valuation x xs (by simp [valuation])
      have rightValue : semanticLrbListEval valuation [] = 1 := rfl
      rw [leftValue, rightValue] at h
      exact False.elim ((by decide : (0 : Fin 3) ≠ 1) h)
  | x :: xs, y :: ys, nodupX, nodupY, equalEval => by
      have heads : x = y := by
        apply Decidable.byContradiction
        intro hxy
        let valuation : Nat → Fin 3 :=
          fun z => if z = x then 0 else if z = y then 2 else 1
        have h := equalEval valuation
        have leftValue :
            semanticLrbListEval valuation (x :: xs) = 0 := by
          simpa [valuation] using
            semanticLrbListEval_cons_of_ne_one
              valuation x xs (by simp [valuation])
        have rightValue :
            semanticLrbListEval valuation (y :: ys) = 2 := by
          simpa [valuation, Ne.symm hxy] using
            semanticLrbListEval_cons_of_ne_one
              valuation y ys (by simp [valuation, Ne.symm hxy])
        rw [leftValue, rightValue] at h
        exact (by decide : (0 : Fin 3) ≠ 2) h
      subst y
      have xNotMemXs : x ∉ xs := (List.nodup_cons.mp nodupX).1
      have xNotMemYs : x ∉ ys := (List.nodup_cons.mp nodupY).1
      have tailsEqual :
          ∀ valuation : Nat → Fin 3,
            semanticLrbListEval valuation xs =
              semanticLrbListEval valuation ys := by
        intro valuation
        let masked : Nat → Fin 3 :=
          fun z => if z = x then 1 else valuation z
        have fullEqual := equalEval masked
        have maskedX : masked x = 1 := by simp [masked]
        rw [semanticLrbListEval_cons_of_eq_one masked x xs maskedX,
          semanticLrbListEval_cons_of_eq_one masked x ys maskedX] at fullEqual
        calc
          semanticLrbListEval valuation xs =
              semanticLrbListEval masked xs := by
                apply semanticLrbListEval_congr
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply xNotMemXs
                  simpa [h] using hz
                simp [masked, hzx]
          _ = semanticLrbListEval masked ys := fullEqual
          _ = semanticLrbListEval valuation ys := by
                apply semanticLrbListEval_congr
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply xNotMemYs
                  simpa [h] using hz
                simp [masked, hzx]
      congr 1
      exact semanticLrbNodup_eq_of_eval_eq
        (List.nodup_cons.mp nodupX).2
        (List.nodup_cons.mp nodupY).2 tailsEqual

/-- A valid identity of the three-element left regular band preserves the
sequence of first occurrences. -/
theorem leftRegularBandThreeValid_firstOccurrenceSequence_eq
    (e : Identity Nat)
    (valid : e.SatisfiedBy leftRegularBandThree.semigroup) :
    firstOccurrenceSequence e.lhs.toList =
      firstOccurrenceSequence e.rhs.toList := by
  have lhsNormal := lrbDerivesNormal e.lhs
  have rhsNormal := lrbDerivesNormal e.rhs
  cases hl : firstOccurrenceSequence e.lhs.toList with
  | nil =>
      cases e.lhs with
      | mk head tail =>
          simp [Word.toList, firstOccurrenceSequence] at hl
  | cons x xs =>
      cases hr : firstOccurrenceSequence e.rhs.toList with
      | nil =>
          cases e.rhs with
          | mk head tail =>
              simp [Word.toList, firstOccurrenceSequence] at hr
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          have reducedEvalEqual :
              ∀ valuation : Nat → Fin 3,
                semanticLrbListEval valuation (x :: xs) =
                  semanticLrbListEval valuation (y :: ys) := by
            intro valuation
            have lhsSound :=
              lhsNormal.sound leftRegularBandThreeBasis_models valuation
            have rhsSound :=
              rhsNormal.sound leftRegularBandThreeBasis_models valuation
            rw [semanticLrbEval_eq_listEval] at lhsSound rhsSound
            exact lhsSound.symm.trans ((valid valuation).trans rhsSound)
          have lhsNodup : (x :: xs).Nodup := by
            rw [← hl]
            exact firstOccurrenceSequence_nodup e.lhs.toList
          have rhsNodup : (y :: ys).Nodup := by
            rw [← hr]
            exact firstOccurrenceSequence_nodup e.rhs.toList
          have reducedEqual : x :: xs = y :: ys :=
            semanticLrbNodup_eq_of_eval_eq
              lhsNodup rhsNodup reducedEvalEqual
          simpa [hl, hr] using reducedEqual

private theorem final_wordOfPrefixFinal
    (pref : List Nat) (final : Nat) :
    (wordOfPrefixFinal pref final).final = final := by
  induction pref with
  | nil => rfl
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact ih

private theorem simpleFinal_wordOfPrefixFinal_iff
    (pref : List Nat) (final z : Nat) :
    SemigroupBasis.CoRoots.S5_107.SimpleFinal
        (wordOfPrefixFinal pref final) z ↔
      final = z ∧ z ∉ pref := by
  change
    ((wordOfPrefixFinal pref final).toList.count z = 1 ∧
        (wordOfPrefixFinal pref final).final = z) ↔
      final = z ∧ z ∉ pref
  rw [final_wordOfPrefixFinal]
  constructor
  · rintro ⟨countOne, finalEq⟩
    subst final
    rw [toList_wordOfPrefixFinal, List.count_append] at countOne
    have prefixZero : pref.count z = 0 := by
      have countEquation : pref.count z + 1 = 1 := by
        simpa using countOne
      omega
    exact ⟨rfl, List.count_eq_zero.mp prefixZero⟩
  · rintro ⟨finalEq, prefixAbsent⟩
    subst final
    constructor
    · rw [toList_wordOfPrefixFinal, List.count_append]
      simp [List.count_eq_zero.mpr prefixAbsent]
    · rfl

private theorem simpleFinal_iff_split
    (w : Word Nat) (z : Nat) :
    SemigroupBasis.CoRoots.S5_107.SimpleFinal w z ↔
      (splitPrefixFinal w).2 = z ∧
        z ∉ (splitPrefixFinal w).1 := by
  let split := splitPrefixFinal w
  have reconstruct :
      wordOfPrefixFinal split.1 split.2 = w :=
    wordOfPrefixFinal_split w
  change
    SemigroupBasis.CoRoots.S5_107.SimpleFinal w z ↔
      split.2 = z ∧ z ∉ split.1
  rw [← reconstruct]
  exact simpleFinal_wordOfPrefixFinal_iff split.1 split.2 z

private def semanticFinalSeparator (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 1 else 2

private def semanticFinalValue
    (z : Nat) (pref : List Nat) (final : Nat) : Fin 3 :=
  if z ∈ pref then 0 else if final = z then 1 else 2

private theorem finalMarkerEval_semanticSeparator
    (z : Nat) (pref : List Nat) (final : Nat) :
    finalMarkerThree.semigroup.eval (semanticFinalSeparator z)
        (wordOfPrefixFinal pref final) =
      semanticFinalValue z pref final := by
  induction pref with
  | nil =>
      simp [wordOfPrefixFinal, semanticFinalSeparator,
        semanticFinalValue]
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append, ih]
      by_cases hx : x = z
      · subst x
        simp [semanticFinalSeparator, semanticFinalValue,
          finalMarkerThree, FiniteTable.semigroup, finalMarkerThreeMul]
      · simp [semanticFinalSeparator, semanticFinalValue,
          finalMarkerThree, FiniteTable.semigroup, finalMarkerThreeMul,
          hx, Ne.symm hx]

private theorem semanticFinalValue_eq_one_iff
    (z : Nat) (pref : List Nat) (final : Nat) :
    semanticFinalValue z pref final = (1 : Fin 3) ↔
      final = z ∧ z ∉ pref := by
  by_cases hpref : z ∈ pref
  · simp [semanticFinalValue, hpref]
  · by_cases hfinal : final = z
    · simp [semanticFinalValue, hpref, hfinal]
    · simp [semanticFinalValue, hpref, hfinal]

private theorem finalMarkerThreeValid_splitSimpleFinal_iff
    (e : Identity Nat)
    (valid : e.SatisfiedBy finalMarkerThree.semigroup)
    (z : Nat) :
    ((splitPrefixFinal e.lhs).2 = z ∧
        z ∉ (splitPrefixFinal e.lhs).1) ↔
      ((splitPrefixFinal e.rhs).2 = z ∧
        z ∉ (splitPrefixFinal e.rhs).1) := by
  let lhsSplit := splitPrefixFinal e.lhs
  let rhsSplit := splitPrefixFinal e.rhs
  have lhsReconstruct :
      wordOfPrefixFinal lhsSplit.1 lhsSplit.2 = e.lhs :=
    wordOfPrefixFinal_split e.lhs
  have rhsReconstruct :
      wordOfPrefixFinal rhsSplit.1 rhsSplit.2 = e.rhs :=
    wordOfPrefixFinal_split e.rhs
  have evaluated := valid (semanticFinalSeparator z)
  rw [← lhsReconstruct, ← rhsReconstruct,
    finalMarkerEval_semanticSeparator,
    finalMarkerEval_semanticSeparator] at evaluated
  change
    (lhsSplit.2 = z ∧ z ∉ lhsSplit.1) ↔
      (rhsSplit.2 = z ∧ z ∉ rhsSplit.1)
  constructor
  · intro lhsSimple
    have lhsOne :
        semanticFinalValue z lhsSplit.1 lhsSplit.2 = (1 : Fin 3) :=
      (semanticFinalValue_eq_one_iff z lhsSplit.1 lhsSplit.2).2
        lhsSimple
    exact
      (semanticFinalValue_eq_one_iff z rhsSplit.1 rhsSplit.2).1
        (evaluated.symm.trans lhsOne)
  · intro rhsSimple
    have rhsOne :
        semanticFinalValue z rhsSplit.1 rhsSplit.2 = (1 : Fin 3) :=
      (semanticFinalValue_eq_one_iff z rhsSplit.1 rhsSplit.2).2
        rhsSimple
    exact
      (semanticFinalValue_eq_one_iff z lhsSplit.1 lhsSplit.2).1
        (evaluated.trans rhsOne)

/-- A valid identity of `finalMarkerThree` preserves the globally simple
final variable predicate used by the `S5_345` syntax layer. -/
theorem finalMarkerThreeValid_simpleFinal_iff
    (e : Identity Nat)
    (valid : e.SatisfiedBy finalMarkerThree.semigroup)
    (z : Nat) :
    SemigroupBasis.CoRoots.S5_107.SimpleFinal e.lhs z ↔
      SemigroupBasis.CoRoots.S5_107.SimpleFinal e.rhs z := by
  rw [simpleFinal_iff_split, simpleFinal_iff_split]
  exact finalMarkerThreeValid_splitSimpleFinal_iff e valid z

/-- A valid identity of `finalMarkerThree` preserves its optional simple
final variable. -/
theorem finalMarkerThreeValid_simpleFinalVariable_eq
    (e : Identity Nat)
    (valid : e.SatisfiedBy finalMarkerThree.semigroup) :
    SemigroupBasis.CoRoots.S5_345.simpleFinalVariable e.lhs =
      SemigroupBasis.CoRoots.S5_345.simpleFinalVariable e.rhs := by
  apply Option.ext
  intro z
  rw [SemigroupBasis.CoRoots.S5_345.simpleFinalVariable_eq_some_iff,
    SemigroupBasis.CoRoots.S5_345.simpleFinalVariable_eq_some_iff]
  exact finalMarkerThreeValid_simpleFinal_iff e valid z

namespace S5_345

def leftRegularBandQuotient :
    SplitSurjection Generated.Catalogue.S5_345.table.semigroup
      leftRegularBandThree.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨1, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    exact by decide +revert
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨4, by decide⟩ else ⟨3, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

def commutativeExponentQuotient :
    SplitSurjection Generated.Catalogue.S5_345.table.semigroup
      commutativeExponentThree.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨2, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

def finalMarkerQuotient :
    SplitSurjection Generated.Catalogue.S5_345.table.semigroup
      finalMarkerThree.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_leftRegularBandThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_345.table.semigroup) :
    e.SatisfiedBy leftRegularBandThree.semigroup :=
  leftRegularBandQuotient.pushforwardIdentity e valid

theorem valid_commutativeExponentThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_345.table.semigroup) :
    e.SatisfiedBy commutativeExponentThree.semigroup :=
  commutativeExponentQuotient.pushforwardIdentity e valid

theorem valid_finalMarkerThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_345.table.semigroup) :
    e.SatisfiedBy finalMarkerThree.semigroup :=
  finalMarkerQuotient.pushforwardIdentity e valid

theorem valid_firstOccurrenceSequence_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_345.table.semigroup) :
    firstOccurrenceSequence e.lhs.toList =
      firstOccurrenceSequence e.rhs.toList :=
  leftRegularBandThreeValid_firstOccurrenceSequence_eq e
    (valid_leftRegularBandThree e valid)

theorem valid_capped_count_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_345.table.semigroup) :
    ∀ z, min (e.lhs.toList.count z) 2 =
      min (e.rhs.toList.count z) 2 :=
  exponentValid_capped_count_eq e
    (valid_commutativeExponentThree e valid)

theorem valid_simpleFinalVariable_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_345.table.semigroup) :
    SemigroupBasis.CoRoots.S5_345.simpleFinalVariable e.lhs =
      SemigroupBasis.CoRoots.S5_345.simpleFinalVariable e.rhs :=
  finalMarkerThreeValid_simpleFinalVariable_eq e
    (valid_finalMarkerThree e valid)

end S5_345

namespace S5_374

def leftRegularBandQuotient :
    SplitSurjection Generated.Catalogue.S5_374.table.semigroup
      leftRegularBandThree.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨1, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    exact by decide +revert
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨4, by decide⟩ else ⟨3, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

def commutativeExponentQuotient :
    SplitSurjection Generated.Catalogue.S5_374.table.semigroup
      commutativeExponentThree.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

def finalMarkerQuotient :
    SplitSurjection Generated.Catalogue.S5_374.table.semigroup
      finalMarkerThree.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨2, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_leftRegularBandThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_374.table.semigroup) :
    e.SatisfiedBy leftRegularBandThree.semigroup :=
  leftRegularBandQuotient.pushforwardIdentity e valid

theorem valid_commutativeExponentThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_374.table.semigroup) :
    e.SatisfiedBy commutativeExponentThree.semigroup :=
  commutativeExponentQuotient.pushforwardIdentity e valid

theorem valid_finalMarkerThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_374.table.semigroup) :
    e.SatisfiedBy finalMarkerThree.semigroup :=
  finalMarkerQuotient.pushforwardIdentity e valid

theorem valid_firstOccurrenceSequence_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_374.table.semigroup) :
    firstOccurrenceSequence e.lhs.toList =
      firstOccurrenceSequence e.rhs.toList :=
  leftRegularBandThreeValid_firstOccurrenceSequence_eq e
    (valid_leftRegularBandThree e valid)

theorem valid_capped_count_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_374.table.semigroup) :
    ∀ z, min (e.lhs.toList.count z) 2 =
      min (e.rhs.toList.count z) 2 :=
  exponentValid_capped_count_eq e
    (valid_commutativeExponentThree e valid)

theorem valid_simpleFinalVariable_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_374.table.semigroup) :
    SemigroupBasis.CoRoots.S5_345.simpleFinalVariable e.lhs =
      SemigroupBasis.CoRoots.S5_345.simpleFinalVariable e.rhs :=
  finalMarkerThreeValid_simpleFinalVariable_eq e
    (valid_finalMarkerThree e valid)

end S5_374

namespace S5_593

def leftRegularBandQuotient :
    SplitSurjection Generated.Catalogue.S5_593.table.semigroup
      leftRegularBandThree.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨2, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨1, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨4, by decide⟩ else ⟨2, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

def commutativeExponentQuotient :
    SplitSurjection Generated.Catalogue.S5_593.table.semigroup
      commutativeExponentThree.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨1, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

def finalMarkerQuotient :
    SplitSurjection Generated.Catalogue.S5_593.table.semigroup
      finalMarkerThree.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_leftRegularBandThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_593.table.semigroup) :
    e.SatisfiedBy leftRegularBandThree.semigroup :=
  leftRegularBandQuotient.pushforwardIdentity e valid

theorem valid_commutativeExponentThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_593.table.semigroup) :
    e.SatisfiedBy commutativeExponentThree.semigroup :=
  commutativeExponentQuotient.pushforwardIdentity e valid

theorem valid_finalMarkerThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_593.table.semigroup) :
    e.SatisfiedBy finalMarkerThree.semigroup :=
  finalMarkerQuotient.pushforwardIdentity e valid

theorem valid_firstOccurrenceSequence_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_593.table.semigroup) :
    firstOccurrenceSequence e.lhs.toList =
      firstOccurrenceSequence e.rhs.toList :=
  leftRegularBandThreeValid_firstOccurrenceSequence_eq e
    (valid_leftRegularBandThree e valid)

theorem valid_capped_count_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_593.table.semigroup) :
    ∀ z, min (e.lhs.toList.count z) 2 =
      min (e.rhs.toList.count z) 2 :=
  exponentValid_capped_count_eq e
    (valid_commutativeExponentThree e valid)

theorem valid_simpleFinalVariable_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_593.table.semigroup) :
    SemigroupBasis.CoRoots.S5_345.simpleFinalVariable e.lhs =
      SemigroupBasis.CoRoots.S5_345.simpleFinalVariable e.rhs :=
  finalMarkerThreeValid_simpleFinalVariable_eq e
    (valid_finalMarkerThree e valid)

end S5_593

end SemigroupBasis.CoRoots.S5_345Factors

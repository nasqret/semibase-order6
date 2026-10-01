import SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_530RelativeLift
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opProfile
import SemigroupBasis.CoRoots.S5_530

/-!
# Unrestricted one/two/three final-occurrence semantics for rank 103

The actual `S5_530` factor proves equality of first-occurrence order and
all multiplicities capped at three. A fresh simple final is stripped using
the exact catalogue identity element. A twice-occurring final is handled
separately: removing its terminal occurrence preserves first-occurrence
order and reduces both exact multiplicities to one. This distinct branch is
essential because duplicating a twice-occurring final is false.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_530

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev lowerBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.S5_530.s5_530Basis

private abbrev rightFactor :=
  SemigroupBasis.Generated.Catalogue.S5_530.table.semigroup

private theorem capped_three_eq_one_iff (count : Nat) :
    Nat.min count 3 = 1 ↔ count = 1 := by
  simp only [Nat.min_def]
  split <;> omega

/-- The actual complete lower calculus preserves final simplicity. -/
theorem finalCountOneIff_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightFactor)
    (finalEq : identity.lhs.final = identity.rhs.final) :
    identity.lhs.toList.count identity.lhs.final = 1 ↔
      identity.rhs.toList.count identity.rhs.final = 1 := by
  have capped :=
    SemigroupBasis.CoRoots.S5_530.valid_capped_count_eq
      identity valid identity.lhs.final
  have aligned :
      Nat.min (identity.lhs.toList.count identity.lhs.final) 3 =
        Nat.min (identity.rhs.toList.count identity.rhs.final) 3 := by
    simpa [SemigroupBasis.CoRoots.S5_530.s5_530Exponent,
      finalEq] using capped
  constructor
  · intro simple
    apply (capped_three_eq_one_iff _).mp
    rw [← aligned]
    exact (capped_three_eq_one_iff _).mpr simple
  · intro simple
    apply (capped_three_eq_one_iff _).mp
    rw [aligned]
    exact (capped_three_eq_one_iff _).mpr simple

/-- The exact cap-three factor invariant aligns the common final variable. -/
theorem finalCappedCounts_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightFactor)
    (finalEq : identity.lhs.final = identity.rhs.final) :
    Nat.min (identity.lhs.toList.count identity.lhs.final) 3 =
      Nat.min (identity.rhs.toList.count identity.rhs.final) 3 := by
  simpa [SemigroupBasis.CoRoots.S5_530.s5_530Exponent,
    finalEq] using
    SemigroupBasis.CoRoots.S5_530.valid_capped_count_eq
      identity valid identity.lhs.final

private theorem splitFinal_not_mem_stem_of_count_one
    (word : Word Nat)
    (countOne : word.toList.count word.final = 1) :
    (splitPrefixFinal word).2 ∉ (splitPrefixFinal word).1 := by
  have countOne' :
      word.toList.count (splitPrefixFinal word).2 = 1 := by
    simpa [split_final_eq] using countOne
  rw [toList_eq_splitPrefixFinal, List.count_append] at countOne'
  simp only [List.count_singleton_self] at countOne'
  have stemCount :
      (splitPrefixFinal word).1.count (splitPrefixFinal word).2 = 0 := by
    omega
  exact List.count_eq_zero.mp stemCount

/-- A singleton on one side forces a singleton on the other simple-final side. -/
theorem splitStem_nil_of_sameLastSupport
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.SameLastSupport left right)
    (rightSimple : right.toList.count right.final = 1)
    (leftStemEmpty : (splitPrefixFinal left).1 = []) :
    (splitPrefixFinal right).1 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter rightStemMember
  have rightMember : letter ∈ right.toList := by
    rw [toList_eq_splitPrefixFinal]
    exact List.mem_append_left _ rightStemMember
  have leftMember : letter ∈ left.toList :=
    (same.support_eq letter).2 rightMember
  have letterIsLeftFinal : letter = (splitPrefixFinal left).2 := by
    rw [toList_eq_splitPrefixFinal, leftStemEmpty] at leftMember
    simpa using leftMember
  have splitFinals :
      (splitPrefixFinal left).2 = (splitPrefixFinal right).2 :=
    (split_final_eq left).trans <|
      same.final_eq.trans (split_final_eq right).symm
  have letterIsRightFinal : letter = (splitPrefixFinal right).2 :=
    letterIsLeftFinal.trans splitFinals
  have rightFinalAbsent :=
    splitFinal_not_mem_stem_of_count_one right rightSimple
  exact rightFinalAbsent (letterIsRightFinal ▸ rightStemMember)

private theorem foldl_eval_congr
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat → S) :
    ∀ (letters : List Nat) (initial : S),
      (∀ letter, letter ∈ letters →
        leftValuation letter = rightValuation letter) →
      letters.foldl
          (fun value letter =>
            semigroup.mul value (leftValuation letter)) initial =
        letters.foldl
          (fun value letter =>
            semigroup.mul value (rightValuation letter)) initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (List.Mem.head rest)]
      apply foldl_eval_congr semigroup
      intro tested member
      exact agree tested (List.Mem.tail letter member)

private theorem eval_congr_on_support
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat → S)
    (word : Word Nat)
    (agree :
      ∀ letter, letter ∈ word.toList →
        leftValuation letter = rightValuation letter) :
    semigroup.eval leftValuation word =
      semigroup.eval rightValuation word := by
  cases word with
  | mk first rest =>
      simp only [Semigroup.eval]
      rw [agree first (by simp [Word.toList])]
      apply foldl_eval_congr semigroup
      intro letter member
      exact agree letter (List.Mem.tail first member)

/-- Zero-based catalogue state 4 is the exact actual-factor right identity. -/
theorem s5_530_right_identity (value : Fin 5) :
    rightFactor.mul value (4 : Fin 5) = value :=
  (SemigroupBasis.CoRoots.S5_530.identityElement_certificate value).2

/-- Strip a genuinely fresh terminal variable using the actual right identity. -/
theorem simpleFinal_stem_valid
    (final : Nat) (left right : Word Nat)
    (finalNotLeft : final ∉ left.toList)
    (finalNotRight : final ∉ right.toList)
    (wholeValid :
      (Identity.mk
        (left ++ Word.singleton final)
        (right ++ Word.singleton final)).SatisfiedBy rightFactor) :
    (Identity.mk left right).SatisfiedBy rightFactor := by
  intro valuation
  let lifted : Nat → Fin 5 :=
    fun letter => if letter = final then (4 : Fin 5) else valuation letter
  have leftAgree :
      rightFactor.eval valuation left =
        rightFactor.eval lifted left := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ final := by
      intro equal
      subst letter
      exact finalNotLeft member
    simp [lifted, different]
  have rightAgree :
      rightFactor.eval valuation right =
        rightFactor.eval lifted right := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ final := by
      intro equal
      subst letter
      exact finalNotRight member
    simp [lifted, different]
  have evaluated := wholeValid lifted
  simp only [Semigroup.eval_append, Semigroup.eval_singleton] at evaluated
  have liftedFinal : lifted final = (4 : Fin 5) := by
    simp [lifted]
  rw [liftedFinal, s5_530_right_identity,
    s5_530_right_identity] at evaluated
  exact leftAgree.trans <| evaluated.trans rightAgree.symm

/-- Appending an already present letter preserves first-occurrence order. -/
theorem firstOccurrenceSequence_append_seen
    (letters : List Nat) (final : Nat) (seen : final ∈ letters) :
    firstOccurrenceSequence (letters ++ [final]) =
      firstOccurrenceSequence letters := by
  induction letters with
  | nil =>
      simp at seen
  | cons first rest induction =>
      by_cases equal : first = final
      · subst first
        change
          final ::
              (firstOccurrenceSequence (rest ++ [final])).filter
                (fun selected => decide (selected ≠ final)) =
            final ::
              (firstOccurrenceSequence rest).filter
                (fun selected => decide (selected ≠ final))
        congr 1
        let keep : Nat → Bool :=
          fun selected => decide (selected ≠ final)
        change
          (firstOccurrenceSequence (rest ++ [final])).filter keep =
            (firstOccurrenceSequence rest).filter keep
        calc
          (firstOccurrenceSequence (rest ++ [final])).filter keep =
              firstOccurrenceSequence ((rest ++ [final]).filter keep) :=
            (firstOccurrenceSequence_filter keep (rest ++ [final])).symm
          _ = firstOccurrenceSequence (rest.filter keep) := by
            simp [keep]
          _ = (firstOccurrenceSequence rest).filter keep :=
            firstOccurrenceSequence_filter keep rest
      · have tailSeen : final ∈ rest := by
          rcases List.mem_cons.mp seen with same | member
          · exact False.elim (equal same.symm)
          · exact member
        change
          first ::
              (firstOccurrenceSequence (rest ++ [final])).filter
                (fun selected => decide (selected ≠ first)) =
            first ::
              (firstOccurrenceSequence rest).filter
                (fun selected => decide (selected ≠ first))
        rw [induction tailSeen]

/-- A twice-occurring final gives two lower stems with equal exact cap profiles. -/
theorem doubleFinal_stem_derivation
    (final : Nat) (left right : Word Nat)
    (leftCount : left.toList.count final = 1)
    (rightCount : right.toList.count final = 1)
    (wholeValid :
      (Identity.mk
        (left ++ Word.singleton final)
        (right ++ Word.singleton final)).SatisfiedBy rightFactor) :
    Derives lowerBasis left right := by
  have leftSeen : final ∈ left.toList :=
    List.count_pos_iff.mp (by omega)
  have rightSeen : final ∈ right.toList :=
    List.count_pos_iff.mp (by omega)
  have order :=
    SemigroupBasis.CoRoots.S5_530.valid_firstOccurrenceSequence_eq
      (Identity.mk
        (left ++ Word.singleton final)
        (right ++ Word.singleton final)) wholeValid
  simp only [Word.toList_append, Word.toList_singleton] at order
  rw [firstOccurrenceSequence_append_seen _ final leftSeen,
    firstOccurrenceSequence_append_seen _ final rightSeen] at order
  apply SemigroupBasis.CoRoots.S5_530.s5_530DerivesOfInvariantEq
    left right order
  intro selected
  by_cases equal : selected = final
  · subst selected
    simp [leftCount, rightCount]
  · have counts :=
      SemigroupBasis.CoRoots.S5_530.valid_capped_count_eq
        (Identity.mk
          (left ++ Word.singleton final)
          (right ++ Word.singleton final)) wholeValid selected
    have absent : selected ∉ [final] := by
      simp [equal]
    have singletonZero : [final].count selected = 0 :=
      List.count_eq_zero.mpr absent
    simpa only [Word.toList_append, Word.toList_singleton,
      List.count_append, singletonZero, Nat.add_zero] using counts

/-- Both low-count cases yield a genuine unrestricted lower-stem derivation. -/
theorem lowFinal_stem_derivation
    (final : Nat) (left right : Word Nat)
    (sameCount : left.toList.count final = right.toList.count final)
    (low : left.toList.count final < 2)
    (wholeValid :
      (Identity.mk
        (left ++ Word.singleton final)
        (right ++ Word.singleton final)).SatisfiedBy rightFactor) :
    Derives lowerBasis left right := by
  by_cases absent : final ∉ left.toList
  · have leftZero : left.toList.count final = 0 :=
      List.count_eq_zero.mpr absent
    have rightZero : right.toList.count final = 0 := by
      omega
    have rightAbsent : final ∉ right.toList :=
      List.count_eq_zero.mp rightZero
    exact
      SemigroupBasis.CoRoots.S5_530.representative_basis.2
        (Identity.mk left right)
        (simpleFinal_stem_valid final left right absent rightAbsent wholeValid)
  · have leftPositive : 0 < left.toList.count final :=
      List.count_pos_iff.mpr (Decidable.byContradiction absent)
    have leftOne : left.toList.count final = 1 := by
      omega
    have rightOne : right.toList.count final = 1 := by
      omega
    exact doubleFinal_stem_derivation
      final left right leftOne rightOne wholeValid

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_530

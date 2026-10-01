import SemigroupBasis.CoRoots.S5_579
import SemigroupBasis.Generated.S4_95

namespace SemigroupBasis.CoRoots.S5_579

open SemigroupBasis
open SemigroupBasis.Examples

/-- Evaluation of a possibly empty list in the concrete `S4_95` factor. -/
private def parityListEval
    (valuation : Nat → Fin 4) (letters : List Nat) : Fin 4 :=
  letters.foldl
    (fun current letter =>
      parityInitialFourMul current (valuation letter)) 0

private theorem parityMul_left_identity (value : Fin 4) :
    parityInitialFourMul 0 value = value := by
  simp [parityInitialFourMul]

private theorem parityMul_right_identity (value : Fin 4) :
    parityInitialFourMul value 0 = value := by
  decide +revert

private theorem parityMul_left_two (value : Fin 4) :
    parityInitialFourMul 2 value = 2 := by
  simp [parityInitialFourMul]

private theorem parityMul_left_three (value : Fin 4) :
    parityInitialFourMul 3 value = 3 := by
  simp [parityInitialFourMul]

private theorem parityFold_left_two
    (valuation : Nat → Fin 4) (letters : List Nat) :
    letters.foldl
        (fun current letter =>
          parityInitialFourMul current (valuation letter)) 2 = 2 := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      simpa [List.foldl_cons, parityMul_left_two] using ih

private theorem parityFold_left_three
    (valuation : Nat → Fin 4) (letters : List Nat) :
    letters.foldl
        (fun current letter =>
          parityInitialFourMul current (valuation letter)) 3 = 3 := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      simpa [List.foldl_cons, parityMul_left_three] using ih

private theorem parityFold_all_zero
    (valuation : Nat → Fin 4) :
    ∀ (letters : List Nat) (initial : Fin 4),
      (∀ letter, letter ∈ letters → valuation letter = 0) →
      letters.foldl
          (fun current letter =>
            parityInitialFourMul current (valuation letter)) initial = initial
  | [], _, _ => rfl
  | letter :: rest, initial, allZero => by
      simp only [List.foldl_cons]
      rw [allZero letter (List.Mem.head rest), parityMul_right_identity]
      exact parityFold_all_zero valuation rest initial
        (fun other member => allZero other (List.Mem.tail letter member))

private theorem parityListEval_cons_two
    (valuation : Nat → Fin 4) (letter : Nat) (rest : List Nat)
    (value : valuation letter = 2) :
    parityListEval valuation (letter :: rest) = 2 := by
  unfold parityListEval
  simp only [List.foldl_cons]
  rw [parityMul_left_identity, value]
  exact parityFold_left_two valuation rest

private theorem parityListEval_cons_three
    (valuation : Nat → Fin 4) (letter : Nat) (rest : List Nat)
    (value : valuation letter = 3) :
    parityListEval valuation (letter :: rest) = 3 := by
  unfold parityListEval
  simp only [List.foldl_cons]
  rw [parityMul_left_identity, value]
  exact parityFold_left_three valuation rest

private theorem parityListEval_cons_zero
    (valuation : Nat → Fin 4) (letter : Nat) (rest : List Nat)
    (value : valuation letter = 0) :
    parityListEval valuation (letter :: rest) =
      parityListEval valuation rest := by
  simp [parityListEval, value, parityMul_left_identity]

private theorem parityListEval_single_one
    (valuation : Nat → Fin 4) (letter : Nat) (rest : List Nat)
    (value : valuation letter = 1)
    (restZero : ∀ other, other ∈ rest → valuation other = 0) :
    parityListEval valuation (letter :: rest) = 1 := by
  unfold parityListEval
  simp only [List.foldl_cons]
  rw [parityMul_left_identity, value]
  exact parityFold_all_zero valuation rest 1 restZero

private theorem parityListEval_double_one
    (valuation : Nat → Fin 4) (letter : Nat) (rest : List Nat)
    (value : valuation letter = 1)
    (restZero : ∀ other, other ∈ rest → valuation other = 0) :
    parityListEval valuation (letter :: letter :: rest) = 0 := by
  unfold parityListEval
  simp only [List.foldl_cons]
  rw [parityMul_left_identity, value]
  change
    rest.foldl
        (fun current other =>
          parityInitialFourMul current (valuation other))
        (parityInitialFourMul 1 1) = 0
  have square : parityInitialFourMul 1 1 = (0 : Fin 4) := by decide
  rw [square]
  exact parityFold_all_zero valuation rest 0 restZero

private theorem parityFold_congr
    (left right : Nat → Fin 4) :
    ∀ (letters : List Nat) (initial : Fin 4),
      (∀ letter, letter ∈ letters → left letter = right letter) →
      letters.foldl
          (fun current letter =>
            parityInitialFourMul current (left letter)) initial =
        letters.foldl
          (fun current letter =>
            parityInitialFourMul current (right letter)) initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (List.Mem.head rest)]
      exact parityFold_congr left right rest
        (parityInitialFourMul initial (right letter))
        (fun other member => agree other (List.Mem.tail letter member))

private theorem parityListEval_congr
    (left right : Nat → Fin 4) (letters : List Nat)
    (agree : ∀ letter, letter ∈ letters → left letter = right letter) :
    parityListEval left letters = parityListEval right letters :=
  parityFold_congr left right letters 0 agree

private theorem parityEval_eq_listEval
    (valuation : Nat → Fin 4) (word : Word Nat) :
    parityInitialFour.semigroup.eval valuation word =
      parityListEval valuation word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              parityInitialFourMul current (valuation letter))
            (valuation head) =
          tail.foldl
            (fun current letter =>
              parityInitialFourMul current (valuation letter))
            (parityInitialFourMul 0 (valuation head))
      rw [parityMul_left_identity]

private theorem parityNormal_heads_eq
    (leftHead rightHead : Nat) (leftTail rightTail : List Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        parityListEval valuation (leftHead :: leftTail) =
          parityListEval valuation (rightHead :: rightTail)) :
    leftHead = rightHead := by
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 4 :=
    fun letter =>
      if letter = leftHead then 2 else if letter = rightHead then 3 else 0
  have evaluated := equalEval valuation
  have leftValue :
      parityListEval valuation (leftHead :: leftTail) = 2 :=
    parityListEval_cons_two valuation leftHead leftTail (by
      simp [valuation])
  have rightValue :
      parityListEval valuation (rightHead :: rightTail) = 3 :=
    parityListEval_cons_three valuation rightHead rightTail (by
      simp [valuation, Ne.symm different])
  rw [leftValue, rightValue] at evaluated
  exact (by decide : (2 : Fin 4) ≠ 3) evaluated

/-- The concrete parity factor separates all first-occurrence/parity block
normal forms. This local copy exposes the exact combinatorial bridge needed by
`S5_579` without transferring a basis endpoint from the factor. -/
private theorem parityNormal_eq_of_eval_eq
    {left right : List Nat}
    (leftNormal : ParityInitialNormal left)
    (rightNormal : ParityInitialNormal right)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        parityListEval valuation left = parityListEval valuation right) :
    left = right := by
  induction leftNormal generalizing right with
  | nil =>
      cases rightNormal with
      | nil => rfl
      | single letter rest _ _ =>
          let valuation : Nat → Fin 4 :=
            fun other => if other = letter then 2 else 0
          have evaluated := equalEval valuation
          have rightValue :
              parityListEval valuation (letter :: rest) = 2 :=
            parityListEval_cons_two valuation letter rest (by
              simp [valuation])
          change (0 : Fin 4) =
            parityListEval valuation (letter :: rest) at evaluated
          rw [rightValue] at evaluated
          exact False.elim ((by decide : (0 : Fin 4) ≠ 2) evaluated)
      | double letter rest _ _ =>
          let valuation : Nat → Fin 4 :=
            fun other => if other = letter then 2 else 0
          have evaluated := equalEval valuation
          have rightValue :
              parityListEval valuation (letter :: letter :: rest) = 2 :=
            parityListEval_cons_two valuation letter (letter :: rest) (by
              simp [valuation])
          change (0 : Fin 4) =
            parityListEval valuation (letter :: letter :: rest) at evaluated
          rw [rightValue] at evaluated
          exact False.elim ((by decide : (0 : Fin 4) ≠ 2) evaluated)
  | single leftHead leftTail leftTailNormal leftHeadFresh ih =>
      cases rightNormal with
      | nil =>
          let valuation : Nat → Fin 4 :=
            fun letter => if letter = leftHead then 2 else 0
          have evaluated := equalEval valuation
          have leftValue :
              parityListEval valuation (leftHead :: leftTail) = 2 :=
            parityListEval_cons_two valuation leftHead leftTail (by
              simp [valuation])
          change
            parityListEval valuation (leftHead :: leftTail) =
              (0 : Fin 4) at evaluated
          rw [leftValue] at evaluated
          exact False.elim ((by decide : (2 : Fin 4) ≠ 0) evaluated)
      | single rightHead rightTail rightTailNormal rightHeadFresh =>
          have heads : leftHead = rightHead :=
            parityNormal_heads_eq
              leftHead rightHead leftTail rightTail equalEval
          subst rightHead
          have tailsEqual :
              ∀ valuation : Nat → Fin 4,
                parityListEval valuation leftTail =
                  parityListEval valuation rightTail := by
            intro valuation
            let masked : Nat → Fin 4 :=
              fun letter => if letter = leftHead then 0 else valuation letter
            have fullEqual := equalEval masked
            have maskedHead : masked leftHead = 0 := by simp [masked]
            rw [parityListEval_cons_zero
                masked leftHead leftTail maskedHead,
              parityListEval_cons_zero
                masked leftHead rightTail maskedHead] at fullEqual
            calc
              parityListEval valuation leftTail =
                  parityListEval masked leftTail := by
                    apply parityListEval_congr
                    intro letter member
                    have different : letter ≠ leftHead := by
                      intro equal
                      apply leftHeadFresh
                      simpa [equal] using member
                    simp [masked, different]
              _ = parityListEval masked rightTail := fullEqual
              _ = parityListEval valuation rightTail := by
                    apply parityListEval_congr
                    intro letter member
                    have different : letter ≠ leftHead := by
                      intro equal
                      apply rightHeadFresh
                      simpa [equal] using member
                    simp [masked, different]
          congr 1
          exact ih rightTailNormal tailsEqual
      | double rightHead rightTail _ rightHeadFresh =>
          have heads : leftHead = rightHead :=
            parityNormal_heads_eq
              leftHead rightHead leftTail (rightHead :: rightTail) equalEval
          subst rightHead
          let valuation : Nat → Fin 4 :=
            fun letter => if letter = leftHead then 1 else 0
          have evaluated := equalEval valuation
          have leftValue :
              parityListEval valuation (leftHead :: leftTail) = 1 :=
            parityListEval_single_one valuation leftHead leftTail (by
              simp [valuation]) (by
                intro letter member
                have different : letter ≠ leftHead := by
                  intro equal
                  apply leftHeadFresh
                  simpa [equal] using member
                simp [valuation, different])
          have rightValue :
              parityListEval valuation
                  (leftHead :: leftHead :: rightTail) = 0 :=
            parityListEval_double_one valuation leftHead rightTail (by
              simp [valuation]) (by
                intro letter member
                have different : letter ≠ leftHead := by
                  intro equal
                  apply rightHeadFresh
                  simpa [equal] using member
                simp [valuation, different])
          rw [leftValue, rightValue] at evaluated
          exact False.elim ((by decide : (1 : Fin 4) ≠ 0) evaluated)
  | double leftHead leftTail leftTailNormal leftHeadFresh ih =>
      cases rightNormal with
      | nil =>
          let valuation : Nat → Fin 4 :=
            fun letter => if letter = leftHead then 2 else 0
          have evaluated := equalEval valuation
          have leftValue :
              parityListEval valuation
                  (leftHead :: leftHead :: leftTail) = 2 :=
            parityListEval_cons_two valuation leftHead
              (leftHead :: leftTail) (by simp [valuation])
          change
            parityListEval valuation
                (leftHead :: leftHead :: leftTail) =
              (0 : Fin 4) at evaluated
          rw [leftValue] at evaluated
          exact False.elim ((by decide : (2 : Fin 4) ≠ 0) evaluated)
      | single rightHead rightTail _ rightHeadFresh =>
          have heads : leftHead = rightHead :=
            parityNormal_heads_eq
              leftHead rightHead (leftHead :: leftTail) rightTail equalEval
          subst rightHead
          let valuation : Nat → Fin 4 :=
            fun letter => if letter = leftHead then 1 else 0
          have evaluated := equalEval valuation
          have leftValue :
              parityListEval valuation
                  (leftHead :: leftHead :: leftTail) = 0 :=
            parityListEval_double_one valuation leftHead leftTail (by
              simp [valuation]) (by
                intro letter member
                have different : letter ≠ leftHead := by
                  intro equal
                  apply leftHeadFresh
                  simpa [equal] using member
                simp [valuation, different])
          have rightValue :
              parityListEval valuation (leftHead :: rightTail) = 1 :=
            parityListEval_single_one valuation leftHead rightTail (by
              simp [valuation]) (by
                intro letter member
                have different : letter ≠ leftHead := by
                  intro equal
                  apply rightHeadFresh
                  simpa [equal] using member
                simp [valuation, different])
          rw [leftValue, rightValue] at evaluated
          exact False.elim ((by decide : (0 : Fin 4) ≠ 1) evaluated)
      | double rightHead rightTail rightTailNormal rightHeadFresh =>
          have heads : leftHead = rightHead :=
            parityNormal_heads_eq leftHead rightHead
              (leftHead :: leftTail) (rightHead :: rightTail) equalEval
          subst rightHead
          have tailsEqual :
              ∀ valuation : Nat → Fin 4,
                parityListEval valuation leftTail =
                  parityListEval valuation rightTail := by
            intro valuation
            let masked : Nat → Fin 4 :=
              fun letter => if letter = leftHead then 0 else valuation letter
            have fullEqual := equalEval masked
            have maskedHead : masked leftHead = 0 := by simp [masked]
            rw [parityListEval_cons_zero
                masked leftHead (leftHead :: leftTail) maskedHead,
              parityListEval_cons_zero
                masked leftHead leftTail maskedHead,
              parityListEval_cons_zero
                masked leftHead (leftHead :: rightTail) maskedHead,
              parityListEval_cons_zero
                masked leftHead rightTail maskedHead] at fullEqual
            calc
              parityListEval valuation leftTail =
                  parityListEval masked leftTail := by
                    apply parityListEval_congr
                    intro letter member
                    have different : letter ≠ leftHead := by
                      intro equal
                      apply leftHeadFresh
                      simpa [equal] using member
                    simp [masked, different]
              _ = parityListEval masked rightTail := fullEqual
              _ = parityListEval valuation rightTail := by
                    apply parityListEval_congr
                    intro letter member
                    have different : letter ≠ leftHead := by
                      intro equal
                      apply rightHeadFresh
                      simpa [equal] using member
                    simp [masked, different]
          congr 2
          exact ih rightTailNormal tailsEqual

private theorem validInCanonicalParityFactor
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy parityFactorTable.semigroup) :
    identity.SatisfiedBy parityInitialFour.semigroup := by
  change
    identity.SatisfiedBy
      Generated.Catalogue.S4_95.table.semigroup at valid
  rw [← Generated.S4_95.table_eq_canonical_catalogue] at valid
  exact valid

/-- Validity in the split `S4_95` factor determines the exact
first-occurrence/parity block profile. This is the missing combinatorial
necessity bridge; it does not assert derivational completeness for `S5_579`. -/
theorem sameFirstOccurrenceParity_of_valid_s4_95
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy parityFactorTable.semigroup) :
    SameFirstOccurrenceParity identity.lhs identity.rhs := by
  have canonicalValid := validInCanonicalParityFactor identity valid
  have lhsNormal := parityInitialDerivesNormal identity.lhs
  have rhsNormal := parityInitialDerivesNormal identity.rhs
  cases lhsEq : FirstOccurrenceParityProfile identity.lhs with
  | nil =>
      exact False.elim <|
        parityInitialNormalList_cons_ne_nil
          identity.lhs.head identity.lhs.tail (by
            simpa [FirstOccurrenceParityProfile, Word.toList] using lhsEq)
  | cons leftHead leftTail =>
      cases rhsEq : FirstOccurrenceParityProfile identity.rhs with
      | nil =>
          exact False.elim <|
            parityInitialNormalList_cons_ne_nil
              identity.rhs.head identity.rhs.tail (by
                simpa [FirstOccurrenceParityProfile, Word.toList] using rhsEq)
      | cons rightHead rightTail =>
          change
            match FirstOccurrenceParityProfile identity.lhs with
            | [] => False
            | head :: tail =>
                Derives parityInitialBasis identity.lhs
                  (parityInitialWordOfCons head tail) at lhsNormal
          change
            match FirstOccurrenceParityProfile identity.rhs with
            | [] => False
            | head :: tail =>
                Derives parityInitialBasis identity.rhs
                  (parityInitialWordOfCons head tail) at rhsNormal
          rw [lhsEq] at lhsNormal
          rw [rhsEq] at rhsNormal
          have reducedEvalEqual :
              ∀ valuation : Nat → Fin 4,
                parityListEval valuation (leftHead :: leftTail) =
                  parityListEval valuation (rightHead :: rightTail) := by
            intro valuation
            have lhsSound :=
              lhsNormal.sound parityInitialBasis_models valuation
            have rhsSound :=
              rhsNormal.sound parityInitialBasis_models valuation
            rw [parityEval_eq_listEval] at lhsSound rhsSound
            exact lhsSound.symm.trans
              ((canonicalValid valuation).trans rhsSound)
          have leftForm :
              ParityInitialNormal (leftHead :: leftTail) := by
            rw [← lhsEq]
            exact firstOccurrenceParityProfile_normal identity.lhs
          have rightForm :
              ParityInitialNormal (rightHead :: rightTail) := by
            rw [← rhsEq]
            exact firstOccurrenceParityProfile_normal identity.rhs
          have reducedEqual :
              leftHead :: leftTail = rightHead :: rightTail :=
            parityNormal_eq_of_eval_eq
              leftForm rightForm reducedEvalEqual
          change
            FirstOccurrenceParityProfile identity.lhs =
              FirstOccurrenceParityProfile identity.rhs
          rw [lhsEq, rhsEq]
          exact reducedEqual

/-- The exact combinatorial signature follows from the two split factors. -/
theorem sameSignature_of_factors
    (identity : Identity Nat)
    (parityValid : identity.SatisfiedBy parityFactorTable.semigroup)
    (finalValid : identity.SatisfiedBy finalMarkerFactorTable.semigroup) :
    SameS5_579Signature identity.lhs identity.rhs :=
  ⟨sameFirstOccurrenceParity_of_valid_s4_95 identity parityValid,
    sameGloballySimpleFinal_of_valid_s3_6 identity finalValid⟩

/-- Every identity valid in `S5_579` has the exact combinatorial signature. -/
theorem valid_signature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameS5_579Signature identity.lhs identity.rhs :=
  sameSignature_of_factors identity
    (valid_s4_95 identity valid) (valid_s3_6 identity valid)

/-- A list already in first-occurrence/parity block form is fixed by the
syntax normalizer.  This public fixed-point lemma is the bridge used by the
repeated-final recursion; it exposes no basis transfer from `S4_95`. -/
theorem firstOccurrenceParityProfile_eq_toList_of_normal
    (word : Word Nat)
    (normal : ParityInitialNormal word.toList) :
    FirstOccurrenceParityProfile word = word.toList := by
  have normalized := parityInitialDerivesNormal word
  cases profileEq : FirstOccurrenceParityProfile word with
  | nil =>
      have impossible :
          parityInitialNormalList word.toList = [] := by
        simpa [FirstOccurrenceParityProfile] using profileEq
      exact False.elim <|
        parityInitialNormalList_cons_ne_nil word.head word.tail <| by
          simpa [Word.toList] using impossible
  | cons head tail =>
      have concreteProfile :
          parityInitialNormalList word.toList = head :: tail := by
        simpa [FirstOccurrenceParityProfile] using profileEq
      rw [concreteProfile] at normalized
      have profileNormal : ParityInitialNormal (head :: tail) := by
        rw [← concreteProfile]
        exact parityInitialNormalList_normal word.toList
      have equalEval :
          ∀ valuation : Nat → Fin 4,
            parityListEval valuation (head :: tail) =
              parityListEval valuation word.toList := by
        intro valuation
        have sound := normalized.sound parityInitialBasis_models valuation
        rw [parityEval_eq_listEval, parityEval_eq_listEval] at sound
        exact sound.symm
      have listsEqual : head :: tail = word.toList :=
        parityNormal_eq_of_eval_eq profileNormal normal equalEval
      simpa [profileEq] using listsEqual

private def paritySupportSeparator (tested : Nat) : Nat → Fin 4 :=
  fun letter => if letter = tested then 2 else 0

private theorem parityListEval_supportSeparator_eq_two_iff
    (tested : Nat) :
    ∀ letters : List Nat,
      parityListEval (paritySupportSeparator tested) letters = 2 ↔
        tested ∈ letters
  | [] => by
      simp [parityListEval]
  | letter :: rest => by
      by_cases equal : letter = tested
      · subst letter
        have value : paritySupportSeparator tested tested = 2 := by
          simp [paritySupportSeparator]
        rw [parityListEval_cons_two _ tested rest value]
        simp
      · have value : paritySupportSeparator tested letter = 0 := by
          simp [paritySupportSeparator, equal]
        rw [parityListEval_cons_zero _ letter rest value,
          parityListEval_supportSeparator_eq_two_iff tested rest]
        have reverse : tested ≠ letter := Ne.symm equal
        simp [equal, reverse]

/-- The parity normalizer preserves support exactly.  The proof uses the
`S4_95` support separator rather than exposing the private recursive scanner. -/
theorem mem_firstOccurrenceParityProfile_iff
    (word : Word Nat) (tested : Nat) :
    tested ∈ FirstOccurrenceParityProfile word ↔
      tested ∈ word.toList := by
  have normalized := parityInitialDerivesNormal word
  cases profileEq : FirstOccurrenceParityProfile word with
  | nil =>
      have impossible : parityInitialNormalList word.toList = [] := by
        simpa [FirstOccurrenceParityProfile] using profileEq
      exact False.elim <|
        parityInitialNormalList_cons_ne_nil word.head word.tail <| by
          simpa [Word.toList] using impossible
  | cons head tail =>
      have concreteProfile :
          parityInitialNormalList word.toList = head :: tail := by
        simpa [FirstOccurrenceParityProfile] using profileEq
      rw [concreteProfile] at normalized
      have evaluated :=
        normalized.sound parityInitialBasis_models
          (paritySupportSeparator tested)
      rw [parityEval_eq_listEval, parityEval_eq_listEval] at evaluated
      have sourceMembership :=
        parityListEval_supportSeparator_eq_two_iff tested word.toList
      have targetMembership :=
        parityListEval_supportSeparator_eq_two_iff tested (head :: tail)
      constructor
      · intro inProfile
        have targetTwo :
            parityListEval (paritySupportSeparator tested)
                (head :: tail) = 2 :=
          targetMembership.2 (by simpa [profileEq] using inProfile)
        exact sourceMembership.1 (evaluated.trans targetTwo)
      · intro inSource
        have sourceTwo :
            parityListEval (paritySupportSeparator tested)
                word.toList = 2 :=
          sourceMembership.2 inSource
        have targetTwo :
            parityListEval (paritySupportSeparator tested)
                (head :: tail) = 2 :=
          evaluated.symm.trans sourceTwo
        simpa [profileEq] using (targetMembership.1 targetTwo)

end SemigroupBasis.CoRoots.S5_579

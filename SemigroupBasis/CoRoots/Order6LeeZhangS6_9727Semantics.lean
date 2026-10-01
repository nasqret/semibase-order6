import SemigroupBasis.CoRoots.Order6LeeZhangS6_9727Normalization
import SemigroupBasis.CoRoots.S5_526Semantics
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

/-!
# The direct Lee--Zhang basis for `S6_9727`: semantics

The quotient onto `S5_526` recovers the word-length class and ordered first
pair.  One valuation in the six-element target then separates the remaining
normalized third coordinate.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhangS6_9727

open SemigroupBasis

/-! ## Exact catalogue table and basis soundness -/

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then 0 else
    if left = 1 then (if right = 5 then 3 else 0) else
      if left = 2 then
        (if right = 2 then 1 else
          if right = 4 then 3 else if right = 5 then 4 else 0)
      else if left = 3 then 3 else if left = 4 then 4 else 5

/-- The zero-based catalogue table `S6_9727`. -/
def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

private def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0]⟩⟩

private def finitePowerTailLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 1]⟩⟩

private def finiteDoubleFirstReturnLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [0, 1, 0]⟩⟩

private def finiteDoubleFirstRepeatLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [0, 1, 1]⟩⟩

private def finiteDoubleFirstForgetLaw : Identity (Fin 3) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [0, 1, 2]⟩⟩

private def finiteReturnPowerLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

private def finiteReturnCollapseLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

private def finiteTailDeleteLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 2, 0]⟩⟩

private theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

private theorem finitePowerTailLaw_map :
    finitePowerTailLaw.map Fin.val = powerTailLaw := rfl

private theorem finiteDoubleFirstReturnLaw_map :
    finiteDoubleFirstReturnLaw.map Fin.val = doubleFirstReturnLaw := rfl

private theorem finiteDoubleFirstRepeatLaw_map :
    finiteDoubleFirstRepeatLaw.map Fin.val = doubleFirstRepeatLaw := rfl

private theorem finiteDoubleFirstForgetLaw_map :
    finiteDoubleFirstForgetLaw.map Fin.val = doubleFirstForgetLaw := rfl

private theorem finiteReturnPowerLaw_map :
    finiteReturnPowerLaw.map Fin.val = returnPowerLaw := rfl

private theorem finiteReturnCollapseLaw_map :
    finiteReturnCollapseLaw.map Fin.val = returnCollapseLaw := rfl

private theorem finiteTailDeleteLaw_map :
    finiteTailDeleteLaw.map Fin.val = tailDeleteLaw := rfl

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finitePowerTailLaw_map]
    exact table.checkIdentityNat_sound finitePowerTailLaw (by decide)
  · rw [← finiteDoubleFirstReturnLaw_map]
    exact table.checkIdentityNat_sound finiteDoubleFirstReturnLaw (by decide)
  · rw [← finiteDoubleFirstRepeatLaw_map]
    exact table.checkIdentityNat_sound finiteDoubleFirstRepeatLaw (by decide)
  · rw [← finiteDoubleFirstForgetLaw_map]
    exact table.checkIdentityNat_sound finiteDoubleFirstForgetLaw (by decide)
  · rw [← finiteReturnPowerLaw_map]
    exact table.checkIdentityNat_sound finiteReturnPowerLaw (by decide)
  · rw [← finiteReturnCollapseLaw_map]
    exact table.checkIdentityNat_sound finiteReturnCollapseLaw (by decide)
  · rw [← finiteTailDeleteLaw_map]
    exact table.checkIdentityNat_sound finiteTailDeleteLaw (by decide)

/-! ## The `S5_526` quotient recovers the coarse signature -/

private def quotientMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 2 else
        if value = 3 then 0 else if value = 4 then 3 else 4

private def quotientSection (value : Fin 5) : Fin 6 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 2 else if value = 3 then 4 else 5

private def quotient :
    SplitSurjection table.semigroup
      SemigroupBasis.CoRoots.S5_526.table.semigroup where
  toFun := quotientMap
  map_mul := by
    intro left right
    revert left right
    decide
  preimage := quotientSection
  right_inverse := by
    intro value
    revert value
    decide

private theorem validCoarseSignatureEq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SemigroupBasis.CoRoots.S5_526.signature identity.lhs =
      SemigroupBasis.CoRoots.S5_526.signature identity.rhs :=
  SemigroupBasis.CoRoots.S5_526.valid_signature_eq identity
    (quotient.pushforwardIdentity identity valid)

/-! ## The normalized-third separator -/

def thirdSeparator
    (first second selected : Nat) : Nat → Fin 6 :=
  fun letter =>
    if letter = first then 2 else
      if letter = second then 2 else
        if letter = selected then 5 else 4

private theorem mul_zero_left (value : Fin 6) :
    mul 0 value = 0 := by
  revert value
  decide

private theorem mul_three_left (value : Fin 6) :
    mul 3 value = 3 := by
  revert value
  decide

private theorem fold_zero
    (valuation : Nat → Fin 6) (letters : List Nat) :
    letters.foldl
        (fun current letter => mul current (valuation letter)) 0 = 0 := by
  induction letters with
  | nil => rfl
  | cons letter rest induction =>
      simp only [List.foldl_cons]
      rw [mul_zero_left]
      exact induction

private theorem fold_three
    (valuation : Nat → Fin 6) (letters : List Nat) :
    letters.foldl
        (fun current letter => mul current (valuation letter)) 3 = 3 := by
  induction letters with
  | nil => rfl
  | cons letter rest induction =>
      simp only [List.foldl_cons]
      rw [mul_three_left]
      exact induction

/-- This valuation returns state `3` exactly when the normalized third
coordinate is the selected variable; every later letter is then ignored. -/
theorem thirdSeparator_eval
    (first second selected third : Nat) (rest : List Nat)
    (selectedNeFirst : selected ≠ first)
    (selectedNeSecond : selected ≠ second) :
    table.semigroup.eval (thirdSeparator first second selected)
        (wordOfTwo first second (third :: rest)) =
      if normalizeThird first second third = selected then
        (3 : Fin 6)
      else (0 : Fin 6) := by
  change
    rest.foldl
        (fun current letter =>
          mul current (thirdSeparator first second selected letter))
        (mul
          (mul
            (thirdSeparator first second selected first)
            (thirdSeparator first second selected second))
          (thirdSeparator first second selected third)) =
      if normalizeThird first second third = selected then 3 else 0
  rw [show thirdSeparator first second selected first = (2 : Fin 6) by
    simp [thirdSeparator]]
  rw [show thirdSeparator first second selected second = (2 : Fin 6) by
    simp [thirdSeparator]]
  rw [show mul 2 2 = (1 : Fin 6) by decide]
  by_cases thirdSecond : third = second
  · subst third
    rw [show thirdSeparator first second selected second = (2 : Fin 6) by
      simp [thirdSeparator]]
    rw [show mul 1 2 = (0 : Fin 6) by decide]
    rw [fold_zero]
    simp [normalizeThird, Ne.symm selectedNeFirst]
  · by_cases thirdFirst : third = first
    · subst third
      rw [show thirdSeparator first second selected first = (2 : Fin 6) by
        simp [thirdSeparator]]
      rw [show mul 1 2 = (0 : Fin 6) by decide]
      rw [fold_zero]
      simp [normalizeThird, thirdSecond, Ne.symm selectedNeFirst]
    · by_cases thirdSelected : third = selected
      · subst third
        rw [show thirdSeparator first second selected selected = (5 : Fin 6) by
          simp [thirdSeparator, selectedNeFirst, selectedNeSecond]]
        rw [show mul 1 5 = (3 : Fin 6) by decide]
        rw [fold_three]
        simp [normalizeThird, selectedNeSecond]
      · rw [show thirdSeparator first second selected third = (4 : Fin 6) by
          simp [thirdSeparator, thirdFirst, thirdSecond, thirdSelected]]
        rw [show mul 1 4 = (0 : Fin 6) by decide]
        rw [fold_zero]
        simp [normalizeThird, thirdSecond, thirdSelected]

private theorem normalizeThird_ne_second_of_ne_first
    (first second third : Nat)
    (different : normalizeThird first second third ≠ first) :
    normalizeThird first second third ≠ second := by
  intro equalSecond
  by_cases repeated : third = second
  · exact different (by simp [normalizeThird, repeated])
  · exact repeated (by
      simpa [normalizeThird, repeated] using equalSecond)

/-- Every identity valid in `S6_9727` has equal three-coordinate signatures. -/
theorem valid_signature_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    signature identity.lhs = signature identity.rhs := by
  rcases identity with
    ⟨⟨lhsHead, lhsTail⟩, ⟨rhsHead, rhsTail⟩⟩
  have coarse :=
    validCoarseSignatureEq
      ⟨⟨lhsHead, lhsTail⟩, ⟨rhsHead, rhsTail⟩⟩ valid
  cases lhsTail with
  | nil =>
      cases rhsTail with
      | nil =>
          cases coarse
          rfl
      | cons rhsSecond rhsRest =>
          cases rhsRest <;>
            simp [SemigroupBasis.CoRoots.S5_526.signature] at coarse
  | cons lhsSecond lhsRest =>
      cases rhsTail with
      | nil =>
          cases lhsRest <;>
            simp [SemigroupBasis.CoRoots.S5_526.signature] at coarse
      | cons rhsSecond rhsRest =>
          cases lhsRest with
          | nil =>
              cases rhsRest with
              | nil =>
                  cases coarse
                  rfl
              | cons rhsThird rhsMore =>
                  simp [SemigroupBasis.CoRoots.S5_526.signature] at coarse
          | cons lhsThird lhsMore =>
              cases rhsRest with
              | nil =>
                  simp [SemigroupBasis.CoRoots.S5_526.signature] at coarse
              | cons rhsThird rhsMore =>
                  injection coarse with heads seconds
                  subst rhsHead
                  subst rhsSecond
                  let lhsNormalized :=
                    normalizeThird lhsHead lhsSecond lhsThird
                  let rhsNormalized :=
                    normalizeThird lhsHead lhsSecond rhsThird
                  have normalized : lhsNormalized = rhsNormalized := by
                    apply Decidable.byContradiction
                    intro different
                    by_cases lhsFirst : lhsNormalized = lhsHead
                    · have rhsNeFirst : rhsNormalized ≠ lhsHead := by
                        intro rhsFirst
                        exact different (lhsFirst.trans rhsFirst.symm)
                      have rhsNeSecond : rhsNormalized ≠ lhsSecond :=
                        normalizeThird_ne_second_of_ne_first
                          lhsHead lhsSecond rhsThird rhsNeFirst
                      have evaluated :=
                        valid (thirdSeparator lhsHead lhsSecond rhsNormalized)
                      change
                        table.semigroup.eval
                            (thirdSeparator lhsHead lhsSecond rhsNormalized)
                            (wordOfTwo lhsHead lhsSecond
                              (lhsThird :: lhsMore)) =
                          table.semigroup.eval
                            (thirdSeparator lhsHead lhsSecond rhsNormalized)
                            (wordOfTwo lhsHead lhsSecond
                              (rhsThird :: rhsMore)) at evaluated
                      rw [thirdSeparator_eval lhsHead lhsSecond rhsNormalized
                            lhsThird lhsMore rhsNeFirst rhsNeSecond,
                          thirdSeparator_eval lhsHead lhsSecond rhsNormalized
                            rhsThird rhsMore rhsNeFirst rhsNeSecond] at evaluated
                      simp [lhsNormalized, rhsNormalized, different] at evaluated
                    · have lhsNeSecond : lhsNormalized ≠ lhsSecond :=
                        normalizeThird_ne_second_of_ne_first
                          lhsHead lhsSecond lhsThird lhsFirst
                      have evaluated :=
                        valid (thirdSeparator lhsHead lhsSecond lhsNormalized)
                      change
                        table.semigroup.eval
                            (thirdSeparator lhsHead lhsSecond lhsNormalized)
                            (wordOfTwo lhsHead lhsSecond
                              (lhsThird :: lhsMore)) =
                          table.semigroup.eval
                            (thirdSeparator lhsHead lhsSecond lhsNormalized)
                            (wordOfTwo lhsHead lhsSecond
                              (rhsThird :: rhsMore)) at evaluated
                      rw [thirdSeparator_eval lhsHead lhsSecond lhsNormalized
                            lhsThird lhsMore lhsFirst lhsNeSecond,
                          thirdSeparator_eval lhsHead lhsSecond lhsNormalized
                            rhsThird rhsMore lhsFirst lhsNeSecond] at evaluated
                      simp [lhsNormalized, rhsNormalized, different,
                        Ne.symm different] at evaluated
                  simpa [signature, lhsNormalized, rhsNormalized] using
                    congrArg (Signature.long lhsHead lhsSecond) normalized

theorem basis_complete : BasisFor table.semigroup basis :=
  basis_complete_of_signature table models valid_signature_eq

namespace S6_9727

theorem representative_basis :
    BasisFor table.semigroup basis :=
  basis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_9727

end SemigroupBasis.CoRoots.Order6LeeZhangS6_9727

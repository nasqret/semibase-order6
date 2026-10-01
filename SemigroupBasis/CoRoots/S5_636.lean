import SemigroupBasis.CoRoots.S5_636Normalization
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_636

open SemigroupBasis
open SemigroupBasis.Examples

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_636.table

abbrev basis : List (Identity Nat) :=
  s5_636Basis

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = s5_636PowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = s5_636GatherLaw := rfl

/-- The exact catalogue table satisfies both displayed laws. -/
theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, s5_636Basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact table.checkIdentityNat_sound finiteGatherLaw (by decide)

/-- Quotient recording the sequence of first occurrences. One-based
elements `1,2` map to the first left-zero value, `3,4` map to the
identity, and `5` maps to the second left-zero value. -/
def leftRegularBandQuotient :
    SplitSurjection table.semigroup leftRegularBandThree.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨1, by decide⟩ else ⟨2, by decide⟩
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

theorem valid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
    identity (leftRegularBandQuotient.pushforwardIdentity identity valid)

/-- One-based table element `3` is the identity. -/
def identityElement : Fin 5 := 2

/-- One-based table elements `1` and `5` uniformly detect block order. -/
def firstOrderWitness : Fin 5 := 0
def secondOrderWitness : Fin 5 := 4

theorem identityElement_certificate (a : Fin 5) :
    Generated.Catalogue.S5_636.mul identityElement a = a ∧
      Generated.Catalogue.S5_636.mul a identityElement = a := by
  revert a
  decide

private theorem exponent_le_three (n : Nat) :
    s5_636Exponent n ≤ 3 := by
  unfold s5_636Exponent periodTwoFromTwoExponent
  split <;> omega

private def exponentState (n : Nat) : Fin 4 :=
  ⟨s5_636Exponent n, by
    have bound := exponent_le_three n
    omega⟩

private def exponentNext (state : Fin 4) : Fin 4 :=
  if h : state.val < 3 then
    ⟨state.val + 1, by omega⟩
  else
    ⟨state.val - 1, by omega⟩

private theorem exponentState_succ (n : Nat) :
    exponentState (n + 1) =
      exponentNext (exponentState n) := by
  apply Fin.ext
  change s5_636Exponent (n + 1) =
    (exponentNext (exponentState n)).val
  rw [s5_636Exponent_succ]
  unfold exponentNext exponentState
  split <;> rfl

/-- One-based table elements `2` and `4` jointly distinguish the exponent
states zero, one, positive even, and odd at least three. -/
def powerWitness (index : Fin 2) : Fin 5 :=
  if index = 0 then 1 else 3

private def powerCode (state : Fin 4) : Fin 5 × Fin 5 :=
  if state = 0 then
    (identityElement, identityElement)
  else if state = 1 then
    (1, 3)
  else if state = 2 then
    (0, identityElement)
  else
    (0, 3)

private theorem powerCode_injective :
    Function.Injective powerCode := by
  intro a b
  revert a b
  decide

private def powerCoordinate
    (profile : Fin 5 × Fin 5) (index : Fin 2) : Fin 5 :=
  if index = 0 then profile.1 else profile.2

private theorem powerCode_step
    (state : Fin 4) (index : Fin 2) :
    Generated.Catalogue.S5_636.mul
        (powerCoordinate (powerCode state) index)
        (powerWitness index) =
      powerCoordinate
        (powerCode (exponentNext state)) index := by
  revert state index
  decide

private def powerState (index : Fin 2) (n : Nat) : Fin 5 :=
  powerCoordinate (powerCode (exponentState n)) index

private theorem powerState_step
    (index : Fin 2) (n : Nat) :
    Generated.Catalogue.S5_636.mul
        (powerState index n) (powerWitness index) =
      powerState index (n + 1) := by
  calc
    Generated.Catalogue.S5_636.mul
        (powerState index n) (powerWitness index) =
        powerCoordinate
          (powerCode (exponentNext (exponentState n))) index := by
      simpa [powerState] using
        powerCode_step (exponentState n) index
    _ = powerState index (n + 1) := by
      rw [powerState, exponentState_succ]

private theorem powerState_other
    (index : Fin 2) (n : Nat) :
    Generated.Catalogue.S5_636.mul
        (powerState index n) identityElement =
      powerState index n :=
  (identityElement_certificate _).2

def powerValuation
    (index : Fin 2) (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then powerWitness index else identityElement

private theorem powerValuation_self
    (index : Fin 2) (z : Nat) :
    powerValuation index z z = powerState index 1 := by
  by_cases hi : index = 0
  · subst index
    simp [powerValuation, powerState, powerCoordinate, powerCode,
      exponentState, s5_636Exponent, periodTwoFromTwoExponent,
      powerWitness, identityElement]
  · simp [powerValuation, powerState, powerCoordinate, powerCode,
      exponentState, s5_636Exponent, periodTwoFromTwoExponent,
      powerWitness, identityElement, hi]

private theorem powerValuation_other
    (index : Fin 2) {z x : Nat} (different : x ≠ z) :
    powerValuation index z x = powerState index 0 := by
  by_cases hi : index = 0
  · subst index
    simp [powerValuation, different, powerState, powerCoordinate,
      powerCode, exponentState, s5_636Exponent,
      periodTwoFromTwoExponent, identityElement]
  · simp [powerValuation, different, powerState, powerCoordinate,
      powerCode, exponentState, s5_636Exponent,
      periodTwoFromTwoExponent, identityElement, hi]

private theorem powerFold (index : Fin 2) (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            Generated.Catalogue.S5_636.mul current
              (powerValuation index z x))
          (powerState index n) =
        powerState index (n + xs.count z)
  | [], _ => by
      simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show
          powerValuation index z z = powerWitness index by
            simp [powerValuation]]
        rw [powerState_step, powerFold]
        rw [List.count_cons_self]
        congr 1
        omega
      · rw [show
          powerValuation index z x = identityElement by
            simp [powerValuation, hx]]
        rw [powerState_other, powerFold,
          List.count_cons_of_ne hx]

theorem eval_power
    (index : Fin 2) (z : Nat) (w : Word Nat) :
    table.semigroup.eval (powerValuation index z) w =
      powerState index (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_636.mul current
                (powerValuation index z x))
            (powerValuation index z head) =
          powerState index ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [powerValuation_self, powerFold, List.count_cons_self]
        congr 1
        omega
      · rw [powerValuation_other index hhead,
          powerFold, List.count_cons_of_ne hhead]
        congr 1
        omega

theorem valid_exponent_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z,
      s5_636Exponent (identity.lhs.toList.count z) =
        s5_636Exponent (identity.rhs.toList.count z) := by
  intro z
  have first := valid (powerValuation 0 z)
  have second := valid (powerValuation 1 z)
  rw [eval_power, eval_power] at first
  rw [eval_power, eval_power] at second
  have profiles :
      powerCode
          (exponentState (identity.lhs.toList.count z)) =
        powerCode
          (exponentState (identity.rhs.toList.count z)) := by
    apply Prod.ext
    · simpa [powerState, powerCoordinate] using first
    · simpa [powerState, powerCoordinate] using second
  have states := powerCode_injective profiles
  exact congrArg Fin.val states

def powerProfilesOneBased : List (List Nat) :=
  [
    List.ofFn (fun a : Fin 5 => a.val + 1),
    List.ofFn (fun a : Fin 5 =>
      (Generated.Catalogue.S5_636.mul a a).val + 1),
    List.ofFn (fun a : Fin 5 =>
      (Generated.Catalogue.S5_636.mul
        (Generated.Catalogue.S5_636.mul a a) a).val + 1)
  ]

theorem powerProfilesOneBased_certificate :
    powerProfilesOneBased =
      [[1, 2, 3, 4, 5], [1, 1, 3, 3, 5], [1, 1, 3, 4, 5]] := by
  decide

def witnessPower (witness : Fin 5) (exponent : Fin 3) : Fin 5 :=
  if exponent.val = 0 then witness else
    if exponent.val = 1 then
      Generated.Catalogue.S5_636.mul witness witness
    else
      Generated.Catalogue.S5_636.mul
        (Generated.Catalogue.S5_636.mul witness witness) witness

/-- All nine pairs of normalized positive exponents preserve the same strict
order witness: `1^i * 5^j = 1`, while `5^j * 1^i = 5`. -/
theorem uniformOrderWitness_certificate (i j : Fin 3) :
    Generated.Catalogue.S5_636.mul
        (witnessPower firstOrderWitness i)
        (witnessPower secondOrderWitness j) =
          firstOrderWitness ∧
      Generated.Catalogue.S5_636.mul
        (witnessPower secondOrderWitness j)
        (witnessPower firstOrderWitness i) =
          secondOrderWitness := by
  revert i j
  decide

theorem representative_basis :
    BasisFor table.semigroup basis :=
  s5_636Basis_complete_of_invariants table models
    valid_firstOccurrenceSequence_eq valid_exponent_eq

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def s5_636YXX : Word Nat := ⟨1, [0, 0]⟩

def expectedOppositeBasis : List (Identity Nat) :=
  [s5_636PowerLaw, ⟨s5_636YXX, s5_636XYX⟩]

theorem oppositeBasis_eq_expected :
    oppositeBasis = expectedOppositeBasis := by
  rfl

theorem opposite_basis :
    BasisFor table.semigroup.opposite expectedOppositeBasis := by
  rw [← oppositeBasis_eq_expected]
  exact representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.S5_636

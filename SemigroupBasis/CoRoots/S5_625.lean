import SemigroupBasis.CoRoots.S5_625Normalization
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_625

open SemigroupBasis
open SemigroupBasis.Examples

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_625.table

abbrev basis : List (Identity Nat) :=
  s5_625Basis

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteTailPowerLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1, 1]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = s5_625PowerLaw := rfl

theorem finiteTailPowerLaw_map :
    finiteTailPowerLaw.map Fin.val = s5_625TailPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = s5_625GatherLaw := rfl

/-- The exact catalogue table satisfies the three displayed laws. -/
theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, s5_625Basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteTailPowerLaw_map]
    exact table.checkIdentityNat_sound finiteTailPowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact table.checkIdentityNat_sound finiteGatherLaw (by decide)

/-- Quotient recording the first-occurrence sequence. One-based elements
`1,2` map to the first left-zero value, `3,4` map to the identity, and
`5` maps to the second left-zero value. -/
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

/-- One-based table element `3` is a right identity. -/
def rightIdentity : Fin 5 := 2

/-- One-based table elements `2` and `4` separate the three positive head
multiplicity states. -/
def headPowerWitness (index : Fin 2) : Fin 5 :=
  if index = 0 then 1 else 3

/-- One-based table element `4` separates odd and even tail multiplicities. -/
def tailParityWitness : Fin 5 := 3

/-- One-based table element `5` detects support. -/
def supportWitness : Fin 5 := 4

/-- One-based table elements `1` and `5` uniformly distinguish block order. -/
def firstOrderWitness : Fin 5 := 0
def secondOrderWitness : Fin 5 := 4

theorem rightIdentity_certificate (a : Fin 5) :
    Generated.Catalogue.S5_625.mul a rightIdentity = a := by
  revert a
  decide

def supportProfileOneBased : List Nat :=
  [rightIdentity.val + 1, supportWitness.val + 1,
    (Generated.Catalogue.S5_625.mul
      rightIdentity supportWitness).val + 1]

theorem supportProfileOneBased_certificate :
    supportProfileOneBased = [3, 5, 5] := by
  decide

def tailParityProfileOneBased : List Nat :=
  [rightIdentity.val + 1, tailParityWitness.val + 1]

theorem tailParityProfileOneBased_certificate :
    tailParityProfileOneBased = [3, 4] := by
  decide

private theorem headExponent_le_three (n : Nat) :
    SemigroupBasis.CoRoots.S5_636.s5_636Exponent n ≤ 3 := by
  unfold SemigroupBasis.CoRoots.S5_636.s5_636Exponent
    periodTwoFromTwoExponent
  split <;> omega

private def headExponentState (n : Nat) : Fin 4 :=
  ⟨SemigroupBasis.CoRoots.S5_636.s5_636Exponent n,
    Nat.lt_succ_of_le (headExponent_le_three n)⟩

private def headExponentNext (state : Fin 4) : Fin 4 :=
  if h : state.val < 3 then
    ⟨state.val + 1, by omega⟩
  else
    ⟨state.val - 1, by omega⟩

private theorem headExponentState_succ (n : Nat) :
    headExponentState (n + 1) =
      headExponentNext (headExponentState n) := by
  apply Fin.ext
  change
    SemigroupBasis.CoRoots.S5_636.s5_636Exponent (n + 1) =
      (headExponentNext (headExponentState n)).val
  rw [SemigroupBasis.CoRoots.S5_636.s5_636Exponent_succ]
  unfold headExponentNext headExponentState
  split <;> rfl

private def headPowerCode (state : Fin 4) : Fin 5 × Fin 5 :=
  if state = 0 then
    (rightIdentity, rightIdentity)
  else if state = 1 then
    (1, 3)
  else if state = 2 then
    (0, rightIdentity)
  else
    (0, 3)

private theorem headPowerCode_injective :
    Function.Injective headPowerCode := by
  intro left right
  revert left right
  decide

private def headPowerCoordinate
    (profile : Fin 5 × Fin 5) (index : Fin 2) : Fin 5 :=
  if index = 0 then profile.1 else profile.2

private theorem headPowerCode_step
    (state : Fin 4) (index : Fin 2)
    (positive : 0 < state.val) :
    Generated.Catalogue.S5_625.mul
        (headPowerCoordinate (headPowerCode state) index)
        (headPowerWitness index) =
      headPowerCoordinate
        (headPowerCode (headExponentNext state)) index := by
  revert state index
  decide

private def headPowerState
    (index : Fin 2) (n : Nat) : Fin 5 :=
  headPowerCoordinate (headPowerCode (headExponentState n)) index

private theorem headPowerState_step
    (index : Fin 2) (n : Nat) (positive : 0 < n) :
    Generated.Catalogue.S5_625.mul
        (headPowerState index n) (headPowerWitness index) =
      headPowerState index (n + 1) := by
  have statePositive :
      0 < (headExponentState n).val :=
    SemigroupBasis.CoRoots.S5_636.s5_636Exponent_pos positive
  calc
    Generated.Catalogue.S5_625.mul
        (headPowerState index n) (headPowerWitness index) =
        headPowerCoordinate
          (headPowerCode
            (headExponentNext (headExponentState n))) index := by
      simpa [headPowerState] using
        headPowerCode_step
          (headExponentState n) index statePositive
    _ = headPowerState index (n + 1) := by
      rw [headPowerState, headExponentState_succ]

private theorem headPowerState_other
    (index : Fin 2) (n : Nat) :
    Generated.Catalogue.S5_625.mul
        (headPowerState index n) rightIdentity =
      headPowerState index n :=
  rightIdentity_certificate _

def headPowerValuation
    (index : Fin 2) (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then headPowerWitness index else rightIdentity

private theorem headPowerValuation_self
    (index : Fin 2) (z : Nat) :
    headPowerValuation index z z = headPowerState index 1 := by
  by_cases hi : index = 0
  · subst index
    simp [headPowerValuation, headPowerState, headPowerCoordinate,
      headPowerCode, headExponentState,
      SemigroupBasis.CoRoots.S5_636.s5_636Exponent,
      periodTwoFromTwoExponent, headPowerWitness, rightIdentity]
  · simp [headPowerValuation, headPowerState, headPowerCoordinate,
      headPowerCode, headExponentState,
      SemigroupBasis.CoRoots.S5_636.s5_636Exponent,
      periodTwoFromTwoExponent, headPowerWitness, rightIdentity, hi]

private theorem headPowerFold (index : Fin 2) (z : Nat) :
    ∀ (xs : List Nat) (n : Nat), 0 < n →
      xs.foldl
          (fun current x =>
            Generated.Catalogue.S5_625.mul current
              (headPowerValuation index z x))
          (headPowerState index n) =
        headPowerState index (n + xs.count z)
  | [], _, _ => by
      simp
  | x :: xs, n, positive => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show
          headPowerValuation index z z =
              headPowerWitness index by
            simp [headPowerValuation]]
        rw [headPowerState_step index n positive,
          headPowerFold index z xs (n + 1) (by omega),
          List.count_cons_self]
        congr 1
        omega
      · rw [show
          headPowerValuation index z x = rightIdentity by
            simp [headPowerValuation, hx]]
        rw [headPowerState_other,
          headPowerFold index z xs n positive,
          List.count_cons_of_ne hx]

theorem eval_headPower_of_head
    (index : Fin 2) (z : Nat) (word : Word Nat)
    (headEq : word.head = z) :
    table.semigroup.eval (headPowerValuation index z) word =
      headPowerState index (word.toList.count z) := by
  cases word with
  | mk head tail =>
      simp only at headEq
      subst head
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_625.mul current
                (headPowerValuation index z x))
            (headPowerValuation index z z) =
          headPowerState index ((z :: tail).count z)
      rw [headPowerValuation_self,
        headPowerFold index z tail 1 (by omega),
        List.count_cons_self]
      congr 1
      omega

theorem valid_head
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  have order :=
    valid_firstOccurrenceSequence_eq identity valid
  cases identity with
  | mk left right =>
      cases left with
      | mk leftHead leftTail =>
          cases right with
          | mk rightHead rightTail =>
              change leftHead = rightHead
              change
                firstOccurrenceSequence (leftHead :: leftTail) =
                  firstOccurrenceSequence
                    (rightHead :: rightTail) at order
              simp only [firstOccurrenceSequence] at order
              exact (List.cons.inj order).1

theorem valid_headExponent
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SemigroupBasis.CoRoots.S5_636.s5_636Exponent
        (identity.lhs.toList.count identity.lhs.head) =
      SemigroupBasis.CoRoots.S5_636.s5_636Exponent
        (identity.rhs.toList.count identity.rhs.head) := by
  have heads := valid_head identity valid
  have first :=
    valid (headPowerValuation 0 identity.lhs.head)
  have second :=
    valid (headPowerValuation 1 identity.lhs.head)
  rw [eval_headPower_of_head
      0 identity.lhs.head identity.lhs rfl,
    eval_headPower_of_head
      0 identity.lhs.head identity.rhs heads.symm] at first
  rw [eval_headPower_of_head
      1 identity.lhs.head identity.lhs rfl,
    eval_headPower_of_head
      1 identity.lhs.head identity.rhs heads.symm] at second
  have profiles :
      headPowerCode
          (headExponentState
            (identity.lhs.toList.count identity.lhs.head)) =
        headPowerCode
          (headExponentState
            (identity.rhs.toList.count identity.rhs.head)) := by
    apply Prod.ext
    · simpa [headPowerState, headPowerCoordinate, heads] using first
    · simpa [headPowerState, headPowerCoordinate, heads] using second
  have states := headPowerCode_injective profiles
  exact congrArg Fin.val states

def headPowerProfilesOneBased : List (List Nat) :=
  [
    [(headPowerCode 1).1.val + 1,
      (headPowerCode 1).2.val + 1],
    [(headPowerCode 2).1.val + 1,
      (headPowerCode 2).2.val + 1],
    [(headPowerCode 3).1.val + 1,
      (headPowerCode 3).2.val + 1]
  ]

theorem headPowerProfilesOneBased_certificate :
    headPowerProfilesOneBased =
      [[2, 4], [1, 3], [1, 4]] := by
  decide

private def parityResidue (n : Nat) : Fin 2 :=
  ⟨n % 2, Nat.mod_lt n (by decide)⟩

private def parityCode (state : Fin 2) : Fin 5 :=
  if state = 0 then rightIdentity else tailParityWitness

private theorem parityCode_injective :
    Function.Injective parityCode := by
  intro left right
  revert left right
  decide

private def parityState (n : Nat) : Fin 5 :=
  parityCode (parityResidue n)

private theorem parityState_step (n : Nat) :
    Generated.Catalogue.S5_625.mul
        (parityState n) tailParityWitness =
      parityState (n + 1) := by
  by_cases hp : n % 2 = 0
  · have hnext : (n + 1) % 2 = 1 := by
      omega
    simp [parityState, parityCode, parityResidue, hp, hnext,
      rightIdentity, tailParityWitness,
      Generated.Catalogue.S5_625.mul]
  · have hmod : n % 2 = 1 := by
      omega
    have hnext : (n + 1) % 2 = 0 := by
      omega
    simp [parityState, parityCode, parityResidue, hmod, hnext,
      rightIdentity, tailParityWitness,
      Generated.Catalogue.S5_625.mul]

private theorem parityState_other (n : Nat) :
    Generated.Catalogue.S5_625.mul
        (parityState n) rightIdentity =
      parityState n :=
  rightIdentity_certificate _

def parityValuation (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then tailParityWitness else rightIdentity

private theorem parityFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            Generated.Catalogue.S5_625.mul current
              (parityValuation z x))
          (parityState n) =
        parityState (n + xs.count z)
  | [], _ => by
      simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show parityValuation z z = tailParityWitness by
          simp [parityValuation]]
        rw [parityState_step, parityFold,
          List.count_cons_self]
        congr 1
        omega
      · rw [show parityValuation z x = rightIdentity by
          simp [parityValuation, hx]]
        rw [parityState_other, parityFold,
          List.count_cons_of_ne hx]

theorem eval_parity (z : Nat) (word : Word Nat) :
    table.semigroup.eval (parityValuation z) word =
      parityState (word.toList.count z) := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_625.mul current
                (parityValuation z x))
            (parityValuation z head) =
          parityState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [show parityValuation z z = parityState 1 by
          simp [parityValuation, parityState, parityCode,
            parityResidue, tailParityWitness]]
        rw [parityFold, List.count_cons_self]
        congr 1
        omega
      · rw [show parityValuation z head = parityState 0 by
          simp [parityValuation, hhead, parityState, parityCode,
            parityResidue, rightIdentity]]
        rw [parityFold, List.count_cons_of_ne hhead]
        congr 1
        omega

theorem valid_parity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z,
      identity.lhs.toList.count z % 2 =
        identity.rhs.toList.count z % 2 := by
  intro z
  have evaluated := valid (parityValuation z)
  rw [eval_parity, eval_parity] at evaluated
  have states :
      parityResidue (identity.lhs.toList.count z) =
        parityResidue (identity.rhs.toList.count z) := by
    apply parityCode_injective
    simpa [parityState] using evaluated
  exact congrArg Fin.val states

def witnessPower (witness : Fin 5) (exponent : Fin 3) : Fin 5 :=
  if exponent.val = 0 then witness else
    if exponent.val = 1 then
      Generated.Catalogue.S5_625.mul witness witness
    else
      Generated.Catalogue.S5_625.mul
        (Generated.Catalogue.S5_625.mul witness witness) witness

/-- All nine pairs of normalized positive exponents preserve the strict
order witness `1^i * 5^j = 1`, `5^j * 1^i = 5`. -/
theorem uniformOrderWitness_certificate (i j : Fin 3) :
    Generated.Catalogue.S5_625.mul
        (witnessPower firstOrderWitness i)
        (witnessPower secondOrderWitness j) =
          firstOrderWitness ∧
      Generated.Catalogue.S5_625.mul
        (witnessPower secondOrderWitness j)
        (witnessPower firstOrderWitness i) =
          secondOrderWitness := by
  revert i j
  decide

theorem representative_basis :
    BasisFor table.semigroup basis :=
  s5_625Basis_complete_of_separates table models
    valid_firstOccurrenceSequence_eq valid_headExponent valid_parity

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def s5_625YX : Word Nat := ⟨1, [0]⟩
def s5_625YYYX : Word Nat := ⟨1, [1, 1, 0]⟩
def s5_625YXX : Word Nat := ⟨1, [0, 0]⟩

def expectedOppositeBasis : List (Identity Nat) :=
  [s5_625PowerLaw,
    ⟨s5_625YX, s5_625YYYX⟩,
    ⟨s5_625YXX, s5_625XYX⟩]

theorem oppositeBasis_eq_expected :
    oppositeBasis = expectedOppositeBasis := by
  rfl

theorem opposite_basis :
    BasisFor table.semigroup.opposite expectedOppositeBasis := by
  rw [← oppositeBasis_eq_expected]
  exact representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.S5_625

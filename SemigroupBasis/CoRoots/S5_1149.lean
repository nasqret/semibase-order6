import SemigroupBasis.CoRoots.S5_1149Normalization
import SemigroupBasis.Generated.CatalogueOrder5Part09
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_1149

open SemigroupBasis
open SemigroupBasis.Examples

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_1149.table

abbrev basis : List (Identity Nat) :=
  s5_1149Basis

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = s5_1149PowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = s5_1149GatherLaw := rfl

/-- The exact catalogue table satisfies both displayed laws. -/
theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, s5_1149Basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact table.checkIdentityNat_sound finiteGatherLaw (by decide)

/-- The quotient that records presence and pairwise first-occurrence order.
The cyclic subgroup elements all map to the identity of `S3_16`. -/
def leftRegularBandQuotient :
    SplitSurjection table.semigroup leftRegularBandThree.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 2 then ⟨2, by decide⟩ else ⟨1, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else ⟨2, by decide⟩
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

/-- One-based table element `2` is the monoid identity. -/
def identityElement : Fin 5 := 1

/-- One-based table element `4` generates the cyclic subgroup
`{2,4,5}` of order three. -/
def residueWitness : Fin 5 := 3

theorem identityElement_certificate (a : Fin 5) :
    Generated.Catalogue.S5_1149.mul identityElement a = a ∧
      Generated.Catalogue.S5_1149.mul a identityElement = a := by
  revert a
  decide

def residueCode (residue : Fin 3) : Fin 5 :=
  if residue.val = 0 then 1
  else if residue.val = 1 then 3
  else 4

theorem residueCode_injective :
    Function.Injective residueCode := by
  intro left right
  revert left right
  decide

def residueOutputsOneBased : List Nat :=
  List.ofFn (fun residue : Fin 3 => (residueCode residue).val + 1)

theorem residueOutputsOneBased_certificate :
    residueOutputsOneBased = [2, 4, 5] := by
  decide

private def residueState (n : Nat) : Fin 5 :=
  residueCode ⟨n % 3, Nat.mod_lt _ (by decide)⟩

def residueValuation (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then residueWitness else identityElement

private theorem residueState_step (n : Nat) :
    Generated.Catalogue.S5_1149.mul
        (residueState n) residueWitness =
      residueState (n + 1) := by
  by_cases h0 : n % 3 = 0
  · have hnext : (n + 1) % 3 = 1 := by omega
    apply Fin.ext
    simp [residueState, residueCode, residueWitness, h0, hnext,
      Generated.Catalogue.S5_1149.mul]
  · by_cases h1 : n % 3 = 1
    · have hnext : (n + 1) % 3 = 2 := by omega
      apply Fin.ext
      simp [residueState, residueCode, residueWitness, h0, h1, hnext,
        Generated.Catalogue.S5_1149.mul]
    · have h2 : n % 3 = 2 := by omega
      have hnext : (n + 1) % 3 = 0 := by omega
      apply Fin.ext
      simp [residueState, residueCode, residueWitness, h0, h1, h2, hnext,
        Generated.Catalogue.S5_1149.mul]

private theorem residueState_other (n : Nat) :
    Generated.Catalogue.S5_1149.mul
        (residueState n) identityElement =
      residueState n :=
  (identityElement_certificate _).2

private theorem residueFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            Generated.Catalogue.S5_1149.mul current
              (residueValuation z x))
          (residueState n) =
        residueState (n + xs.count z)
  | [], _ => by simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show residueValuation z z = residueWitness by
          simp [residueValuation]]
        rw [residueState_step, residueFold]
        rw [List.count_cons_self]
        congr 1
        omega
      · rw [show residueValuation z x = identityElement by
          simp [residueValuation, hx]]
        rw [residueState_other, residueFold,
          List.count_cons_of_ne hx]

theorem eval_residue (z : Nat) (w : Word Nat) :
    table.semigroup.eval (residueValuation z) w =
      residueState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_1149.mul current
                (residueValuation z x))
            (residueValuation z head) =
          residueState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [show residueValuation z z = residueState 1 by
          simp [residueValuation, residueWitness, residueState,
            residueCode]]
        rw [residueFold, List.count_cons_self]
        congr 1
        omega
      · rw [show residueValuation z head = residueState 0 by
          simp [residueValuation, hhead, residueState, residueCode,
            identityElement]]
        rw [residueFold, List.count_cons_of_ne hhead]
        congr 1
        omega

theorem valid_count_mod_three_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z,
      identity.lhs.toList.count z % 3 =
        identity.rhs.toList.count z % 3 := by
  intro z
  have evaluated := valid (residueValuation z)
  rw [eval_residue, eval_residue] at evaluated
  have states :
      (⟨identity.lhs.toList.count z % 3,
          Nat.mod_lt _ (by decide)⟩ : Fin 3) =
        ⟨identity.rhs.toList.count z % 3,
          Nat.mod_lt _ (by decide)⟩ := by
    apply residueCode_injective
    simpa [residueState] using evaluated
  exact congrArg Fin.val states

theorem valid_exponent_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z,
      s5_1149Exponent (identity.lhs.toList.count z) =
        s5_1149Exponent (identity.rhs.toList.count z) := by
  intro z
  have modEq := valid_count_mod_three_eq identity valid z
  have orderEq :=
    valid_firstOccurrenceSequence_eq identity valid
  have supportEq :
      identity.lhs.toList.count z = 0 ↔
        identity.rhs.toList.count z = 0 := by
    constructor
    · intro leftZero
      apply List.count_eq_zero.mpr
      intro rightMember
      have rightInitial :
          z ∈ firstOccurrenceSequence identity.rhs.toList :=
        (s5_1149Mem_firstOccurrenceSequence_iff z _).mpr rightMember
      have leftInitial :
          z ∈ firstOccurrenceSequence identity.lhs.toList := by
        rw [orderEq]
        exact rightInitial
      exact (List.count_eq_zero.mp leftZero)
        ((s5_1149Mem_firstOccurrenceSequence_iff z _).mp leftInitial)
    · intro rightZero
      apply List.count_eq_zero.mpr
      intro leftMember
      have leftInitial :
          z ∈ firstOccurrenceSequence identity.lhs.toList :=
        (s5_1149Mem_firstOccurrenceSequence_iff z _).mpr leftMember
      have rightInitial :
          z ∈ firstOccurrenceSequence identity.rhs.toList := by
        rw [← orderEq]
        exact leftInitial
      exact (List.count_eq_zero.mp rightZero)
        ((s5_1149Mem_firstOccurrenceSequence_iff z _).mp rightInitial)
  by_cases hl : identity.lhs.toList.count z = 0
  · have hr := supportEq.mp hl
    simp [s5_1149Exponent, hl, hr]
  · have hr : identity.rhs.toList.count z ≠ 0 :=
      fun zero => hl (supportEq.mpr zero)
    simp [s5_1149Exponent, hl, hr, modEq]

/-- One-based elements `1` and `3` are the exact initial-order markers. -/
def firstOrderWitness : Fin 5 := 0
def secondOrderWitness : Fin 5 := 2

theorem firstOrderWitness_leftZero_certificate (a : Fin 5) :
    Generated.Catalogue.S5_1149.mul firstOrderWitness a =
      firstOrderWitness := by
  revert a
  decide

theorem secondOrderWitness_leftZero_certificate (a : Fin 5) :
    Generated.Catalogue.S5_1149.mul secondOrderWitness a =
      secondOrderWitness := by
  revert a
  decide

theorem representative_basis :
    BasisFor table.semigroup basis :=
  s5_1149Basis_complete_of_invariants table models
    valid_firstOccurrenceSequence_eq valid_exponent_eq

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def s5_1149YXX : Word Nat := ⟨1, [0, 0]⟩

def expectedOppositeBasis : List (Identity Nat) :=
  [s5_1149PowerLaw, ⟨s5_1149YXX, s5_1149XYX⟩]

theorem oppositeBasis_eq_expected :
    oppositeBasis = expectedOppositeBasis := by
  rfl

theorem opposite_basis :
    BasisFor table.semigroup.opposite expectedOppositeBasis := by
  rw [← oppositeBasis_eq_expected]
  exact representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.S5_1149

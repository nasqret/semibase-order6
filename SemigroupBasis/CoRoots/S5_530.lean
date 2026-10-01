import SemigroupBasis.CoRoots.S5_530Normalization
import SemigroupBasis.Examples.CommutativeExponentFour
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_530

open SemigroupBasis
open SemigroupBasis.Examples

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_530.table

abbrev basis : List (Identity Nat) :=
  s5_530Basis

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = s5_530PowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = s5_530GatherLaw := rfl

/-- The exact catalogue table satisfies both displayed laws. -/
theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, s5_530Basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact table.checkIdentityNat_sound finiteGatherLaw (by decide)

/-- Quotient recording the sequence of first occurrences. Zero-based
elements `0,1,2` collapse to one left-zero value, `3` is the other
left-zero value, and `4` is the identity. -/
def leftRegularBandQuotient :
    SplitSurjection table.semigroup leftRegularBandThree.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨1, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨4, by decide⟩ else ⟨3, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- Quotient recording multiplicity zero, one, two, or at least three. -/
def exponentFourQuotient :
    SplitSurjection table.semigroup commutativeExponentFour.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨2, by decide⟩ else
          if a.val = 3 then ⟨0, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else
        if b.val = 2 then ⟨2, by decide⟩ else ⟨4, by decide⟩
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

theorem valid_capped_count_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z,
      s5_530Exponent (identity.lhs.toList.count z) =
        s5_530Exponent (identity.rhs.toList.count z) := by
  intro z
  simpa [s5_530Exponent] using
    exponentFourValid_capped_count_eq identity
      (exponentFourQuotient.pushforwardIdentity identity valid) z

/-- One-based table element `5` is the identity. -/
def identityElement : Fin 5 := 4

/-- One-based table elements `1` and `4` uniformly detect block order. -/
def firstOrderWitness : Fin 5 := 0
def secondOrderWitness : Fin 5 := 3

theorem identityElement_certificate (a : Fin 5) :
    Generated.Catalogue.S5_530.mul identityElement a = a ∧
      Generated.Catalogue.S5_530.mul a identityElement = a := by
  revert a
  decide

def powerProfilesOneBased : List (List Nat) :=
  [
    List.ofFn (fun a : Fin 5 => a.val + 1),
    List.ofFn (fun a : Fin 5 =>
      (Generated.Catalogue.S5_530.mul a a).val + 1),
    List.ofFn (fun a : Fin 5 =>
      (Generated.Catalogue.S5_530.mul
        (Generated.Catalogue.S5_530.mul a a) a).val + 1)
  ]

theorem powerProfilesOneBased_certificate :
    powerProfilesOneBased =
      [[1, 2, 3, 4, 5], [1, 1, 2, 4, 5], [1, 1, 1, 4, 5]] := by
  decide

def witnessPower (witness : Fin 5) (_ : Fin 3) : Fin 5 :=
  witness

/-- All nine pairs of positive capped exponents preserve the same strict
order witness: `1^i * 4^j = 1`, while `4^j * 1^i = 4`. -/
theorem uniformOrderWitness_certificate (i j : Fin 3) :
    Generated.Catalogue.S5_530.mul
        (witnessPower firstOrderWitness i)
        (witnessPower secondOrderWitness j) =
          firstOrderWitness ∧
      Generated.Catalogue.S5_530.mul
        (witnessPower secondOrderWitness j)
        (witnessPower firstOrderWitness i) =
          secondOrderWitness := by
  revert i j
  decide

theorem representative_basis :
    BasisFor table.semigroup basis :=
  s5_530Basis_complete_of_invariants table models
    valid_firstOccurrenceSequence_eq valid_capped_count_eq

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def s5_530YXX : Word Nat := ⟨1, [0, 0]⟩

def expectedOppositeBasis : List (Identity Nat) :=
  [s5_530PowerLaw, ⟨s5_530YXX, s5_530XYX⟩]

theorem oppositeBasis_eq_expected :
    oppositeBasis = expectedOppositeBasis := by
  rfl

theorem opposite_basis :
    BasisFor table.semigroup.opposite expectedOppositeBasis := by
  rw [← oppositeBasis_eq_expected]
  exact representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.S5_530

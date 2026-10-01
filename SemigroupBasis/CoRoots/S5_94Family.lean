import SemigroupBasis.CoRoots.S5_94
import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_94Family

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_94

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun e => e.map toFinFour

private theorem basis_roundTrip_checked :
    basis.all (fun e =>
      decide ((e.map toFinFour).map Fin.val = e)) = true := by
  decide

private theorem basis_roundTrip
    (e : Identity Nat) (member : e ∈ basis) :
    (e.map toFinFour).map Fin.val = e := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) e member

private theorem models_of_finite_checks
    (T : FiniteTable)
    (checked : finiteBasis.all T.checkIdentity = true) :
    Models T.semigroup basis := by
  intro e member
  have finiteMember : e.map toFinFour ∈ finiteBasis :=
    List.mem_map.mpr ⟨e, member, rfl⟩
  have finiteValid :=
    T.checkIdentityNat_sound (e.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip e member] at finiteValid
  exact finiteValid

private def swapOneTwo : Fin 5 → Fin 5
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 3
  | 4 => 4

private theorem swapOneTwo_injective : Function.Injective swapOneTwo := by
  intro a b
  revert a b
  decide

private def swapTwoThree : Fin 5 → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2
  | 4 => 4

private theorem swapTwoThree_injective : Function.Injective swapTwoThree := by
  intro a b
  revert a b
  decide

namespace S5_94

private def exponentEmbedding :
    Embedding commutativeExponentThree.semigroup
      Generated.Catalogue.S5_94.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

private def simpleEndpointsQuotient :
    SplitSurjection Generated.Catalogue.S5_94.table.semigroup
      simpleEndpointsFour.semigroup where
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

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_94.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_94.table (by decide)

theorem valid_simpleEndpoints (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_94.table.semigroup) :
    e.SatisfiedBy simpleEndpointsFour.semigroup :=
  simpleEndpointsQuotient.pushforwardIdentity e valid

theorem valid_exponentThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_94.table.semigroup) :
    e.SatisfiedBy commutativeExponentThree.semigroup :=
  exponentEmbedding.pullback_identity e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_94.table.semigroup basis :=
  basis_complete_of_factors Generated.Catalogue.S5_94.table
    models valid_simpleEndpoints valid_exponentThree

def selfDualEmbedding :
    Embedding Generated.Catalogue.S5_94.table.semigroup.opposite
      Generated.Catalogue.S5_94.table.semigroup where
  toFun := swapOneTwo
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := swapOneTwo_injective

theorem selfDualInvolution (a : Fin 5) :
    selfDualEmbedding.toFun (selfDualEmbedding.toFun a) = a := by
  revert a
  decide

end S5_94

namespace S5_95

private def exponentEmbedding :
    Embedding commutativeExponentThree.semigroup
      Generated.Catalogue.S5_95.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨2, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

private def simpleEndpointsQuotient :
    SplitSurjection Generated.Catalogue.S5_95.table.semigroup
      simpleEndpointsFour.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else
        if b.val = 2 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_95.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_95.table (by decide)

theorem valid_simpleEndpoints (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_95.table.semigroup) :
    e.SatisfiedBy simpleEndpointsFour.semigroup :=
  simpleEndpointsQuotient.pushforwardIdentity e valid

theorem valid_exponentThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_95.table.semigroup) :
    e.SatisfiedBy commutativeExponentThree.semigroup :=
  exponentEmbedding.pullback_identity e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_95.table.semigroup basis :=
  basis_complete_of_factors Generated.Catalogue.S5_95.table
    models valid_simpleEndpoints valid_exponentThree

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_95.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_95

namespace S5_104

private def exponentEmbedding :
    Embedding commutativeExponentThree.semigroup
      Generated.Catalogue.S5_104.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

private def simpleEndpointsQuotient :
    SplitSurjection Generated.Catalogue.S5_104.table.semigroup
      simpleEndpointsFour.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨2, by decide⟩ else
        if b.val = 2 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_104.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_104.table (by decide)

theorem valid_simpleEndpoints (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_104.table.semigroup) :
    e.SatisfiedBy simpleEndpointsFour.semigroup :=
  simpleEndpointsQuotient.pushforwardIdentity e valid

theorem valid_exponentThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_104.table.semigroup) :
    e.SatisfiedBy commutativeExponentThree.semigroup :=
  exponentEmbedding.pullback_identity e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_104.table.semigroup basis :=
  basis_complete_of_factors Generated.Catalogue.S5_104.table
    models valid_simpleEndpoints valid_exponentThree

def selfDualEmbedding :
    Embedding Generated.Catalogue.S5_104.table.semigroup.opposite
      Generated.Catalogue.S5_104.table.semigroup where
  toFun := swapTwoThree
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := swapTwoThree_injective

theorem selfDualInvolution (a : Fin 5) :
    selfDualEmbedding.toFun (selfDualEmbedding.toFun a) = a := by
  revert a
  decide

end S5_104

end SemigroupBasis.CoRoots.S5_94Family

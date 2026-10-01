import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.Examples.SimpleEndpointsFour
import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_107Factors

open SemigroupBasis
open SemigroupBasis.Examples

/-- The common copy of the exponent-three semigroup in each root. -/
def exponentMap (a : Fin 3) : Fin 5 :=
  if a.val = 0 then ⟨0, by decide⟩ else
    if a.val = 1 then ⟨1, by decide⟩ else ⟨4, by decide⟩

/-- The common quotient map `[0, 0, 2, 1, 3]` onto `simpleEndpointsFour`. -/
def simpleEndpointsMap (a : Fin 5) : Fin 4 :=
  if a.val = 0 then ⟨0, by decide⟩ else
    if a.val = 1 then ⟨0, by decide⟩ else
      if a.val = 2 then ⟨2, by decide⟩ else
        if a.val = 3 then ⟨1, by decide⟩ else ⟨3, by decide⟩

/-- A chosen section of `simpleEndpointsMap`. -/
def simpleEndpointsPreimage (a : Fin 4) : Fin 5 :=
  if a.val = 0 then ⟨0, by decide⟩ else
    if a.val = 1 then ⟨3, by decide⟩ else
      if a.val = 2 then ⟨2, by decide⟩ else ⟨4, by decide⟩

private def initialSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 3

private def finalSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 3

private theorem simpleInitial_of_valid
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (valid :
      (Identity.mk
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
          simpleEndpointsFour.semigroup) :
    ∀ z,
      (initial₁ = z ∧ z ∉ middle₁ ∧ final₁ ≠ z) ↔
        (initial₂ = z ∧ z ∉ middle₂ ∧ final₂ ≠ z) := by
  intro z
  have evaluated := valid (initialSeparator z)
  constructor
  · intro simple₁
    have lhsTwo :
        simpleEndpointsFour.semigroup.eval (initialSeparator z)
          (wordOfEndpoints initial₁ middle₁ final₁) = (2 : Fin 4) := by
      simpa [initialSeparator] using
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          z initial₁ middle₁ final₁).2 simple₁
    have rhsTwo := evaluated.symm.trans lhsTwo
    exact
      (simpleEndpointsEval_initialSeparator_eq_two_iff
        z initial₂ middle₂ final₂).1 <| by
          simpa [initialSeparator] using rhsTwo
  · intro simple₂
    have rhsTwo :
        simpleEndpointsFour.semigroup.eval (initialSeparator z)
          (wordOfEndpoints initial₂ middle₂ final₂) = (2 : Fin 4) := by
      simpa [initialSeparator] using
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          z initial₂ middle₂ final₂).2 simple₂
    have lhsTwo := evaluated.trans rhsTwo
    exact
      (simpleEndpointsEval_initialSeparator_eq_two_iff
        z initial₁ middle₁ final₁).1 <| by
          simpa [initialSeparator] using lhsTwo

private theorem simpleFinal_of_valid
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (valid :
      (Identity.mk
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
          simpleEndpointsFour.semigroup) :
    ∀ z,
      (final₁ = z ∧ z ∉ initial₁ :: middle₁) ↔
        (final₂ = z ∧ z ∉ initial₂ :: middle₂) := by
  intro z
  have evaluated := valid (finalSeparator z)
  constructor
  · intro simple₁
    have lhsOne :
        simpleEndpointsFour.semigroup.eval (finalSeparator z)
          (wordOfEndpoints initial₁ middle₁ final₁) = (1 : Fin 4) := by
      simpa [finalSeparator] using
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          z initial₁ middle₁ final₁).2 simple₁
    have rhsOne := evaluated.symm.trans lhsOne
    exact
      (simpleEndpointsEval_finalSeparator_eq_one_iff
        z initial₂ middle₂ final₂).1 <| by
          simpa [finalSeparator] using rhsOne
  · intro simple₂
    have rhsOne :
        simpleEndpointsFour.semigroup.eval (finalSeparator z)
          (wordOfEndpoints initial₂ middle₂ final₂) = (1 : Fin 4) := by
      simpa [finalSeparator] using
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          z initial₂ middle₂ final₂).2 simple₂
    have lhsOne := evaluated.trans rhsOne
    exact
      (simpleEndpointsEval_finalSeparator_eq_one_iff
        z initial₁ middle₁ final₁).1 <| by
          simpa [finalSeparator] using lhsOne

namespace S5_107

def exponentEmbedding :
    Embedding commutativeExponentThree.semigroup
      Generated.Catalogue.S5_107.table.semigroup where
  toFun := exponentMap
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

def simpleEndpointsQuotient :
    SplitSurjection Generated.Catalogue.S5_107.table.semigroup
      simpleEndpointsFour.semigroup where
  toFun := simpleEndpointsMap
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := simpleEndpointsPreimage
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_exponentThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_107.table.semigroup) :
    e.SatisfiedBy commutativeExponentThree.semigroup :=
  exponentEmbedding.pullback_identity e valid

theorem valid_simpleEndpoints (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_107.table.semigroup) :
    e.SatisfiedBy simpleEndpointsFour.semigroup :=
  simpleEndpointsQuotient.pushforwardIdentity e valid

theorem valid_capped_count_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_107.table.semigroup) :
    ∀ z, min (e.lhs.toList.count z) 2 =
      min (e.rhs.toList.count z) 2 :=
  exponentValid_capped_count_eq e (valid_exponentThree e valid)

theorem valid_simpleInitial
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (valid :
      (Identity.mk
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
          Generated.Catalogue.S5_107.table.semigroup) :
    ∀ z,
      (initial₁ = z ∧ z ∉ middle₁ ∧ final₁ ≠ z) ↔
        (initial₂ = z ∧ z ∉ middle₂ ∧ final₂ ≠ z) :=
  simpleInitial_of_valid initial₁ middle₁ final₁
    initial₂ middle₂ final₂
    (valid_simpleEndpoints _ valid)

theorem valid_simpleFinal
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (valid :
      (Identity.mk
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
          Generated.Catalogue.S5_107.table.semigroup) :
    ∀ z,
      (final₁ = z ∧ z ∉ initial₁ :: middle₁) ↔
        (final₂ = z ∧ z ∉ initial₂ :: middle₂) :=
  simpleFinal_of_valid initial₁ middle₁ final₁
    initial₂ middle₂ final₂
    (valid_simpleEndpoints _ valid)

end S5_107

namespace S5_108

def exponentEmbedding :
    Embedding commutativeExponentThree.semigroup
      Generated.Catalogue.S5_108.table.semigroup where
  toFun := exponentMap
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

def simpleEndpointsQuotient :
    SplitSurjection Generated.Catalogue.S5_108.table.semigroup
      simpleEndpointsFour.semigroup where
  toFun := simpleEndpointsMap
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := simpleEndpointsPreimage
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_exponentThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_108.table.semigroup) :
    e.SatisfiedBy commutativeExponentThree.semigroup :=
  exponentEmbedding.pullback_identity e valid

theorem valid_simpleEndpoints (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_108.table.semigroup) :
    e.SatisfiedBy simpleEndpointsFour.semigroup :=
  simpleEndpointsQuotient.pushforwardIdentity e valid

theorem valid_capped_count_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_108.table.semigroup) :
    ∀ z, min (e.lhs.toList.count z) 2 =
      min (e.rhs.toList.count z) 2 :=
  exponentValid_capped_count_eq e (valid_exponentThree e valid)

theorem valid_simpleInitial
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (valid :
      (Identity.mk
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
          Generated.Catalogue.S5_108.table.semigroup) :
    ∀ z,
      (initial₁ = z ∧ z ∉ middle₁ ∧ final₁ ≠ z) ↔
        (initial₂ = z ∧ z ∉ middle₂ ∧ final₂ ≠ z) :=
  simpleInitial_of_valid initial₁ middle₁ final₁
    initial₂ middle₂ final₂
    (valid_simpleEndpoints _ valid)

theorem valid_simpleFinal
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (valid :
      (Identity.mk
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
          Generated.Catalogue.S5_108.table.semigroup) :
    ∀ z,
      (final₁ = z ∧ z ∉ initial₁ :: middle₁) ↔
        (final₂ = z ∧ z ∉ initial₂ :: middle₂) :=
  simpleFinal_of_valid initial₁ middle₁ final₁
    initial₂ middle₂ final₂
    (valid_simpleEndpoints _ valid)

end S5_108

namespace S5_109

def exponentEmbedding :
    Embedding commutativeExponentThree.semigroup
      Generated.Catalogue.S5_109.table.semigroup where
  toFun := exponentMap
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

def simpleEndpointsQuotient :
    SplitSurjection Generated.Catalogue.S5_109.table.semigroup
      simpleEndpointsFour.semigroup where
  toFun := simpleEndpointsMap
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := simpleEndpointsPreimage
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_exponentThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_109.table.semigroup) :
    e.SatisfiedBy commutativeExponentThree.semigroup :=
  exponentEmbedding.pullback_identity e valid

theorem valid_simpleEndpoints (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_109.table.semigroup) :
    e.SatisfiedBy simpleEndpointsFour.semigroup :=
  simpleEndpointsQuotient.pushforwardIdentity e valid

theorem valid_capped_count_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_109.table.semigroup) :
    ∀ z, min (e.lhs.toList.count z) 2 =
      min (e.rhs.toList.count z) 2 :=
  exponentValid_capped_count_eq e (valid_exponentThree e valid)

theorem valid_simpleInitial
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (valid :
      (Identity.mk
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
          Generated.Catalogue.S5_109.table.semigroup) :
    ∀ z,
      (initial₁ = z ∧ z ∉ middle₁ ∧ final₁ ≠ z) ↔
        (initial₂ = z ∧ z ∉ middle₂ ∧ final₂ ≠ z) :=
  simpleInitial_of_valid initial₁ middle₁ final₁
    initial₂ middle₂ final₂
    (valid_simpleEndpoints _ valid)

theorem valid_simpleFinal
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (valid :
      (Identity.mk
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
          Generated.Catalogue.S5_109.table.semigroup) :
    ∀ z,
      (final₁ = z ∧ z ∉ initial₁ :: middle₁) ↔
        (final₂ = z ∧ z ∉ initial₂ :: middle₂) :=
  simpleFinal_of_valid initial₁ middle₁ final₁
    initial₂ middle₂ final₂
    (valid_simpleEndpoints _ valid)

end S5_109

end SemigroupBasis.CoRoots.S5_107Factors

import SemigroupBasis.Generated.S4_21
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.Generated.S4_23

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_23`, with exact table
`[[1,1,1,1],[1,1,1,2],[1,1,1,2],[1,2,3,4]]`. -/
abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S4_23.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_23.table := rfl

/-- Multiplication on the five-element subsemigroup of `S4_23^2` whose
one-based elements are `(1,1), (1,2), (1,3), (2,1), (4,4)`. -/
def divisorSubMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then 0 else
    if a = 1 then (if b = 4 then 1 else 0) else
      if a = 2 then (if b = 4 then 1 else 0) else
        if a = 3 then (if b = 4 then 3 else 0) else b

def divisorSubTable : FiniteTable where
  order := 5
  mul := divisorSubMul
  assoc := by decide

/-- The explicit inclusion of the five listed elements into `S4_23^2`. -/
def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    (if i = 0 then
      if a = 0 then (0 : Fin 4) else
        if a = 1 then 0 else
          if a = 2 then 0 else
            if a = 3 then 1 else 3
    else
      if a = 0 then (0 : Fin 4) else
        if a = 1 then 1 else
          if a = 2 then 2 else
            if a = 3 then 0 else 3
      : Fin 4)
  map_mul := by
    intro a b
    funext i
    exact by decide +revert
  injective := by
    intro a b h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    clear h
    exact by decide +revert

/-- The quotient map `[1,1,2,3,4]` in one-based notation. -/
def divisorQuotient :
    SplitSurjection divisorSubTable.semigroup
      SemigroupBasis.Generated.S4_21.table.semigroup where
  toFun := fun a : Fin 5 =>
    (if a = 0 then (0 : Fin 4) else
      if a = 1 then 0 else
        if a = 2 then 1 else
          if a = 3 then 2 else 3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    (if b = 0 then (0 : Fin 5) else
      if b = 1 then 2 else
        if b = 2 then 3 else 4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finitePrefixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteSquareCommutationLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem finitePrefixCommutationLaw_map :
    finitePrefixCommutationLaw.map Fin.val =
      edmundsFourTwentyOnePrefixCommutationLaw := rfl

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val =
      edmundsFourTwentyOnePowerLaw := rfl

theorem finiteSquareCommutationLaw_map :
    finiteSquareCommutationLaw.map Fin.val =
      edmundsFourTwentyOneSquareCommutationLaw := rfl

theorem representative_models :
    Models table.semigroup edmundsFourTwentyOneBasis := by
  intro e he
  simp only [edmundsFourTwentyOneBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · rw [← finitePrefixCommutationLaw_map]
    exact table.checkIdentityNat_sound
      finitePrefixCommutationLaw (by decide)
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteSquareCommutationLaw_map]
    exact table.checkIdentityNat_sound
      finiteSquareCommutationLaw (by decide)

theorem representative_basis :
    BasisFor table.semigroup edmundsFourTwentyOneBasis :=
  SemigroupBasis.Generated.S4_21.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient representative_models

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis edmundsFourTwentyOneBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_23

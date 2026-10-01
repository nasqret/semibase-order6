import SemigroupBasis.Generated.S4_72
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.Generated.S4_76

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_76`, with exact table
`[[1,1,1,1],[1,1,1,2],[3,3,3,3],[3,3,3,4]]`. -/
abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S4_76.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_76.table := rfl

/-- Multiplication on the five-element subsemigroup of `S4_76^2` whose
one-based elements are `(1,1), (1,3), (1,4), (3,1), (3,2)`. -/
def divisorSubMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then 0 else
    if a = 1 then 1 else
      if a = 2 then (if b = 2 then 2 else 1) else
        if a = 3 then 3 else
          if b = 2 then 4 else 3

def divisorSubTable : FiniteTable where
  order := 5
  mul := divisorSubMul
  assoc := by decide

/-- The explicit inclusion of the five listed elements into `S4_76^2`. -/
def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    (if i = 0 then
      if a = 0 then (0 : Fin 4) else
        if a = 1 then 0 else
          if a = 2 then 0 else 2
    else
      if a = 0 then (0 : Fin 4) else
        if a = 1 then 2 else
          if a = 2 then 3 else
            if a = 3 then 0 else 1
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

/-- The quotient map `[3,1,4,1,2]` in one-based notation. -/
def divisorQuotient :
    SplitSurjection divisorSubTable.semigroup
      SemigroupBasis.Generated.S4_72.table.semigroup where
  toFun := fun a : Fin 5 =>
    (if a = 0 then (2 : Fin 4) else
      if a = 1 then 0 else
        if a = 2 then 3 else
          if a = 3 then 0 else 1 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    (if b = 0 then (1 : Fin 5) else
      if b = 1 then 4 else
        if b = 2 then 0 else 2 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteRightDuplicationLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def finiteRepeatedFirstLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = firstCappedPowerLaw := rfl

theorem finiteRightDuplicationLaw_map :
    finiteRightDuplicationLaw.map Fin.val =
      firstRepeatedRightDuplicationLaw := rfl

theorem finiteRepeatedFirstLaw_map :
    finiteRepeatedFirstLaw.map Fin.val =
      firstCappedRepeatedFirstLaw := rfl

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      firstCappedSuffixCommutationLaw := rfl

theorem representative_models :
    Models table.semigroup firstRepeatedMarkerFourBasis := by
  intro e he
  simp only [firstRepeatedMarkerFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteRightDuplicationLaw_map]
    exact table.checkIdentityNat_sound finiteRightDuplicationLaw (by decide)
  · rw [← finiteRepeatedFirstLaw_map]
    exact table.checkIdentityNat_sound finiteRepeatedFirstLaw (by decide)
  · rw [← finiteSuffixCommutationLaw_map]
    exact table.checkIdentityNat_sound finiteSuffixCommutationLaw (by decide)

theorem representative_basis :
    BasisFor table.semigroup firstRepeatedMarkerFourBasis :=
  SemigroupBasis.Generated.S4_72.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient representative_models

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis firstRepeatedMarkerFourBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_76

import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Generated.S4_13
import SemigroupBasis.FiniteReflection
import SemigroupBasis.TransferPower

namespace SemigroupBasis.Generated.S4_12

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_12`. -/
abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S4_12.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_12.table := rfl

/-- The diagonal of the separating homomorphisms
`[1,2,1,4]` and `[1,1,3,3]`, embedding `S4_13` into `S4_12²`. -/
def sourceEmbedding :
    Embedding SemigroupBasis.Generated.S4_13.table.semigroup
      (table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    (if i = 0 then
      if a = 0 then (0 : Fin 4) else
        if a = 1 then 1 else
          if a = 2 then 0 else 3
    else
      if a = 0 then (0 : Fin 4) else
        if a = 1 then 0 else
          if a = 2 then 2 else 2
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

def finiteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def finiteLongCancellationLaw : Identity (Fin 4) :=
  ⟨⟨0, [0, 1, 2, 3]⟩, ⟨1, [2, 3]⟩⟩

theorem finiteCommutativityLaw_map :
    finiteCommutativityLaw.map Fin.val =
      cyclicThreeTwoCommutativityLaw := rfl

theorem finiteLongCancellationLaw_map :
    finiteLongCancellationLaw.map Fin.val =
      cyclicThreeTwoLongCancellationLaw := rfl

set_option maxRecDepth 100000 in
theorem representative_models :
    Models table.semigroup cyclicThreeTwoBasis := by
  intro e he
  simp only [cyclicThreeTwoBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteCommutativityLaw_map]
    exact table.checkIdentityNat_sound finiteCommutativityLaw (by decide)
  · rw [← finiteLongCancellationLaw_map]
    exact table.checkIdentityNat_sound finiteLongCancellationLaw (by decide)

theorem representative_basis :
    BasisFor table.semigroup cyclicThreeTwoBasis :=
  SemigroupBasis.BasisFor.inheritAlongPowerEmbedding
    SemigroupBasis.Generated.S4_13.representative_basis
    sourceEmbedding representative_models

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis cyclicThreeTwoBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_12

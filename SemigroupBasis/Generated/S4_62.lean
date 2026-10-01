import SemigroupBasis.Generated.S4_60
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.Generated.S4_62

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_62`, with exact table
`[[1,1,1,1],[1,1,1,1],[1,2,3,3],[1,2,4,4]]`. -/
abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S4_62.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_62.table := rfl

/-- The one-based embedding
`1 ↦ (1,3), 2 ↦ (2,3), 3 ↦ (3,3), 4 ↦ (1,4)`
of `S4_60` into `S4_62²`. -/
def sourceEmbedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      (table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    (if i = 0 then
      if a = 0 then (0 : Fin 4) else
        if a = 1 then 1 else
          if a = 2 then 2 else 0
    else
      if a = 0 then (2 : Fin 4) else
        if a = 1 then 2 else
          if a = 2 then 2 else 3
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

def finiteInitialGatherLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def finiteFinalGatherLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def finiteLeftContractionLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def finiteFinalSwitchLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem finiteInitialGatherLaw_map :
    finiteInitialGatherLaw.map Fin.val =
      edmundsFourSixtyInitialGatherLaw := rfl

theorem finiteFinalGatherLaw_map :
    finiteFinalGatherLaw.map Fin.val =
      edmundsFourSixtyFinalGatherLaw := rfl

theorem finiteLeftContractionLaw_map :
    finiteLeftContractionLaw.map Fin.val =
      edmundsFourSixtyLeftContractionLaw := rfl

theorem finiteFinalSwitchLaw_map :
    finiteFinalSwitchLaw.map Fin.val =
      edmundsFourSixtyFinalSwitchLaw := rfl

theorem representative_models :
    Models table.semigroup edmundsFourSixtyBasis := by
  intro e he
  simp only [edmundsFourSixtyBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [← finiteInitialGatherLaw_map]
    exact table.checkIdentityNat_sound finiteInitialGatherLaw (by decide)
  · rw [← finiteFinalGatherLaw_map]
    exact table.checkIdentityNat_sound finiteFinalGatherLaw (by decide)
  · rw [← finiteLeftContractionLaw_map]
    exact table.checkIdentityNat_sound finiteLeftContractionLaw (by decide)
  · rw [← finiteFinalSwitchLaw_map]
    exact table.checkIdentityNat_sound finiteFinalSwitchLaw (by decide)

theorem representative_basis :
    BasisFor table.semigroup edmundsFourSixtyBasis :=
  SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongPowerEmbedding
    sourceEmbedding representative_models

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis edmundsFourSixtyBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_62

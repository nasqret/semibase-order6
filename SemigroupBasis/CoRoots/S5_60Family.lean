import SemigroupBasis.CoRoots.S5_60
import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_60Family

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_60

namespace S5_66

abbrev table : FiniteTable := cyclicFourTwo

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_66.table := by
  unfold table cyclicFourTwo cyclicFourTwoMul
    SemigroupBasis.Generated.Catalogue.S5_66.table
    SemigroupBasis.Generated.Catalogue.S5_66.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_66.table.semigroup
      basis := by
  rw [← table_eq_canonical_catalogue]
  exact cyclicFourTwoBasis_complete

theorem self_dual :
    SemigroupBasis.Generated.Catalogue.S5_66.table.semigroup.opposite =
      SemigroupBasis.Generated.Catalogue.S5_66.table.semigroup := by
  rw [← table_eq_canonical_catalogue]
  exact cyclicFourTwo_selfDual

theorem opposite_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_66.table.semigroup.opposite
      basis := by
  rw [self_dual]
  exact representative_basis

end S5_66

namespace S5_60

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_60.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_60.table := rfl

/-- The diagonal of the two recorded one-based homomorphisms
`[1,2,1,3,5]` and `[1,1,4,4,4]`. -/
def sourceEmbedding :
    Embedding
      SemigroupBasis.Generated.Catalogue.S5_66.table.semigroup
      (table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    (if i = 0 then
      if a = 0 then (0 : Fin 5) else
        if a = 1 then 1 else
          if a = 2 then 0 else
            if a = 3 then 2 else 4
    else
      if a = 0 then (0 : Fin 5) else
        if a = 1 then 0 else
          if a = 2 then 3 else
            if a = 3 then 3 else 3
      : Fin 5)
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

def finiteLongCancellationLaw : Identity (Fin 5) :=
  ⟨⟨0, [0, 1, 2, 3, 4]⟩, ⟨1, [2, 3, 4]⟩⟩

theorem finiteCommutativityLaw_map :
    finiteCommutativityLaw.map Fin.val =
      cyclicFourTwoCommutativityLaw := rfl

theorem finiteLongCancellationLaw_map :
    finiteLongCancellationLaw.map Fin.val =
      cyclicFourTwoLongCancellationLaw := rfl

set_option maxRecDepth 100000 in
theorem representative_models :
    Models table.semigroup basis := by
  intro identity member
  simp only [basis, cyclicFourTwoBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [← finiteCommutativityLaw_map]
    exact table.checkIdentityNat_sound finiteCommutativityLaw (by decide)
  · rw [← finiteLongCancellationLaw_map]
    exact table.checkIdentityNat_sound
      finiteLongCancellationLaw (by decide)

theorem representative_basis :
    BasisFor table.semigroup basis :=
  S5_66.representative_basis.inheritAlongPowerEmbedding
    sourceEmbedding representative_models

theorem self_dual :
    table.semigroup.opposite = table.semigroup := by
  unfold table SemigroupBasis.Generated.Catalogue.S5_60.table
    SemigroupBasis.Generated.Catalogue.S5_60.mul
    FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  apply Fin.ext
  decide +revert

theorem opposite_basis :
    BasisFor table.semigroup.opposite basis := by
  rw [self_dual]
  exact representative_basis

end S5_60

end SemigroupBasis.CoRoots.S5_60Family

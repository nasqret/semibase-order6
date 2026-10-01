import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.CoRoots.S5_97Family
import SemigroupBasis.FiniteReflection
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.S5_97Transfers

open SemigroupBasis

-- BEGIN S5_114
namespace S5_114

def powerEmbedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_97.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_114.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else (0 : Fin 5) else if a = 0 then (4 : Fin 5) else if a = 1 then (4 : Fin 5) else if a = 2 then (4 : Fin 5) else if a = 3 then (4 : Fin 5) else (0 : Fin 5)
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

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def finiteTransferLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 1]⟩⟩

def finiteLongInsertionLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_114.table.semigroup
      SemigroupBasis.CoRoots.S5_97.basis := by
  intro e he
  simp only [
    SemigroupBasis.CoRoots.S5_97.basis,
    List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · change (finitePowerLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_114.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_114.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · change (finiteCommutativityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_114.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_114.table.checkIdentityNat_sound
      finiteCommutativityLaw (by decide)
  · change (finiteTransferLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_114.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_114.table.checkIdentityNat_sound
      finiteTransferLaw (by decide)
  · change (finiteLongInsertionLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_114.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_114.table.checkIdentityNat_sound
      finiteLongInsertionLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_114.table.semigroup
      SemigroupBasis.CoRoots.S5_97.basis :=
  SemigroupBasis.CoRoots.S5_97Family.S5_97.basis_complete.inheritAlongPowerEmbedding
    powerEmbedding targetModels


end S5_114
-- END S5_114

end SemigroupBasis.Generated.S5_97Transfers

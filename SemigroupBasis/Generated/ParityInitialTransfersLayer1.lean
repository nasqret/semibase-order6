import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S4_95
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.ParityInitialTransfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S5_972
namespace S5_972

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_95.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_972.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (3 : Fin 5) else if a = 0 then (2 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
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
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = parityInitialPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = parityInitialGatherLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_972.table.semigroup parityInitialBasis := by
  intro e he
  simp only [parityInitialBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_972.table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_972.table.checkIdentityNat_sound finiteGatherLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_972.table.semigroup
      parityInitialBasis :=
  SemigroupBasis.Generated.S4_95.representative_basis.inheritAlongPowerEmbedding
    powerEmbedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_972.table.semigroup.opposite
      (reversedBasis parityInitialBasis) :=
  representative_basis.oppositeReversed

end S5_972
-- END S5_972

-- BEGIN S5_974
namespace S5_974

def embedding :
    Embedding SemigroupBasis.Generated.S4_95.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_974.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = parityInitialPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = parityInitialGatherLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_974.table.semigroup parityInitialBasis := by
  intro e he
  simp only [parityInitialBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_974.table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_974.table.checkIdentityNat_sound finiteGatherLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_974.table.semigroup
      parityInitialBasis :=
  SemigroupBasis.Generated.S4_95.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_974.table.semigroup.opposite
      (reversedBasis parityInitialBasis) :=
  representative_basis.oppositeReversed

end S5_974
-- END S5_974

-- BEGIN S5_980
namespace S5_980

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_95.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_980.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (2 : Fin 5) else if a = 0 then (3 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
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
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = parityInitialPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = parityInitialGatherLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_980.table.semigroup parityInitialBasis := by
  intro e he
  simp only [parityInitialBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_980.table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_980.table.checkIdentityNat_sound finiteGatherLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_980.table.semigroup
      parityInitialBasis :=
  SemigroupBasis.Generated.S4_95.representative_basis.inheritAlongPowerEmbedding
    powerEmbedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_980.table.semigroup.opposite
      (reversedBasis parityInitialBasis) :=
  representative_basis.oppositeReversed

end S5_980
-- END S5_980

-- BEGIN S5_984
namespace S5_984

def embedding :
    Embedding SemigroupBasis.Generated.S4_95.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_984.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = parityInitialPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = parityInitialGatherLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_984.table.semigroup parityInitialBasis := by
  intro e he
  simp only [parityInitialBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_984.table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_984.table.checkIdentityNat_sound finiteGatherLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_984.table.semigroup
      parityInitialBasis :=
  SemigroupBasis.Generated.S4_95.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_984.table.semigroup.opposite
      (reversedBasis parityInitialBasis) :=
  representative_basis.oppositeReversed

end S5_984
-- END S5_984

-- BEGIN S5_986
namespace S5_986

def embedding :
    Embedding SemigroupBasis.Generated.S4_95.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_986.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = parityInitialPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = parityInitialGatherLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_986.table.semigroup parityInitialBasis := by
  intro e he
  simp only [parityInitialBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_986.table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_986.table.checkIdentityNat_sound finiteGatherLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_986.table.semigroup
      parityInitialBasis :=
  SemigroupBasis.Generated.S4_95.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_986.table.semigroup.opposite
      (reversedBasis parityInitialBasis) :=
  representative_basis.oppositeReversed

end S5_986
-- END S5_986

-- BEGIN S5_992
namespace S5_992

def embedding :
    Embedding SemigroupBasis.Generated.S4_95.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_992.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = parityInitialPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = parityInitialGatherLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_992.table.semigroup parityInitialBasis := by
  intro e he
  simp only [parityInitialBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_992.table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_992.table.checkIdentityNat_sound finiteGatherLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_992.table.semigroup
      parityInitialBasis :=
  SemigroupBasis.Generated.S4_95.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_992.table.semigroup.opposite
      (reversedBasis parityInitialBasis) :=
  representative_basis.oppositeReversed

end S5_992
-- END S5_992

-- BEGIN S5_994
namespace S5_994

def embedding :
    Embedding SemigroupBasis.Generated.S4_95.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = parityInitialPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = parityInitialGatherLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup parityInitialBasis := by
  intro e he
  simp only [parityInitialBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_994.table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_994.table.checkIdentityNat_sound finiteGatherLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup
      parityInitialBasis :=
  SemigroupBasis.Generated.S4_95.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite
      (reversedBasis parityInitialBasis) :=
  representative_basis.oppositeReversed

end S5_994
-- END S5_994

-- BEGIN S5_995
namespace S5_995

def embedding :
    Embedding SemigroupBasis.Generated.S4_95.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_995.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = parityInitialPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = parityInitialGatherLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_995.table.semigroup parityInitialBasis := by
  intro e he
  simp only [parityInitialBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_995.table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_995.table.checkIdentityNat_sound finiteGatherLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_995.table.semigroup
      parityInitialBasis :=
  SemigroupBasis.Generated.S4_95.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_995.table.semigroup.opposite
      (reversedBasis parityInitialBasis) :=
  representative_basis.oppositeReversed

end S5_995
-- END S5_995

-- BEGIN S5_996
namespace S5_996

def embedding :
    Embedding SemigroupBasis.Generated.S4_95.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_996.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = parityInitialPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = parityInitialGatherLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_996.table.semigroup parityInitialBasis := by
  intro e he
  simp only [parityInitialBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_996.table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_996.table.checkIdentityNat_sound finiteGatherLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_996.table.semigroup
      parityInitialBasis :=
  SemigroupBasis.Generated.S4_95.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_996.table.semigroup.opposite
      (reversedBasis parityInitialBasis) :=
  representative_basis.oppositeReversed

end S5_996
-- END S5_996

end SemigroupBasis.Generated.ParityInitialTransfers

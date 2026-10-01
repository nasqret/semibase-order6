import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S4_110
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.NormalBandTransfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S5_1022
namespace S5_1022

def embedding :
    Embedding SemigroupBasis.Generated.S4_110.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1022.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteInteriorSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      normalBandIdempotenceLaw := rfl

theorem finiteInteriorSwapLaw_map :
    finiteInteriorSwapLaw.map Fin.val =
      normalBandInteriorSwapLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1022.table.semigroup normalBandBasis := by
  intro e he
  simp only [normalBandBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1022.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteInteriorSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1022.table.checkIdentityNat_sound
      finiteInteriorSwapLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1022.table.semigroup
      normalBandBasis :=
  SemigroupBasis.Generated.S4_110.representative_basis.inheritAlongEmbedding
    embedding targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1022.table.semigroup.opposite
      (reversedBasis normalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1022
-- END S5_1022

-- BEGIN S5_1040
namespace S5_1040

def embedding :
    Embedding SemigroupBasis.Generated.S4_110.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1040.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (0 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteInteriorSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      normalBandIdempotenceLaw := rfl

theorem finiteInteriorSwapLaw_map :
    finiteInteriorSwapLaw.map Fin.val =
      normalBandInteriorSwapLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1040.table.semigroup normalBandBasis := by
  intro e he
  simp only [normalBandBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1040.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteInteriorSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1040.table.checkIdentityNat_sound
      finiteInteriorSwapLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1040.table.semigroup
      normalBandBasis :=
  SemigroupBasis.Generated.S4_110.representative_basis.inheritAlongEmbedding
    embedding targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1040.table.semigroup.opposite
      (reversedBasis normalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1040
-- END S5_1040

-- BEGIN S5_1053
namespace S5_1053

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_110.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_1053.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (0 : Fin 5) else (3 : Fin 5) else if a = 0 then (1 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (4 : Fin 5) else (1 : Fin 5)
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

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteInteriorSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      normalBandIdempotenceLaw := rfl

theorem finiteInteriorSwapLaw_map :
    finiteInteriorSwapLaw.map Fin.val =
      normalBandInteriorSwapLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1053.table.semigroup normalBandBasis := by
  intro e he
  simp only [normalBandBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1053.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteInteriorSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1053.table.checkIdentityNat_sound
      finiteInteriorSwapLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1053.table.semigroup
      normalBandBasis :=
  SemigroupBasis.Generated.S4_110.representative_basis.inheritAlongPowerEmbedding
    powerEmbedding targetModels


end S5_1053
-- END S5_1053

-- BEGIN S5_1067
namespace S5_1067

def embedding :
    Embedding SemigroupBasis.Generated.S4_110.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1067.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteInteriorSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      normalBandIdempotenceLaw := rfl

theorem finiteInteriorSwapLaw_map :
    finiteInteriorSwapLaw.map Fin.val =
      normalBandInteriorSwapLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1067.table.semigroup normalBandBasis := by
  intro e he
  simp only [normalBandBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1067.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteInteriorSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1067.table.checkIdentityNat_sound
      finiteInteriorSwapLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1067.table.semigroup
      normalBandBasis :=
  SemigroupBasis.Generated.S4_110.representative_basis.inheritAlongEmbedding
    embedding targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1067.table.semigroup.opposite
      (reversedBasis normalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1067
-- END S5_1067

-- BEGIN S5_1078
namespace S5_1078

def embedding :
    Embedding SemigroupBasis.Generated.S4_110.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1078.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteInteriorSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      normalBandIdempotenceLaw := rfl

theorem finiteInteriorSwapLaw_map :
    finiteInteriorSwapLaw.map Fin.val =
      normalBandInteriorSwapLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1078.table.semigroup normalBandBasis := by
  intro e he
  simp only [normalBandBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1078.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteInteriorSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1078.table.checkIdentityNat_sound
      finiteInteriorSwapLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1078.table.semigroup
      normalBandBasis :=
  SemigroupBasis.Generated.S4_110.representative_basis.inheritAlongEmbedding
    embedding targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1078.table.semigroup.opposite
      (reversedBasis normalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1078
-- END S5_1078

-- BEGIN S5_1088
namespace S5_1088

def embedding :
    Embedding SemigroupBasis.Generated.S4_110.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1088.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteInteriorSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      normalBandIdempotenceLaw := rfl

theorem finiteInteriorSwapLaw_map :
    finiteInteriorSwapLaw.map Fin.val =
      normalBandInteriorSwapLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1088.table.semigroup normalBandBasis := by
  intro e he
  simp only [normalBandBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1088.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteInteriorSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1088.table.checkIdentityNat_sound
      finiteInteriorSwapLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1088.table.semigroup
      normalBandBasis :=
  SemigroupBasis.Generated.S4_110.representative_basis.inheritAlongEmbedding
    embedding targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1088.table.semigroup.opposite
      (reversedBasis normalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1088
-- END S5_1088

-- BEGIN S5_1097
namespace S5_1097

def embedding :
    Embedding SemigroupBasis.Generated.S4_110.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1097.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteInteriorSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      normalBandIdempotenceLaw := rfl

theorem finiteInteriorSwapLaw_map :
    finiteInteriorSwapLaw.map Fin.val =
      normalBandInteriorSwapLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1097.table.semigroup normalBandBasis := by
  intro e he
  simp only [normalBandBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1097.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteInteriorSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1097.table.checkIdentityNat_sound
      finiteInteriorSwapLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1097.table.semigroup
      normalBandBasis :=
  SemigroupBasis.Generated.S4_110.representative_basis.inheritAlongEmbedding
    embedding targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1097.table.semigroup.opposite
      (reversedBasis normalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1097
-- END S5_1097

-- BEGIN S5_1113
namespace S5_1113

def embedding :
    Embedding SemigroupBasis.Generated.S4_110.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1113.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (1 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteInteriorSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      normalBandIdempotenceLaw := rfl

theorem finiteInteriorSwapLaw_map :
    finiteInteriorSwapLaw.map Fin.val =
      normalBandInteriorSwapLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1113.table.semigroup normalBandBasis := by
  intro e he
  simp only [normalBandBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1113.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteInteriorSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1113.table.checkIdentityNat_sound
      finiteInteriorSwapLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1113.table.semigroup
      normalBandBasis :=
  SemigroupBasis.Generated.S4_110.representative_basis.inheritAlongEmbedding
    embedding targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1113.table.semigroup.opposite
      (reversedBasis normalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1113
-- END S5_1113

-- BEGIN S5_1133
namespace S5_1133

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_110.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_1133.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else (3 : Fin 5) else if a = 0 then (1 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (1 : Fin 5)
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

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteInteriorSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      normalBandIdempotenceLaw := rfl

theorem finiteInteriorSwapLaw_map :
    finiteInteriorSwapLaw.map Fin.val =
      normalBandInteriorSwapLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1133.table.semigroup normalBandBasis := by
  intro e he
  simp only [normalBandBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1133.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteInteriorSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1133.table.checkIdentityNat_sound
      finiteInteriorSwapLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1133.table.semigroup
      normalBandBasis :=
  SemigroupBasis.Generated.S4_110.representative_basis.inheritAlongPowerEmbedding
    powerEmbedding targetModels


end S5_1133
-- END S5_1133

end SemigroupBasis.Generated.NormalBandTransfers

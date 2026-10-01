import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S4_120
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.FirstFinalBandTransfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S5_1034
namespace S5_1034

def embedding :
    Embedding SemigroupBasis.Generated.S4_120.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1034.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferIdempotenceLaw : Identity Nat :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def transferRepeatLaw : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferIdempotenceLaw, transferRepeatLaw]

theorem transferBasis_eq_root :
    transferBasis = firstFinalBandBasis := rfl

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteRepeatLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      transferIdempotenceLaw := rfl

theorem finiteRepeatLaw_map :
    finiteRepeatLaw.map Fin.val =
      transferRepeatLaw := rfl

theorem targetModelsTransfer :
    Models SemigroupBasis.Generated.Catalogue.S5_1034.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1034.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteRepeatLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1034.table.checkIdentityNat_sound
      finiteRepeatLaw (by decide)

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1034.table.semigroup firstFinalBandBasis := by
  simpa only [transferBasis_eq_root] using targetModelsTransfer

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1034.table.semigroup
      firstFinalBandBasis :=
  SemigroupBasis.Generated.S4_120.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1034.table.semigroup.opposite
      (reversedBasis firstFinalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1034
-- END S5_1034

-- BEGIN S5_1065
namespace S5_1065

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_120.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_1065.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (1 : Fin 5) else (4 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (0 : Fin 5)
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

def transferIdempotenceLaw : Identity Nat :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def transferRepeatLaw : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferIdempotenceLaw, transferRepeatLaw]

theorem transferBasis_eq_root :
    transferBasis = firstFinalBandBasis := rfl

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteRepeatLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      transferIdempotenceLaw := rfl

theorem finiteRepeatLaw_map :
    finiteRepeatLaw.map Fin.val =
      transferRepeatLaw := rfl

theorem targetModelsTransfer :
    Models SemigroupBasis.Generated.Catalogue.S5_1065.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1065.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteRepeatLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1065.table.checkIdentityNat_sound
      finiteRepeatLaw (by decide)

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1065.table.semigroup firstFinalBandBasis := by
  simpa only [transferBasis_eq_root] using targetModelsTransfer

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1065.table.semigroup
      firstFinalBandBasis :=
  SemigroupBasis.Generated.S4_120.representative_basis.inheritAlongPowerEmbedding
    powerEmbedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1065.table.semigroup.opposite
      (reversedBasis firstFinalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1065
-- END S5_1065

-- BEGIN S5_1083
namespace S5_1083

def embedding :
    Embedding SemigroupBasis.Generated.S4_120.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1083.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (4 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferIdempotenceLaw : Identity Nat :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def transferRepeatLaw : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferIdempotenceLaw, transferRepeatLaw]

theorem transferBasis_eq_root :
    transferBasis = firstFinalBandBasis := rfl

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteRepeatLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      transferIdempotenceLaw := rfl

theorem finiteRepeatLaw_map :
    finiteRepeatLaw.map Fin.val =
      transferRepeatLaw := rfl

theorem targetModelsTransfer :
    Models SemigroupBasis.Generated.Catalogue.S5_1083.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1083.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteRepeatLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1083.table.checkIdentityNat_sound
      finiteRepeatLaw (by decide)

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1083.table.semigroup firstFinalBandBasis := by
  simpa only [transferBasis_eq_root] using targetModelsTransfer

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1083.table.semigroup
      firstFinalBandBasis :=
  SemigroupBasis.Generated.S4_120.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1083.table.semigroup.opposite
      (reversedBasis firstFinalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1083
-- END S5_1083

-- BEGIN S5_1091
namespace S5_1091

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_120.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_1091.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (4 : Fin 5) else (0 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (3 : Fin 5) else (2 : Fin 5)
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

def transferIdempotenceLaw : Identity Nat :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def transferRepeatLaw : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferIdempotenceLaw, transferRepeatLaw]

theorem transferBasis_eq_root :
    transferBasis = firstFinalBandBasis := rfl

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteRepeatLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      transferIdempotenceLaw := rfl

theorem finiteRepeatLaw_map :
    finiteRepeatLaw.map Fin.val =
      transferRepeatLaw := rfl

theorem targetModelsTransfer :
    Models SemigroupBasis.Generated.Catalogue.S5_1091.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1091.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteRepeatLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1091.table.checkIdentityNat_sound
      finiteRepeatLaw (by decide)

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1091.table.semigroup firstFinalBandBasis := by
  simpa only [transferBasis_eq_root] using targetModelsTransfer

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1091.table.semigroup
      firstFinalBandBasis :=
  SemigroupBasis.Generated.S4_120.representative_basis.inheritAlongPowerEmbedding
    powerEmbedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1091.table.semigroup.opposite
      (reversedBasis firstFinalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1091
-- END S5_1091

-- BEGIN S5_1098
namespace S5_1098

def embedding :
    Embedding SemigroupBasis.Generated.S4_120.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1098.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferIdempotenceLaw : Identity Nat :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def transferRepeatLaw : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferIdempotenceLaw, transferRepeatLaw]

theorem transferBasis_eq_root :
    transferBasis = firstFinalBandBasis := rfl

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteRepeatLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      transferIdempotenceLaw := rfl

theorem finiteRepeatLaw_map :
    finiteRepeatLaw.map Fin.val =
      transferRepeatLaw := rfl

theorem targetModelsTransfer :
    Models SemigroupBasis.Generated.Catalogue.S5_1098.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1098.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteRepeatLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1098.table.checkIdentityNat_sound
      finiteRepeatLaw (by decide)

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1098.table.semigroup firstFinalBandBasis := by
  simpa only [transferBasis_eq_root] using targetModelsTransfer

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1098.table.semigroup
      firstFinalBandBasis :=
  SemigroupBasis.Generated.S4_120.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1098.table.semigroup.opposite
      (reversedBasis firstFinalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1098
-- END S5_1098

-- BEGIN S5_1123
namespace S5_1123

def embedding :
    Embedding SemigroupBasis.Generated.S4_120.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (1 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferIdempotenceLaw : Identity Nat :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def transferRepeatLaw : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferIdempotenceLaw, transferRepeatLaw]

theorem transferBasis_eq_root :
    transferBasis = firstFinalBandBasis := rfl

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteRepeatLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      transferIdempotenceLaw := rfl

theorem finiteRepeatLaw_map :
    finiteRepeatLaw.map Fin.val =
      transferRepeatLaw := rfl

theorem targetModelsTransfer :
    Models SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1123.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteRepeatLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1123.table.checkIdentityNat_sound
      finiteRepeatLaw (by decide)

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup firstFinalBandBasis := by
  simpa only [transferBasis_eq_root] using targetModelsTransfer

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup
      firstFinalBandBasis :=
  SemigroupBasis.Generated.S4_120.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup.opposite
      (reversedBasis firstFinalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1123
-- END S5_1123

-- BEGIN S5_1130
namespace S5_1130

def embedding :
    Embedding SemigroupBasis.Generated.S4_120.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1130.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferIdempotenceLaw : Identity Nat :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def transferRepeatLaw : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferIdempotenceLaw, transferRepeatLaw]

theorem transferBasis_eq_root :
    transferBasis = firstFinalBandBasis := rfl

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteRepeatLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      transferIdempotenceLaw := rfl

theorem finiteRepeatLaw_map :
    finiteRepeatLaw.map Fin.val =
      transferRepeatLaw := rfl

theorem targetModelsTransfer :
    Models SemigroupBasis.Generated.Catalogue.S5_1130.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1130.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteRepeatLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1130.table.checkIdentityNat_sound
      finiteRepeatLaw (by decide)

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1130.table.semigroup firstFinalBandBasis := by
  simpa only [transferBasis_eq_root] using targetModelsTransfer

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1130.table.semigroup
      firstFinalBandBasis :=
  SemigroupBasis.Generated.S4_120.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1130.table.semigroup.opposite
      (reversedBasis firstFinalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1130
-- END S5_1130

-- BEGIN S5_1134
namespace S5_1134

def embedding :
    Embedding SemigroupBasis.Generated.S4_120.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1134.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferIdempotenceLaw : Identity Nat :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def transferRepeatLaw : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferIdempotenceLaw, transferRepeatLaw]

theorem transferBasis_eq_root :
    transferBasis = firstFinalBandBasis := rfl

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteRepeatLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      transferIdempotenceLaw := rfl

theorem finiteRepeatLaw_map :
    finiteRepeatLaw.map Fin.val =
      transferRepeatLaw := rfl

theorem targetModelsTransfer :
    Models SemigroupBasis.Generated.Catalogue.S5_1134.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1134.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteRepeatLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1134.table.checkIdentityNat_sound
      finiteRepeatLaw (by decide)

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1134.table.semigroup firstFinalBandBasis := by
  simpa only [transferBasis_eq_root] using targetModelsTransfer

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1134.table.semigroup
      firstFinalBandBasis :=
  SemigroupBasis.Generated.S4_120.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1134.table.semigroup.opposite
      (reversedBasis firstFinalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1134
-- END S5_1134

-- BEGIN S5_1138
namespace S5_1138

def embedding :
    Embedding SemigroupBasis.Generated.S4_120.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1138.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferIdempotenceLaw : Identity Nat :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def transferRepeatLaw : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferIdempotenceLaw, transferRepeatLaw]

theorem transferBasis_eq_root :
    transferBasis = firstFinalBandBasis := rfl

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteRepeatLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      transferIdempotenceLaw := rfl

theorem finiteRepeatLaw_map :
    finiteRepeatLaw.map Fin.val =
      transferRepeatLaw := rfl

theorem targetModelsTransfer :
    Models SemigroupBasis.Generated.Catalogue.S5_1138.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1138.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteRepeatLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1138.table.checkIdentityNat_sound
      finiteRepeatLaw (by decide)

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1138.table.semigroup firstFinalBandBasis := by
  simpa only [transferBasis_eq_root] using targetModelsTransfer

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1138.table.semigroup
      firstFinalBandBasis :=
  SemigroupBasis.Generated.S4_120.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1138.table.semigroup.opposite
      (reversedBasis firstFinalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1138
-- END S5_1138

-- BEGIN S5_1139
namespace S5_1139

def embedding :
    Embedding SemigroupBasis.Generated.S4_120.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1139.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferIdempotenceLaw : Identity Nat :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def transferRepeatLaw : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferIdempotenceLaw, transferRepeatLaw]

theorem transferBasis_eq_root :
    transferBasis = firstFinalBandBasis := rfl

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteRepeatLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      transferIdempotenceLaw := rfl

theorem finiteRepeatLaw_map :
    finiteRepeatLaw.map Fin.val =
      transferRepeatLaw := rfl

theorem targetModelsTransfer :
    Models SemigroupBasis.Generated.Catalogue.S5_1139.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1139.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteRepeatLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1139.table.checkIdentityNat_sound
      finiteRepeatLaw (by decide)

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1139.table.semigroup firstFinalBandBasis := by
  simpa only [transferBasis_eq_root] using targetModelsTransfer

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1139.table.semigroup
      firstFinalBandBasis :=
  SemigroupBasis.Generated.S4_120.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1139.table.semigroup.opposite
      (reversedBasis firstFinalBandBasis) :=
  representative_basis.oppositeReversed

end S5_1139
-- END S5_1139

end SemigroupBasis.Generated.FirstFinalBandTransfers

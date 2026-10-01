import SemigroupBasis.CoRoots.S4_90Family
import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S4_90
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.Generated.S4_90Transfers

open SemigroupBasis
open SemigroupBasis.CoRoots.S4_90

-- BEGIN S4_93
namespace S4_93

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      basis :=
  SemigroupBasis.CoRoots.S4_90Family.basis_complete

theorem opposite_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S4_93
-- END S4_93

-- BEGIN S5_671
namespace S5_671

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_90.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_671.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (4 : Fin 5) else if a = 1 then (4 : Fin 5) else if a = 2 then (0 : Fin 5) else (2 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else (0 : Fin 5)
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

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixParityCommutationLaw := rfl

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = suffixParityPowerLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_671.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteSuffixCommutationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_671.table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_671.table.checkIdentityNat_sound finitePowerLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_671.table.semigroup basis :=
  SemigroupBasis.Generated.S4_90.representative_basis.inheritAlongPowerEmbedding
    powerEmbedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_671.table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S5_671
-- END S5_671

-- BEGIN S5_958
namespace S5_958

def embedding :
    Embedding SemigroupBasis.Generated.S4_90.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_958.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixParityCommutationLaw := rfl

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = suffixParityPowerLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_958.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteSuffixCommutationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_958.table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_958.table.checkIdentityNat_sound finitePowerLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_958.table.semigroup basis :=
  SemigroupBasis.Generated.S4_90.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_958.table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S5_958
-- END S5_958

-- BEGIN S5_961
namespace S5_961

def embedding :
    Embedding SemigroupBasis.Generated.S4_90.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_961.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixParityCommutationLaw := rfl

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = suffixParityPowerLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_961.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteSuffixCommutationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_961.table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_961.table.checkIdentityNat_sound finitePowerLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_961.table.semigroup basis :=
  SemigroupBasis.Generated.S4_90.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_961.table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S5_961
-- END S5_961

-- BEGIN S5_963
namespace S5_963

def embedding :
    Embedding SemigroupBasis.Generated.S4_90.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_963.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixParityCommutationLaw := rfl

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = suffixParityPowerLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_963.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteSuffixCommutationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_963.table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_963.table.checkIdentityNat_sound finitePowerLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_963.table.semigroup basis :=
  SemigroupBasis.Generated.S4_90.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_963.table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S5_963
-- END S5_963

-- BEGIN S5_965
namespace S5_965

def embedding :
    Embedding SemigroupBasis.Generated.S4_90.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_965.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixParityCommutationLaw := rfl

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = suffixParityPowerLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_965.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteSuffixCommutationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_965.table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_965.table.checkIdentityNat_sound finitePowerLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_965.table.semigroup basis :=
  SemigroupBasis.Generated.S4_90.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_965.table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S5_965
-- END S5_965

-- BEGIN S5_968
namespace S5_968

def embedding :
    Embedding SemigroupBasis.Generated.S4_90.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_968.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixParityCommutationLaw := rfl

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = suffixParityPowerLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_968.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteSuffixCommutationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_968.table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_968.table.checkIdentityNat_sound finitePowerLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_968.table.semigroup basis :=
  SemigroupBasis.Generated.S4_90.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_968.table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S5_968
-- END S5_968

-- BEGIN S5_970
namespace S5_970

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_970.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixParityCommutationLaw := rfl

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = suffixParityPowerLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_970.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteSuffixCommutationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_970.table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_970.table.checkIdentityNat_sound finitePowerLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_970.table.semigroup basis :=
  SemigroupBasis.CoRoots.S4_90Family.basis_complete.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_970.table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S5_970
-- END S5_970

-- BEGIN S5_977
namespace S5_977

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_977.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixParityCommutationLaw := rfl

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = suffixParityPowerLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_977.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteSuffixCommutationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_977.table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_977.table.checkIdentityNat_sound finitePowerLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_977.table.semigroup basis :=
  SemigroupBasis.CoRoots.S4_90Family.basis_complete.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_977.table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S5_977
-- END S5_977

-- BEGIN S5_979
namespace S5_979

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_90.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_979.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (2 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else (0 : Fin 5)
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

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixParityCommutationLaw := rfl

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = suffixParityPowerLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_979.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteSuffixCommutationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_979.table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_979.table.checkIdentityNat_sound finitePowerLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_979.table.semigroup basis :=
  SemigroupBasis.Generated.S4_90.representative_basis.inheritAlongPowerEmbedding
    powerEmbedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_979.table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S5_979
-- END S5_979

-- BEGIN S5_981
namespace S5_981

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_981.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixParityCommutationLaw := rfl

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = suffixParityPowerLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_981.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteSuffixCommutationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_981.table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_981.table.checkIdentityNat_sound finitePowerLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_981.table.semigroup basis :=
  SemigroupBasis.CoRoots.S4_90Family.basis_complete.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_981.table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S5_981
-- END S5_981

-- BEGIN S5_982
namespace S5_982

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_982.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixParityCommutationLaw := rfl

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = suffixParityPowerLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_982.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteSuffixCommutationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_982.table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_982.table.checkIdentityNat_sound finitePowerLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_982.table.semigroup basis :=
  SemigroupBasis.CoRoots.S4_90Family.basis_complete.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_982.table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S5_982
-- END S5_982

-- BEGIN S5_985
namespace S5_985

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_985.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixParityCommutationLaw := rfl

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = suffixParityPowerLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_985.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteSuffixCommutationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_985.table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_985.table.checkIdentityNat_sound finitePowerLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_985.table.semigroup basis :=
  SemigroupBasis.CoRoots.S4_90Family.basis_complete.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_985.table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S5_985
-- END S5_985

-- BEGIN S5_988
namespace S5_988

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_988.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixParityCommutationLaw := rfl

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = suffixParityPowerLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_988.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteSuffixCommutationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_988.table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_988.table.checkIdentityNat_sound finitePowerLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_988.table.semigroup basis :=
  SemigroupBasis.CoRoots.S4_90Family.basis_complete.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_988.table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S5_988
-- END S5_988

end SemigroupBasis.Generated.S4_90Transfers

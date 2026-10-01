import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

namespace SemigroupBasis.Generated.FinalMarkerTransfers

open SemigroupBasis
open SemigroupBasis.Examples

namespace S4_15

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_15.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S4_15.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_15.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_15.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S4_15.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S4_15.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_15.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_15.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S4_15

namespace S4_16

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_16.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S4_16.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_16.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_16.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S4_16.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S4_16.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_16.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_16.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S4_16

namespace S4_17

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_17.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S4_17.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_17.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_17.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S4_17.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S4_17.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_17.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_17.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S4_17

namespace S4_44

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_44.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S4_44.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_44.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_44.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S4_44.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S4_44.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_44.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_44.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S4_44

namespace S4_54

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_54.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S4_54.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_54.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_54.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S4_54.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S4_54.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_54.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_54.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S4_54

namespace S4_58

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_58.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S4_58.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_58.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_58.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S4_58.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S4_58.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_58.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_58.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S4_58

namespace S4_61

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_61.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S4_61.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_61.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_61.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S4_61.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S4_61.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_61.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_61.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S4_61

namespace S4_81

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_81.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S4_81.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_81.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_81.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S4_81.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S4_81.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_81.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_81.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S4_81

namespace S5_68

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_68.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_68.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_68.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_68.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_68.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_68.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_68.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_68.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_68

namespace S5_69

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_69.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_69.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_69.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_69.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_69.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_69.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_69.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_69.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_69

namespace S5_70

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_70.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_70.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_70.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_70.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_70.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_70.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_70.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_70.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_70

namespace S5_71

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_71.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_71.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_71.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_71.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_71.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_71.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_71.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_71.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_71

namespace S5_72

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_72.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_72.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_72.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_72.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_72.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_72.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_72.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_72.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_72

namespace S5_73

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_73.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_73.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_73.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_73.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_73.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_73.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_73.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_73.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_73

namespace S5_231

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_231.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_231.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_231.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_231.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_231.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_231.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_231.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_231.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_231

namespace S5_233

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_233.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_233.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_233.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_233.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_233.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_233.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_233.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_233.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_233

namespace S5_235

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_235.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_235.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_235.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_235.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_235.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_235.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_235.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_235.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_235

namespace S5_257

def targetLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def targetLaw1 : Identity Nat := ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩
def targetLaw2 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0]⟩⟩
def targetLaw3 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

private def swap : Nat → Word Nat
  | 0 => Word.singleton 1
  | 1 => Word.singleton 0
  | n + 2 => Word.singleton (n + 2)

private theorem targetDerivesSourceAxioms :
    ∀ e : Identity Nat, e ∈ finalMarkerThreeOppositeBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [finalMarkerThreeOppositeBasis, reversedBasis,
    finalMarkerThreeBasis, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    exact Derives.fromBasis (e := targetLaw0) (by simp [targetBasis])
  · subst e
    have h : Derives targetBasis targetLaw1.lhs targetLaw1.rhs :=
      Derives.fromBasis (e := targetLaw1) (by simp [targetBasis])
    have hs := Derives.subst h swap
    simpa [targetLaw1, finalMarkerPrefixDuplicationLaw, Identity.reversed,
      swap, Word.bind, Word.reverse, Word.reverseAux, Word.append,
      Word.singleton] using hs
  · subst e
    exact Derives.fromBasis (e := targetLaw2) (by simp [targetBasis])
  · subst e
    exact Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])

private theorem sourceDerivesTargetAxioms :
    ∀ e : Identity Nat, e ∈ targetBasis →
      Derives finalMarkerThreeOppositeBasis e.lhs e.rhs := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    exact Derives.fromBasis (e := finalMarkerPowerLaw.reversed)
      (by simp [finalMarkerThreeOppositeBasis, reversedBasis,
        finalMarkerThreeBasis])
  · subst e
    have h :
        Derives finalMarkerThreeOppositeBasis
          finalMarkerPrefixDuplicationLaw.reversed.lhs
          finalMarkerPrefixDuplicationLaw.reversed.rhs :=
      Derives.fromBasis (e := finalMarkerPrefixDuplicationLaw.reversed)
        (by simp [finalMarkerThreeOppositeBasis, reversedBasis,
          finalMarkerThreeBasis])
    have hs := Derives.subst h swap
    simpa [targetLaw1, finalMarkerPrefixDuplicationLaw, Identity.reversed,
      swap, Word.bind, Word.reverse, Word.reverseAux, Word.append,
      Word.singleton] using hs
  · subst e
    exact Derives.fromBasis (e := finalMarkerCopyLaw.reversed)
      (by simp [finalMarkerThreeOppositeBasis, reversedBasis,
        finalMarkerThreeBasis, finalMarkerCopyLaw, Identity.reversed,
        Word.reverse])
  · subst e
    exact Derives.fromBasis (e := finalMarkerRotateLaw.reversed)
      (by simp [finalMarkerThreeOppositeBasis, reversedBasis,
        finalMarkerThreeBasis, finalMarkerRotateLaw, Identity.reversed,
        Word.reverse])

private theorem sourceModelsTarget :
    Models SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      targetBasis := by
  intro e he
  exact (sourceDerivesTargetAxioms e he).sound
    SemigroupBasis.Generated.S3_6.opposite_basis.1

private theorem sourceBasis :
    BasisFor SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      targetBasis :=
  SemigroupBasis.Generated.S3_6.opposite_basis.replace
    sourceModelsTarget targetDerivesSourceAxioms

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_257.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 5) else if a = 1 then (4 : Fin 5) else (0 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_257.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_257.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_257.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_257.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_257.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_257.table.semigroup targetBasis :=
  sourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_257.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_257

namespace S5_287

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_287.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_287.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_287.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_287.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_287.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_287.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_287.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_287.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_287

namespace S5_288

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_288.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_288.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_288.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_288.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_288.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_288.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_288.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_288.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_288

namespace S5_289

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_289.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_289.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_289.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_289.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_289.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_289.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_289.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_289.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_289

namespace S5_293

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_293.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_293.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_293.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_293.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_293.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_293.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_293.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_293.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_293

namespace S5_294

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_294.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_294.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_294.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_294.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_294.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_294.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_294.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_294.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_294

namespace S5_295

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_295.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_295.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_295.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_295.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_295.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_295.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_295.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_295.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_295

namespace S5_297

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_297.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_297.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_297.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_297.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_297.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_297.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_297.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_297.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_297

namespace S5_299

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_299.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_299.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_299.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_299.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_299.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_299.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_299.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_299.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_299

namespace S5_301

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_301.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_301.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_301.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_301.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_301.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_301.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_301.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_301.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_301

namespace S5_306

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_306.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_306.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_306.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_306.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_306.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_306.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_306.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_306.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_306

namespace S5_308

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_308.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_308.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_308.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_308.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_308.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_308.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_308.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_308.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_308

namespace S5_313

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_313.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_313.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_313.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_313.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_313.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_313.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_313.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_313.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_313

namespace S5_417

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_417.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_417.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_417.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_417.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_417.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_417.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_417.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_417.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_417

namespace S5_418

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_418.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_418.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_418.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_418.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_418.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_418.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_418.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_418.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_418

namespace S5_419

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_419.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_419.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_419.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_419.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_419.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_419.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_419.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_419.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_419

namespace S5_542

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_542.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_542.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_542.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_542.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_542.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_542.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_542.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_542.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_542

namespace S5_543

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_543.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_543.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_543.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_543.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_543.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_543.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_543.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_543.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_543

namespace S5_546

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_546.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_546.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_546.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_546.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_546.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_546.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_546.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_546.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_546

namespace S5_548

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_548.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_548.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_548.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_548.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_548.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_548.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_548.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_548.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_548

namespace S5_549

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_549.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_549.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_549.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_549.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_549.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_549.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_549.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_549.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_549

namespace S5_563

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_563.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_563.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_563.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_563.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_563.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_563.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_563.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_563.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_563

namespace S5_565

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_565.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_565.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_565.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_565.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_565.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_565.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_565.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_565.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_565

namespace S5_566

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_566.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_566.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_566.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_566.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_566.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_566.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_566.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_566.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_566

namespace S5_570

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_570.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_570.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_570.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_570.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_570.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_570.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_570.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_570.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_570

namespace S5_572

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_572.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_572.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_572.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_572.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_572.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_572.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_572.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_572.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_572

namespace S5_648

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_648.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_648.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_648.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_648.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_648.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_648.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_648.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_648.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_648

namespace S5_674

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_674.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_674.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_674.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_674.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_674.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_674.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_674.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_674.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_674

namespace S5_678

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_678.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_678.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_678.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_678.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_678.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_678.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_678.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_678.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_678

namespace S5_681

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_681.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_681.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_681.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_681.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_681.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_681.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_681.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_681.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_681

namespace S5_688

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_688.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_688.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_688.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_688.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_688.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_688.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_688.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_688.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_688

namespace S5_689

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_689.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_689.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_689.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_689.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_689.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_689.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_689.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_689.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_689

namespace S5_691

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_691.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_691.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_691.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_691.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_691.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_691.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_691.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_691.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_691

namespace S5_704

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_704.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_704.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_704.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_704.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_704.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_704.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_704.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_704.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_704

namespace S5_707

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_707.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_707.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_707.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_707.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_707.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_707.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_707.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_707.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_707

namespace S5_712

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_712.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_712.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_712.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_712.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_712.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_712.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_712.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_712.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_712

namespace S5_732

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_732.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_732.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_732.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_732.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_732.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_732.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_732.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_732.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_732

namespace S5_734

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_734.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_734.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_734.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_734.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_734.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_734.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_734.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_734.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_734

namespace S5_881

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_881.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_881.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_881.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_881.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_881.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_881.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_881.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_881.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_881

namespace S5_885

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_885.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_885.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_885.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_885.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_885.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_885.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_885.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_885.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_885

namespace S5_888

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_888.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_888.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_888.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_888.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_888.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_888.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_888.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_888.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_888

namespace S5_911

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_911.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_911.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_911.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_911.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_911.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_911.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_911.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_911.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_911

namespace S5_913

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_913.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_913.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_913.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_913.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_913.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_913.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_913.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_913.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_913

namespace S5_927

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_927.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩


theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw := rfl

theorem targetModels : Models SemigroupBasis.Generated.Catalogue.S5_927.table.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_927.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_927.table.checkIdentityNat_sound
      finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_927.table.checkIdentityNat_sound
      finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_927.table.checkIdentityNat_sound
      finiteLaw3 (by decide)


theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_927.table.semigroup finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_927.table.semigroup.opposite
      (reversedBasis finalMarkerThreeBasis) :=
  representative_basis.oppositeReversed

end S5_927

end SemigroupBasis.Generated.FinalMarkerTransfers

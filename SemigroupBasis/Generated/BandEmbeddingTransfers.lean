import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S3_13
import SemigroupBasis.Generated.S3_16
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

namespace SemigroupBasis.Generated.BandEmbeddingTransfers

open SemigroupBasis
open SemigroupBasis.Examples

namespace S4_99

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_99.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_99.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_99.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_99.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_99.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_99.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S4_99

namespace S4_102

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_102.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_102.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_102.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_102.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_102.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_102.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S4_102

namespace S4_103

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_103.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_103.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_103.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_103.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_103.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_103.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S4_103

namespace S4_104

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_104.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_104.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_104.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_104.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_104.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_104.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S4_104

namespace S4_106

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_106.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_106.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_106.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_106.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_106.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_106.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S4_106

namespace S4_107

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_107.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_107.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_107.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_107.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_107.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_107.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S4_107

namespace S4_108

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_108.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_108.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_108.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_108.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_108.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_108.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S4_108

namespace S4_109

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_109.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_109.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_109.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_109.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_109.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_109.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S4_109

namespace S4_111

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_111.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_111.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_111.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_111.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_111.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_111.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S4_111

namespace S4_113

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_113.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 4) else if a = 1 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_113.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_113.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_113.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_113.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_113.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S4_113

namespace S4_116

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 4) else if a = 1 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_116.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_116.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S4_116

namespace S4_118

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_118.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_118.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_118.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_118.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_118.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_118.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S4_118

namespace S4_119

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_119.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_119.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_119.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_119.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_119.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_119.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S4_119

namespace S4_121

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_121.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_121.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_121.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_121.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_121.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_121.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S4_121

namespace S5_1011

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1011.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1011.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1011.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1011.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1011.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1011.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1011

namespace S5_1014

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1014.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1014.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1014.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1014.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1014.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1014.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1014

namespace S5_1015

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1015.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1015.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1015.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1015.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1015.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1015.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1015

namespace S5_1016

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1016.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1016.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1016.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1016.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1016.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1016.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1016

namespace S5_1018

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1018.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1018.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1018.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1018.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1018.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1018.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1018

namespace S5_1019

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1019.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (4 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1019.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1019.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1019.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1019.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1019.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1019

namespace S5_1020

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1020.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1020.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1020.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1020.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1020.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1020.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1020

namespace S5_1021

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1021.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1021.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1021.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1021.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1021.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1021.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1021

namespace S5_1023

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1023.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1023.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1023.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1023.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1023.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1023.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1023

namespace S5_1025

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1025.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1025.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1025.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1025.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1025.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1025.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1025

namespace S5_1028

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1028.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1028.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1028.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1028.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1028.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1028.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1028

namespace S5_1030

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1030.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1030.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1030.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1030.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1030.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1030.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1030

namespace S5_1031

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1031.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1031.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1031.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1031.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1031.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1031.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1031

namespace S5_1032

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1032.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1032.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1032.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1032.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1032.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1032.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1032

namespace S5_1033

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1033.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1033.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1033.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1033.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1033.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1033.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1033

namespace S5_1035

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1035.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1035.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1035.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1035.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1035.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1035.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1035

namespace S5_1036

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1036.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1036.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1036.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1036.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1036.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1036.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1036

namespace S5_1037

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1037.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1037.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1037.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1037.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1037.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1037.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1037

namespace S5_1038

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1038.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1038.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1038.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1038.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1038.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1038.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1038

namespace S5_1039

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1039.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1039.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1039.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1039.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1039.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1039.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1039

namespace S5_1041

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1041.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1041.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1041.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1041.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1041.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1041.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1041

namespace S5_1042

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1042.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1042.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1042.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1042.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1042.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1042.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1042

namespace S5_1044

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1044.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1044.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1044.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1044.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1044.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1044.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1044

namespace S5_1045

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1045.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (4 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1045.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1045.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1045.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1045.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1045.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1045

namespace S5_1051

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1051.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (4 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1051.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1051.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1051.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1051.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1051.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1051

namespace S5_1052

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1052.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (4 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1052.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1052.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1052.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1052.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1052.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1052

namespace S5_1054

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1054.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1054.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1054.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1054.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1054.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1054.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1054

namespace S5_1055

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1055.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1055.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1055.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1055.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1055.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1055.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1055

namespace S5_1056

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1056.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1056.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1056.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1056.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1056.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1056.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1056

namespace S5_1057

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1057.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1057.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1057.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1057.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1057.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1057.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1057

namespace S5_1058

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1058.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (4 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1058.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1058.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1058.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1058.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1058.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1058

namespace S5_1059

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1059.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1059.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1059.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1059.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1059.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1059.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1059

namespace S5_1060

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1060.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (4 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1060.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1060.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1060.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1060.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1060.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1060

namespace S5_1061

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1061.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (4 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1061.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1061.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1061.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1061.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1061.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1061

namespace S5_1062

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1062.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (4 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1062.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1062.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1062.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1062.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1062.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1062

namespace S5_1063

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1063.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1063.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1063.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1063.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1063.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1063.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1063

namespace S5_1064

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1064.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1064.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1064.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1064.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1064.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1064.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1064

namespace S5_1066

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1066.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1066.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1066.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1066.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1066.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1066.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1066

namespace S5_1068

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1068.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1068.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1068.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1068.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1068.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1068.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1068

namespace S5_1071

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1071.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1071.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1071.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1071.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1071.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1071.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1071

namespace S5_1072

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1072.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (4 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1072.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1072.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1072.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1072.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1072.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1072

namespace S5_1073

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1073.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1073.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1073.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1073.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1073.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1073.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1073

namespace S5_1074

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1074.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1074.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1074.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1074.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1074.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1074.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1074

namespace S5_1075

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1075.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1075.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1075.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1075.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1075.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1075.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1075

namespace S5_1076

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1076.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1076.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1076.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1076.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1076.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1076.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1076

namespace S5_1077

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1077.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (4 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1077.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1077.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1077.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1077.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1077.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1077

namespace S5_1079

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1079.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 5) else if a = 1 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1079.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1079.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1079.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1079.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1079.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1079

namespace S5_1080

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1080.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (3 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1080.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1080.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1080.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1080.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1080.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1080

namespace S5_1081

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1081.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (3 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1081.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1081.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1081.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1081.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1081.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1081

namespace S5_1082

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1082.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (3 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1082.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1082.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1082.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1082.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1082.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1082

namespace S5_1084

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1084.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (3 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1084.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1084.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1084.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1084.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1084.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1084

namespace S5_1085

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1085.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (3 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1085.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1085.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1085.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1085.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1085.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1085

namespace S5_1086

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1086.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1086.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1086.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1086.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1086.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1086.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1086

namespace S5_1087

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1087.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1087.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1087.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1087.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1087.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1087.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1087

namespace S5_1090

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1090.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1090.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1090.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1090.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1090.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1090.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1090

namespace S5_1093

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1093.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1093.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1093.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1093.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1093.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1093.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1093

namespace S5_1094

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1094.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1094.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1094.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1094.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1094.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1094.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1094

namespace S5_1095

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1095.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1095.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1095.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1095.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1095.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1095.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1095

namespace S5_1096

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1096.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1096.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1096.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1096.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1096.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1096.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1096

namespace S5_1100

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1100.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1100.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1100.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1100.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1100.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1100.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1100

namespace S5_1102

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1102.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 5) else if a = 1 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1102.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1102.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1102.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1102.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1102.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1102

namespace S5_1105

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1105.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 5) else if a = 1 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1105.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1105.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1105.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1105.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1105.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1105

namespace S5_1106

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1106.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1106.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1106.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1106.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1106.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1106.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1106

namespace S5_1107

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1107.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1107.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1107.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1107.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1107.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1107.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1107

namespace S5_1109

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1109.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1109.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1109.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1109.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1109.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1109.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1109

namespace S5_1110

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1110.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 5) else if a = 1 then (4 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1110.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1110.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1110.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1110.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1110.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1110

namespace S5_1111

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1111.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1111.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1111.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1111.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1111.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1111.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1111

namespace S5_1112

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1112.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1112.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1112.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1112.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1112.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1112.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1112

namespace S5_1114

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1114.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 5) else if a = 1 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1114.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1114.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1114.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1114.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1114.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1114

namespace S5_1116

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1116.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1116.table.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1116.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1116.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1116.table.semigroup leftNormalBandThreeBasis :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1116.table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1116

namespace S5_1119

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1119.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1119.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1119.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1119.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1119.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1119.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1119

namespace S5_1121

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1121.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 5) else if a = 1 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1121.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1121.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1121.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1121.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1121.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1121

namespace S5_1122

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1122.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 5) else if a = 1 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1122.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1122.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1122.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1122.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1122.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1122

namespace S5_1124

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1124.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1124.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1124.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1124.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1124.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1124.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1124

namespace S5_1126

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1126.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1126.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1126.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1126.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1126.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1126.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1126

namespace S5_1127

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1127.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1127.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1127.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1127.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1127.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1127.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1127

namespace S5_1128

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1128.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1128.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1128.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1128.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1128.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1128.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1128

namespace S5_1129

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1129.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1129.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1129.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1129.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1129.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1129.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1129

namespace S5_1131

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1131.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1131.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1131.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1131.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1131.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1131.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1131

namespace S5_1132

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1132.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1132.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1132.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1132.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1132.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1132.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1132

namespace S5_1136

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1136.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1136.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1136.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1136.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1136.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1136.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1136

namespace S5_1137

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1137.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1137.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1137.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1137.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1137.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1137.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1137

namespace S5_1140

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1140.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1140.table.semigroup leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1140.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1140.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1140.table.semigroup leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1140.table.semigroup.opposite
      (reversedBasis leftRegularBandThreeBasis) :=
  representative_basis.oppositeReversed

end S5_1140

end SemigroupBasis.Generated.BandEmbeddingTransfers

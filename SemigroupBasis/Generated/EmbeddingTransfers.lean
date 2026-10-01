import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Generated.S2_3
import SemigroupBasis.Generated.S3_8
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

namespace SemigroupBasis.Generated.EmbeddingTransfers

open SemigroupBasis
open SemigroupBasis.Examples

namespace S4_7

def embedding :
    Embedding SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_7.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 4) else (1 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨1, []⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = cyclicCommutativityLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = cyclicCancellationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_7.table.semigroup cyclicTwoBasis := by
  intro e he
  simp only [cyclicTwoBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_7.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_7.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_7.table.semigroup cyclicTwoBasis :=
  SemigroupBasis.Generated.S2_2.representative_basis.inheritAlongEmbedding embedding targetModels

end S4_7

namespace S4_19

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_19.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_19.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_19.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_19.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_19.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S4_19

namespace S4_22

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_22.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_22.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_22.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_22.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_22.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S4_22

namespace S4_24

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_24.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_24.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_24.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_24.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_24.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S4_24

namespace S4_47

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_47.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_47.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_47.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_47.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_47.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S4_47

namespace S4_67

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_67.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_67.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_67.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_67.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_67.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S4_67

namespace S4_68

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_68.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_68.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_68.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_68.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_68.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S4_68

namespace S4_78

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_78.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_78.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_78.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_78.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_78.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S4_78

namespace S4_83

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_83.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_83.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_83.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_83.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_83.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S4_83

namespace S4_98

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_98.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 4) else (1 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_98.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_98.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_98.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_98.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S4_98

namespace S4_100

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_100.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 4) else (1 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_100.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_100.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_100.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_100.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S4_100

namespace S4_105

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_105.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 4) else (1 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_105.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_105.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_105.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_105.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S4_105

namespace S4_112

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_112.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 4) else (1 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_112.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_112.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_112.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_112.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S4_112

namespace S4_114

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_114.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 4) else (1 : Fin 4)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_114.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_114.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_114.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_114.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S4_114

namespace S5_75

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_75.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_75.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_75.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_75.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_75.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_75

namespace S5_88

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_88.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_88.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_88.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_88.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_88.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_88

namespace S5_93

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_93.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_93.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_93.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_93.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_93.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_93

namespace S5_99

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_99.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_99.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_99.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_99.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_99.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_99

namespace S5_103

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_103.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_103.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_103.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_103.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_103.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_103

namespace S5_106

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_106.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_106.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_106.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_106.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_106.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_106

namespace S5_111

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_111.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_111.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_111.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_111.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_111.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_111

namespace S5_242

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_242.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_242.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_242.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_242.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_242.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_242

namespace S5_248

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_248.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_248.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_248.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_248.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_248.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_248

namespace S5_252

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_252.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_252.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_252.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_252.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_252.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_252

namespace S5_258

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_258.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 5) else if a = 1 then (4 : Fin 5) else (0 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_258.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_258.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_258.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_258.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_258

namespace S5_319

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_319.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_319.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_319.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_319.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_319.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_319

namespace S5_322

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_322.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_322.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_322.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_322.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_322.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_322

namespace S5_349

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_349.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_349.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_349.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_349.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_349.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_349

namespace S5_358

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_358.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_358.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_358.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_358.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_358.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_358

namespace S5_360

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_360.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_360.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_360.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_360.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_360.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_360

namespace S5_376

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_376.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_376.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_376.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_376.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_376.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_376

namespace S5_377

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_377.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_377.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_377.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_377.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_377.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_377

namespace S5_395

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_395.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_395.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_395.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_395.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_395.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_395

namespace S5_399

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_399.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_399.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_399.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_399.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_399.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_399

namespace S5_404

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_404.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_404.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_404.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_404.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_404.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_404

namespace S5_410

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_410.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_410.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_410.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_410.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_410.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_410

namespace S5_413

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_413.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_413.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_413.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_413.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_413.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_413

namespace S5_421

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_421.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_421.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_421.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_421.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_421.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_421

namespace S5_424

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_424.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_424.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_424.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_424.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_424.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_424

namespace S5_426

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_426.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_426.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_426.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_426.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_426.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_426

namespace S5_550

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_550.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_550.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_550.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_550.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_550.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_550

namespace S5_599

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_599.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_599.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_599.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_599.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_599.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_599

namespace S5_600

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_600.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_600.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_600.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_600.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_600.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_600

namespace S5_601

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_601.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_601.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_601.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_601.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_601.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_601

namespace S5_603

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_603.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_603.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_603.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_603.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_603.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_603

namespace S5_627

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_627.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_627.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_627.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_627.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_627.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_627

namespace S5_629

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_629.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_629.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_629.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_629.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_629.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_629

namespace S5_639

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_639.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_639.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_639.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_639.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_639.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_639

namespace S5_642

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_642.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_642.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_642.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_642.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_642.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_642

namespace S5_643

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_643.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_643.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_643.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_643.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_643.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_643

namespace S5_651

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_651.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_651.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_651.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_651.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_651.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_651

namespace S5_756

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_756.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_756.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_756.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_756.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_756.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_756

namespace S5_757

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_757.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_757.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_757.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_757.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_757.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_757

namespace S5_766

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_766.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_766.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_766.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_766.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_766.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_766

namespace S5_774

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_774.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_774.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_774.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_774.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_774.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_774

namespace S5_776

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_776.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_776.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_776.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_776.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_776.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_776

namespace S5_777

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_777.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_777.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_777.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_777.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_777.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_777

namespace S5_835

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_835.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_835.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_835.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_835.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_835.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_835

namespace S5_837

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_837.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_837.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_837.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_837.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_837.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_837

namespace S5_838

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_838.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_838.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_838.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_838.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_838.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_838

namespace S5_874

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_874.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_874.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_874.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_874.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_874.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_874

namespace S5_876

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_876.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_876.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_876.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_876.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_876.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_876

namespace S5_894

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_894.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_894.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_894.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_894.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_894.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_894

namespace S5_895

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_895.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_895.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_895.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_895.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_895.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_895

namespace S5_905

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_905.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_905.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_905.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_905.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_905.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_905

namespace S5_921

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_921.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_921.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_921.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_921.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_921.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_921

namespace S5_923

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_923.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_923.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_923.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_923.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_923.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_923

namespace S5_934

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_934.table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_934.table.semigroup commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_934.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_934.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_934.table.semigroup commutativeExponentThreeBasis :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_934

namespace S5_1010

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1010.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 5) else (1 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1010.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1010.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1010.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1010.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_1010

namespace S5_1012

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1012.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 5) else (1 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1012.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1012.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1012.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1012.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_1012

namespace S5_1017

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1017.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 5) else (1 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1017.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1017.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1017.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1017.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_1017

namespace S5_1024

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1024.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 5) else (1 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1024.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1024.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1024.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1024.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_1024

namespace S5_1026

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1026.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 5) else (1 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1026.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1026.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1026.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1026.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_1026

namespace S5_1043

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1043.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 5) else (1 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1043.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1043.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1043.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1043.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_1043

namespace S5_1046

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1046.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 5) else (1 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1046.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1046.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1046.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1046.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_1046

namespace S5_1049

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1049.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 5) else (1 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1049.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1049.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1049.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1049.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_1049

namespace S5_1050

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1050.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 5) else (1 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1050.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1050.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1050.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1050.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_1050

namespace S5_1069

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1069.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 5) else (1 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1069.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1069.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1069.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1069.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_1069

namespace S5_1101

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1101.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 5) else (1 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1101.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1101.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1101.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1101.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_1101

namespace S5_1103

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1103.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 5) else (1 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1103.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1103.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1103.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1103.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_1103

namespace S5_1108

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1108.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 5) else (1 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1108.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1108.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1108.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1108.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_1108

namespace S5_1115

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1115.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 5) else (1 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1115.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1115.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1115.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1115.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_1115

namespace S5_1117

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1117.table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 5) else (1 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1117.table.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1117.table.checkIdentityNat_sound
      finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1117.table.checkIdentityNat_sound
      finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1117.table.semigroup semilatticeBasis :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S5_1117

end SemigroupBasis.Generated.EmbeddingTransfers

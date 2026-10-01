import SemigroupBasis.Generated.S2_3
import SemigroupBasis.Generated.S3_10
import SemigroupBasis.Generated.S3_11
import SemigroupBasis.Generated.S3_13
import SemigroupBasis.Generated.S3_15
import SemigroupBasis.Generated.S3_16
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6EmbeddingTransfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S6_14732
namespace S6_14732

/-- Exact one-based order-six catalogue table: `[[1,2,1,4,5,6],[2,1,2,4,5,6],[1,2,3,4,5,6],[4,4,4,4,4,4],[5,5,5,4,5,5],[6,6,6,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "be6b6d568aaa68591e0055854df43eba36441594cdd542a12e43694de9a1b607"

def embedding :
    Embedding SemigroupBasis.Generated.S3_10.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_10.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14732
-- END S6_14732

-- BEGIN S6_14738
namespace S6_14738

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,3,3],[2,1,3,3,3,3],[3,3,3,3,3,3],[3,3,3,4,3,3],[3,3,3,3,5,3],[3,3,3,3,3,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "027bb4e67e5db9f08850643a07d3eb156cd264bfa76b61d0e028fb13f7558a1d"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14738
-- END S6_14738

-- BEGIN S6_14740
namespace S6_14740

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,3,3],[2,1,3,3,3,3],[3,3,3,3,3,3],[3,3,3,4,3,3],[3,3,3,3,5,5],[3,3,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c77cd6473b2c644d55634724104b4f2531b37d3c398ce2ded40b143334646faf"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14740
-- END S6_14740

-- BEGIN S6_14745
namespace S6_14745

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,3,3],[2,1,3,3,3,3],[3,3,3,3,3,3],[3,3,3,4,3,4],[3,3,3,3,5,5],[3,3,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "6b5739de0fc680b7399437e2d8ae83360246daf71a8583443bda657d5bda79f9"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14745
-- END S6_14745

-- BEGIN S6_14752
namespace S6_14752

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,3,3],[2,1,3,3,3,3],[3,3,3,3,3,3],[3,3,3,4,4,4],[3,3,3,4,5,4],[3,3,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "25d380db7ddbbda31036c1e66228b4aeb37de0fcaa8fdaffab2c84623e808a1e"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14752
-- END S6_14752

-- BEGIN S6_14754
namespace S6_14754

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,3,3],[2,1,3,3,3,3],[3,3,3,3,3,3],[3,3,3,4,4,4],[3,3,3,4,5,5],[3,3,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c7e2b9b122371474d4930fc03877e7c32f51cdb51bba9206c54397afeee0177b"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14754
-- END S6_14754

-- BEGIN S6_14772
namespace S6_14772

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,3,6],[2,1,3,3,3,6],[3,3,3,3,3,3],[3,3,3,4,3,3],[3,3,3,3,5,3],[6,6,3,3,3,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "558882557d611c9ef5d9b8c807d553c72f1bc9557d7aef0244fd380b1c0cab9e"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14772
-- END S6_14772

-- BEGIN S6_14776
namespace S6_14776

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,3,6],[2,1,3,3,3,6],[3,3,3,3,3,3],[3,3,3,4,4,3],[3,3,3,4,5,3],[6,6,3,3,3,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "67a62023ead39db87f0758d53019baf4001e446ae7f7064771daafc0e2f6e198"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14776
-- END S6_14776

-- BEGIN S6_14787
namespace S6_14787

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,3,6],[2,1,3,3,3,6],[3,3,3,3,3,6],[3,3,3,4,3,6],[3,3,3,3,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "159f20cd4ca3d986406b917f165f8b579f3fccbdd3ebc2f09629f041b9612fac"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14787
-- END S6_14787

-- BEGIN S6_14789
namespace S6_14789

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,3,6],[2,1,3,3,3,6],[3,3,3,3,3,6],[3,3,3,4,4,6],[3,3,3,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "37a136dfdaa0a15e75df1fb4314958ec767cd4363c4d1eec0d86d2dcacb1c82d"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14789
-- END S6_14789

-- BEGIN S6_14802
namespace S6_14802

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,5,5],[2,1,3,3,5,5],[3,3,3,3,3,3],[3,3,3,4,3,3],[5,5,3,3,5,5],[5,5,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9b673bc14ea138de00abd72cda695e41101b57bfef7a0091d77bb8f35d24fe66"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14802
-- END S6_14802

-- BEGIN S6_14806
namespace S6_14806

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,5,5],[2,1,3,3,5,5],[3,3,3,3,3,3],[3,3,3,4,3,4],[5,5,3,3,5,5],[5,5,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "7bb157f74fc1c4bd32a6dfbbf857ae6c61099d92a48108dd872c8a623c5ca64a"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14806
-- END S6_14806

-- BEGIN S6_14820
namespace S6_14820

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,5,6],[2,1,3,3,5,6],[3,3,3,3,3,3],[3,3,3,4,3,3],[5,5,3,3,5,3],[6,6,3,3,3,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "fce5f855eae7b07d233c4a3be6f07196078c7cd0b67ccbdb21dd2b0d5b49b075"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14820
-- END S6_14820

-- BEGIN S6_14822
namespace S6_14822

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,5,6],[2,1,3,3,5,6],[3,3,3,3,3,3],[3,3,3,4,3,3],[5,5,3,3,5,5],[6,6,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0d3303374783f39c134760c6ea6dc33108840e9a7ebac9a7b9b51761f64b6d84"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14822
-- END S6_14822

-- BEGIN S6_14838
namespace S6_14838

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,5,6],[2,1,3,3,5,6],[3,3,3,3,3,6],[3,3,3,4,3,6],[5,5,3,3,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "151d4c31a0edc9fca48a772ead585906fa8b6630573664b91640ef07a56d42df"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14838
-- END S6_14838

-- BEGIN S6_14842
namespace S6_14842

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,5,6],[2,1,3,3,5,6],[3,3,3,3,5,5],[3,3,3,4,5,5],[5,5,5,5,5,5],[6,6,5,5,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "72cba01c004bb7151473541c53b34a44f888bf0ddfce6c8559e3f7f4ee1d805f"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14842
-- END S6_14842

-- BEGIN S6_14846
namespace S6_14846

/-- Exact one-based order-six catalogue table: `[[1,2,3,3,5,6],[2,1,3,3,5,6],[3,3,3,3,5,6],[3,3,3,4,5,6],[5,5,5,5,5,5],[6,6,6,6,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a0f4af0f2255bb40ee89367c6223be1e1587ced82454f9347386e57db339d1b7"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14846
-- END S6_14846

-- BEGIN S6_14859
namespace S6_14859

/-- Exact one-based order-six catalogue table: `[[1,2,3,4,5,6],[2,1,3,4,5,6],[3,3,3,3,3,3],[4,4,3,4,3,3],[5,5,3,3,5,3],[6,6,3,3,3,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "6cdb799d496fda663c1103c0ffe0ab9389475d2d37d44129c9c2aab2efea3514"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14859
-- END S6_14859

-- BEGIN S6_14861
namespace S6_14861

/-- Exact one-based order-six catalogue table: `[[1,2,3,4,5,6],[2,1,3,4,5,6],[3,3,3,3,3,3],[4,4,3,4,3,3],[5,5,3,3,5,5],[6,6,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8cbca3ddef5c93cdc4a1612d332ef55e5fce9248f4c126bf898af84d1e8f56c5"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14861
-- END S6_14861

-- BEGIN S6_14867
namespace S6_14867

/-- Exact one-based order-six catalogue table: `[[1,2,3,4,5,6],[2,1,3,4,5,6],[3,3,3,3,3,3],[4,4,3,4,3,4],[5,5,3,3,5,5],[6,6,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2b5b3bc1c60a525ef42c7886e02ec610074e4f0339ed6409905efd64e91c2898"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14867
-- END S6_14867

-- BEGIN S6_14874
namespace S6_14874

/-- Exact one-based order-six catalogue table: `[[1,2,3,4,5,6],[2,1,3,4,5,6],[3,3,3,3,3,3],[4,4,3,4,4,4],[5,5,3,4,5,4],[6,6,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "3f30982b87f618ded714a2c913ef54663c4efab63126f469908b315a7bc147c7"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14874
-- END S6_14874

-- BEGIN S6_14876
namespace S6_14876

/-- Exact one-based order-six catalogue table: `[[1,2,3,4,5,6],[2,1,3,4,5,6],[3,3,3,3,3,3],[4,4,3,4,4,4],[5,5,3,4,5,5],[6,6,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0273b5182644b697379cbc1ccc33bf9dac7940bf71df21f5250b3ee62a2dafc9"

def embedding :
    Embedding SemigroupBasis.Generated.S3_11.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = parityPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = parityCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeParityBasis) := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeParityBasis) :=
  SemigroupBasis.Generated.S3_11.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_14876
-- END S6_14876

-- BEGIN S6_15000
namespace S6_15000

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,1,1],[1,1,1,1,5,1],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "eb53f7508f6ca8ae89f6684e14ac69700f9e5fcc5fcb8efed36213614a7d6b5a"

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 6) else (1 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (semilatticeBasis) := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (semilatticeBasis) :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_15000
-- END S6_15000

-- BEGIN S6_15001
namespace S6_15001

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,1,1],[1,1,1,1,5,1],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "82e863ce445c3209cb239004d3f524da09b53576650de0f75e75d2e97334f6b8"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15001
-- END S6_15001

-- BEGIN S6_15002
namespace S6_15002

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,1,1],[1,1,1,1,5,5],[1,1,1,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "1cbc8938a809fa5d4b4b2220b5b6f5e167e90f7df989d9a97a36a34aacd1e645"

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 6) else (1 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (semilatticeBasis) := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (semilatticeBasis) :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_15002
-- END S6_15002

-- BEGIN S6_15003
namespace S6_15003

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,1,1],[1,1,1,1,5,5],[1,1,1,1,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "394f055673167512293706808b945b8c9b459e1b6fa0170b0958fe4302cd1b15"

def embedding :
    Embedding SemigroupBasis.Generated.S3_15.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_15.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15003
-- END S6_15003

-- BEGIN S6_15004
namespace S6_15004

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,1,1],[1,1,1,1,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d0385d637a88b2d46349a8b463c38ad6cc889a038fe03ba9bb31dbb04f2f1294"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models table.semigroup (leftRegularBandThreeBasis) := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftRegularBandThreeBasis) :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftRegularBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15004
-- END S6_15004

-- BEGIN S6_15005
namespace S6_15005

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,1,1],[5,5,5,5,5,5],[5,5,5,5,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5db070663e48e1494018be263038b5e18f3e1b26c7e5f7585d6604cdb623b2c3"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15005
-- END S6_15005

-- BEGIN S6_15006
namespace S6_15006

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,1,1],[5,5,5,5,5,5],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c76120e8946f3f35321e4e52d8207a848df0687371e1353299ff60878926e86d"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15006
-- END S6_15006

-- BEGIN S6_15007
namespace S6_15007

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,1,4],[1,1,1,1,5,5],[1,1,1,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4bf7ef918ff4395e6c51af08239827257c27b564e7bd5c2f2fe179a97de2e276"

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 6) else (1 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (semilatticeBasis) := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (semilatticeBasis) :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_15007
-- END S6_15007

-- BEGIN S6_15008
namespace S6_15008

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,1,4],[5,5,5,5,5,5],[1,1,1,4,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4828d54ded6ac1eeafde809c78ee9a5dc0d2f670e546f8ce683d37a1ed993a84"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15008
-- END S6_15008

-- BEGIN S6_15009
namespace S6_15009

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,1,4],[5,5,5,5,5,5],[1,1,1,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "fc5a7059fefae8d65b07f0f961d2c3ad3f75e0b3f6d3d48e890555e3344a7509"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models table.semigroup (leftRegularBandThreeBasis) := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftRegularBandThreeBasis) :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftRegularBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15009
-- END S6_15009

-- BEGIN S6_15010
namespace S6_15010

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,1,4],[5,5,5,5,5,5],[1,1,1,6,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "df8863fc575204f647ec178dd13cff72137c862979917f9661fb0ab3abcd0b81"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15010
-- END S6_15010

-- BEGIN S6_15011
namespace S6_15011

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,1,4],[5,5,5,5,5,5],[5,5,5,6,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c7ad41e244329ec933e470cde93fe7309d8b1c8d4abd880c56262f5a77dce320"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15011
-- END S6_15011

-- BEGIN S6_15013
namespace S6_15013

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,1,6],[5,5,5,5,5,5],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d2300846cec282c3624f6be16fb8e1b46940b25702937d942004c1bf8cbb5712"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models table.semigroup (leftRegularBandThreeBasis) := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftRegularBandThreeBasis) :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftRegularBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15013
-- END S6_15013

-- BEGIN S6_15014
namespace S6_15014

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,4,4],[1,1,1,4,5,4],[1,1,1,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a72f163d9e5b51f7834440920f7ee89b73b776fa8d7340c1a3f311606fd03d0b"

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 6) else (1 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (semilatticeBasis) := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (semilatticeBasis) :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_15014
-- END S6_15014

-- BEGIN S6_15015
namespace S6_15015

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,4,4],[1,1,1,4,5,4],[1,1,1,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "fbfb1018c21ca66dc755a663515a53c9a422d6025b485f564589b3400b8cf537"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15015
-- END S6_15015

-- BEGIN S6_15016
namespace S6_15016

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,4,4],[1,1,1,4,5,5],[1,1,1,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "6bf7088623f03756c2eeda558f421149a79f7f85f4d5a73b2c7bb2363cff2486"

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 6) else (1 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (semilatticeBasis) := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (semilatticeBasis) :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_15016
-- END S6_15016

-- BEGIN S6_15017
namespace S6_15017

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,4,4],[1,1,1,4,5,5],[1,1,1,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8d42420ea248a942ae500ac57dabfd52e459b72b344770b19cb8059c70e17529"

def embedding :
    Embedding SemigroupBasis.Generated.S3_15.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_15.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15017
-- END S6_15017

-- BEGIN S6_15018
namespace S6_15018

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,4,4],[1,1,1,4,5,6],[1,1,1,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a2cf440a8479a75e8fe9d3cd9c650ea5090dbd5437c0acfa63c1b0ae8b7147f4"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models table.semigroup (leftRegularBandThreeBasis) := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftRegularBandThreeBasis) :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftRegularBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15018
-- END S6_15018

-- BEGIN S6_15019
namespace S6_15019

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,4,4],[1,1,1,5,5,5],[1,1,1,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "be1edd6fb2a129c4d41b02ea5570b3211ecd6f3634f6dad738779a59c51f5b7a"

def embedding :
    Embedding SemigroupBasis.Generated.S3_15.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_15.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15019
-- END S6_15019

-- BEGIN S6_15020
namespace S6_15020

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,4,6],[1,1,1,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cc05f60b584def5baf7eb23579d2ff9f5d283b2c4eeffd63d95f5c60072c2105"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models table.semigroup (leftRegularBandThreeBasis) := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftRegularBandThreeBasis) :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftRegularBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15020
-- END S6_15020

-- BEGIN S6_15021
namespace S6_15021

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,4,6],[1,1,1,5,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d94f1fd947ae56cdf1253db79fd835e7606e1857fefd0980e8a403bfb4af3168"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models table.semigroup (leftRegularBandThreeBasis) := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftRegularBandThreeBasis) :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftRegularBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15021
-- END S6_15021

-- BEGIN S6_15022
namespace S6_15022

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,5,5],[5,5,5,5,5,5],[5,5,5,5,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c0bbabccb600f20d34022f7ac52f2e3a7445213da2808ab1f20c08a840278729"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models table.semigroup (leftRegularBandThreeBasis) := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftRegularBandThreeBasis) :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftRegularBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15022
-- END S6_15022

-- BEGIN S6_15023
namespace S6_15023

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,5,5],[5,5,5,5,5,5],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "3976486a65c28b513d6bff8a07d2784d50748d213be31b52999704f7278cac66"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models table.semigroup (leftRegularBandThreeBasis) := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftRegularBandThreeBasis) :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftRegularBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15023
-- END S6_15023

-- BEGIN S6_15025
namespace S6_15025

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,5,6],[5,5,5,5,5,5],[5,5,5,6,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2807f77b562e475422fde2a7b39e602993835c2b16849261a6a9aa45638a7879"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models table.semigroup (leftRegularBandThreeBasis) := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftRegularBandThreeBasis) :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftRegularBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15025
-- END S6_15025

-- BEGIN S6_15026
namespace S6_15026

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[1,1,1,4,5,6],[5,5,5,5,5,5],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9f825421181b61d7f943e7a890c5426a8673c89a21fc61782efff9ac5506c474"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models table.semigroup (leftRegularBandThreeBasis) := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftRegularBandThreeBasis) :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftRegularBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15026
-- END S6_15026

-- BEGIN S6_15027
namespace S6_15027

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[4,4,4,4,4,4],[4,4,4,4,5,4],[4,4,4,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e1159ba77aeab3c4c532a41e9ba5923f5a870cee4800653b9208854b80cd4189"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15027
-- END S6_15027

-- BEGIN S6_15028
namespace S6_15028

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[4,4,4,4,4,4],[4,4,4,4,5,4],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2012b000daa280cf9c8bba9cbd4a6a18fdc840d18e7fa64b12308fc47bf71096"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15028
-- END S6_15028

-- BEGIN S6_15029
namespace S6_15029

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[4,4,4,4,4,4],[4,4,4,4,5,5],[4,4,4,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "6cf17401f1f488507425cc85df865ea6fa9cc9ffe32c6779fe1058b703cb1d45"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15029
-- END S6_15029

-- BEGIN S6_15030
namespace S6_15030

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[4,4,4,4,4,4],[4,4,4,4,5,5],[4,4,4,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d68f641b20523c1b66f856c99cc5e19fab42a3f4d313d8d9d50e271951541fbb"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15030
-- END S6_15030

-- BEGIN S6_15032
namespace S6_15032

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[4,4,4,4,4,4],[4,4,4,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "eb5e3757d37533d9018fc9a6a0b62742384c37f21e6e64aab8fb91635f0fa0b8"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models table.semigroup (leftRegularBandThreeBasis) := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftRegularBandThreeBasis) :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftRegularBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15032
-- END S6_15032

-- BEGIN S6_15033
namespace S6_15033

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,1],[4,4,4,4,4,4],[5,5,5,5,5,5],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "68ad244efbc92044a32364adf5fd2daa95aa6be63e01a84d455c5a44e62af4ab"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15033
-- END S6_15033

-- BEGIN S6_15034
namespace S6_15034

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,3],[1,1,1,4,1,4],[1,1,1,1,5,5],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "dfebe878f21f049a3eea51a78387360e42fd0fd4d5cd374ab5e483ba4aba6226"

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 6) else (1 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (semilatticeBasis) := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (semilatticeBasis) :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_15034
-- END S6_15034

-- BEGIN S6_15035
namespace S6_15035

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,3],[1,1,1,4,1,4],[5,5,5,5,5,5],[1,1,3,4,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9646766d4fc9f8fc8e7460678a6b32ae679fd6609db648f2bc71750e8d49c906"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15035
-- END S6_15035

-- BEGIN S6_15036
namespace S6_15036

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,3],[1,1,1,4,1,4],[5,5,5,5,5,5],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8ffc4bf811678df50a0bb05c9e33c8f57925194cf8671bee9f44b6a2f7989a53"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models table.semigroup (leftRegularBandThreeBasis) := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftRegularBandThreeBasis) :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftRegularBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15036
-- END S6_15036

-- BEGIN S6_15037
namespace S6_15037

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,3],[1,1,1,4,4,1],[1,1,1,4,5,1],[1,1,3,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4e12abd5dd34a17f5e47a1cdb5fe8eb08d64d2aa372669812a8cdcacfaee0f5f"

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 6) else (1 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (semilatticeBasis) := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (semilatticeBasis) :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_15037
-- END S6_15037

-- BEGIN S6_15038
namespace S6_15038

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,3],[1,1,1,4,4,1],[1,1,1,4,5,1],[1,1,6,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2f99947527281ec6e3681b719634dd0016131d7aa545c73c1310ffb34d213999"

def embedding :
    Embedding SemigroupBasis.Generated.S3_15.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_15.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15038
-- END S6_15038

-- BEGIN S6_15039
namespace S6_15039

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,3],[1,1,1,4,4,1],[1,1,1,5,5,1],[1,1,6,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e59684af9d2007818003f449dcd4a8d4bacd85157cee44df5a58d38c97be3a37"

def embedding :
    Embedding SemigroupBasis.Generated.S3_15.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_15.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15039
-- END S6_15039

-- BEGIN S6_15040
namespace S6_15040

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,3],[1,1,1,4,4,4],[1,1,1,4,5,4],[1,1,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "053624e1b2bc28cf77952048a8c4bffe9eac78cc7a7947f0d2c2a0b54fff7510"

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 6) else (1 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (semilatticeBasis) := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (semilatticeBasis) :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_15040
-- END S6_15040

-- BEGIN S6_15041
namespace S6_15041

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,3],[1,1,1,4,4,4],[1,1,1,4,5,5],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "11df640e8866acaf4e860c3c4af521fd262f9479bad782a407ab5a4fa3804a31"

def embedding :
    Embedding SemigroupBasis.Generated.S2_3.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 2 =>
    if a = 0 then (0 : Fin 6) else (1 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = semilatticeIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = semilatticeCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (semilatticeBasis) := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (semilatticeBasis) :=
  SemigroupBasis.Generated.S2_3.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_15041
-- END S6_15041

-- BEGIN S6_15042
namespace S6_15042

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,3],[1,1,1,4,4,4],[1,1,1,5,5,5],[1,1,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "64e0672cf7182133ef0d441d54e6bf234992d3f182099c1a2a37cd5fa5feaccf"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (5 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = leftNormalBandIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = leftNormalBandSuffixCommutationLaw := rfl

theorem targetModels :
    Models table.semigroup (leftNormalBandThreeBasis) := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftNormalBandThreeBasis) :=
  SemigroupBasis.Generated.S3_13.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftNormalBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15042
-- END S6_15042

-- BEGIN S6_15043
namespace S6_15043

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,3],[1,1,1,4,4,4],[1,1,1,5,5,5],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5346a57552a71dd39bc557a276e323ba006b9aa9f9d6071c9e0462aa5c1b7952"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (5 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models table.semigroup (leftRegularBandThreeBasis) := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftRegularBandThreeBasis) :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftRegularBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15043
-- END S6_15043

-- BEGIN S6_15045
namespace S6_15045

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,1,1,1,1],[1,1,3,1,1,3],[1,1,1,4,5,1],[5,5,5,5,5,5],[1,1,3,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "47101aae19e0a3a7ffa378cea7b83ff0d39f9417973ffa57ed85cc0cc2a4f044"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = lrbIdempotenceLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = lrbRegularLaw := rfl

theorem targetModels :
    Models table.semigroup (leftRegularBandThreeBasis) := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (leftRegularBandThreeBasis) :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (leftRegularBandThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_15045
-- END S6_15045

end SemigroupBasis.Generated.Order6EmbeddingTransfers

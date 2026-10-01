import SemigroupBasis.Generated.S2_3
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

-- BEGIN S6_15733
namespace S6_15733

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,2,3,3],[1,4,4,4,4,4],[1,2,3,4,5,6],[1,2,6,2,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d36e46325a5333b4d8e38558b930e7898374ef38c88873fa58db60d97a5729c5"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (4 : Fin 6) else (3 : Fin 6)
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

end S6_15733
-- END S6_15733

-- BEGIN S6_15734
namespace S6_15734

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,2,3,3],[1,4,4,4,4,4],[1,2,3,4,5,6],[1,4,6,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "70f35a045d5f0b1dc7f5be71eba7fcde5b54f305e39e0fa23f2cd2f6a5d33ba7"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (4 : Fin 6) else (3 : Fin 6)
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

end S6_15734
-- END S6_15734

-- BEGIN S6_15735
namespace S6_15735

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,2,3,3],[1,4,4,4,4,4],[1,2,5,2,5,5],[1,2,6,2,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "f36ca4a46a405da7faa7e67cfd46cb4064f443c0077eff6913f5ca08d79b3aa9"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (3 : Fin 6)
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

end S6_15735
-- END S6_15735

-- BEGIN S6_15736
namespace S6_15736

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,2,3,3],[1,4,4,4,4,4],[1,2,5,2,5,5],[1,4,6,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "366d3c99d6567f6a47d56b042356317d8d2ef2666f45bf62b1c1f64e8fb0f61d"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (3 : Fin 6)
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

end S6_15736
-- END S6_15736

-- BEGIN S6_15739
namespace S6_15739

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,2,3,6],[1,4,4,4,4,4],[1,2,3,2,5,6],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2c649ba5dd8da8c401deaf595ff799e38827dba9168e3f34aefd720ee6a74c63"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
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

end S6_15739
-- END S6_15739

-- BEGIN S6_15742
namespace S6_15742

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,2,3,6],[1,4,4,4,4,4],[1,2,3,4,5,6],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "63738df160cd9f3dfd4b5a1c5d8d0de02ceb68a4f686cbba52cb239b499ae4c2"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
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

end S6_15742
-- END S6_15742

-- BEGIN S6_15743
namespace S6_15743

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,2,3,6],[1,4,4,4,4,4],[1,2,5,2,5,6],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0660ff54a87b772ced05d0037c33632df02b580cb122a1b82d2e09b115d6321f"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
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

end S6_15743
-- END S6_15743

-- BEGIN S6_15744
namespace S6_15744

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,2,3,6],[1,4,4,4,4,4],[1,4,5,4,5,6],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "f2b01559bd6d85a9112f833267529e6276ecdb96c8c873367b399571216e3cda"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
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

end S6_15744
-- END S6_15744

-- BEGIN S6_15745
namespace S6_15745

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,2,5,5],[1,4,4,4,4,4],[1,5,5,5,5,5],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "99ffbc6162060355f1d9c519906b00fb1e5b1a3ecb40bd555aee09006e788b3c"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (4 : Fin 6)
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

end S6_15745
-- END S6_15745

-- BEGIN S6_15749
namespace S6_15749

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,2,5,6],[1,4,4,4,4,4],[1,5,5,5,5,5],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cf399f3c6f8b7c50ce5f755a7c175ed010839bd90433e4a743f2245c012ab81b"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (4 : Fin 6)
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

end S6_15749
-- END S6_15749

-- BEGIN S6_15750
namespace S6_15750

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,3,3],[1,2,3,3,5,3],[1,2,3,3,3,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e9293fd7c48ca5fc43ce11e6f2d2500a200197b14de705ac0bbdff035087a77f"

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

end S6_15750
-- END S6_15750

-- BEGIN S6_15751
namespace S6_15751

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,3,3],[1,2,3,3,5,3],[1,2,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "6dfadb65d3aadd1295eefdabcb16a1e539dd243515a31493f241246d941f2ee3"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (5 : Fin 6)
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

end S6_15751
-- END S6_15751

-- BEGIN S6_15752
namespace S6_15752

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,3,3],[1,2,3,3,5,5],[1,2,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "524e824ca6b2dac62e847b8b03db6b6da7725f518831d903fbc75b26933f7924"

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

end S6_15752
-- END S6_15752

-- BEGIN S6_15753
namespace S6_15753

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,3,3],[1,2,3,3,5,5],[1,2,3,3,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9494a1eeae41819a7f83235449774442dc096fe41f82d278b85e3bd403cbfd1d"

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

end S6_15753
-- END S6_15753

-- BEGIN S6_15754
namespace S6_15754

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,3,3],[1,2,3,3,5,6],[1,2,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "95d3d694aa833b11e59c35715aa3a47c85334db0d04f97100aee7220b16f63fe"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)
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

end S6_15754
-- END S6_15754

-- BEGIN S6_15755
namespace S6_15755

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,3,3],[1,2,5,5,5,5],[1,2,5,5,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5e26744d13fc26d85fc16cb6d0bc855ad8f2b6f8b5d68d7914a43ab2764ea141"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)
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

end S6_15755
-- END S6_15755

-- BEGIN S6_15756
namespace S6_15756

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,3,3],[1,2,5,5,5,5],[1,2,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c0dddfff06e5e66bbe0e6be5df61477b9bd022dab4ad1835355ecd0c78e85242"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)
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

end S6_15756
-- END S6_15756

-- BEGIN S6_15757
namespace S6_15757

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,3,4],[1,2,3,3,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0fd4702fcca1dab801a5e0272755d9bb042d27b5304423bb0e02cd7cb9b5fde0"

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

end S6_15757
-- END S6_15757

-- BEGIN S6_15758
namespace S6_15758

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,3,4],[1,2,5,5,5,5],[1,2,3,4,3,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "126c0ba589e4421d49c8eb833aec4eccf5e6bcd33f94060d73db60211b5776df"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)
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

end S6_15758
-- END S6_15758

-- BEGIN S6_15759
namespace S6_15759

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,3,4],[1,2,5,5,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e9331185b04f95514af6473a3fe4c5540535d019bd2234c63442e8f73203393b"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 6) else if a = 1 then (5 : Fin 6) else (4 : Fin 6)
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

end S6_15759
-- END S6_15759

-- BEGIN S6_15760
namespace S6_15760

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,3,4],[1,2,5,5,5,5],[1,2,3,6,3,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "87a6570eb948b263bf626bfdb24fd065db9477babebe1b92f023ce18f5ed46cc"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)
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

end S6_15760
-- END S6_15760

-- BEGIN S6_15761
namespace S6_15761

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,3,4],[1,2,5,5,5,5],[1,2,5,6,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "13fc14191809c7c20305fb47366926f682cbb7dfb10160cf078eb5f0f00b2499"

def embedding :
    Embedding SemigroupBasis.Generated.S3_13.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)
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

end S6_15761
-- END S6_15761

-- BEGIN S6_15763
namespace S6_15763

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,3,6],[1,2,5,5,5,5],[1,2,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "16cbc4a085b9f5557df368ea6d2022514b7e8240c6f880aaae00c08834c660f0"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (5 : Fin 6)
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

end S6_15763
-- END S6_15763

-- BEGIN S6_15764
namespace S6_15764

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,4,4],[1,2,3,4,5,4],[1,2,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "39abd44c8f4ef92c7531ae8ec1034e59615b9bed2d680674101aa84fd8fd05a1"

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

end S6_15764
-- END S6_15764

-- BEGIN S6_15765
namespace S6_15765

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,4,4],[1,2,3,4,5,4],[1,2,3,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "efc619e6c078694e51951f972de64d51b51c8d53a5f6a247c99d639e78e96df3"

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

end S6_15765
-- END S6_15765

-- BEGIN S6_15766
namespace S6_15766

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,4,4],[1,2,3,4,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "f34e93bd154f7423b81ec329086af20acfeb5ffaa6bc1bba11ed447d2f368a18"

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

end S6_15766
-- END S6_15766

-- BEGIN S6_15767
namespace S6_15767

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,4,4],[1,2,3,4,5,5],[1,2,3,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "74ec57c4830ec2541af8a40a544378163a8cf6a372392cbfa19db997ff16c064"

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

end S6_15767
-- END S6_15767

-- BEGIN S6_15768
namespace S6_15768

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,4,4],[1,2,3,4,5,6],[1,2,3,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d1ea818e5d56bb449d0f810e5c98a85d874dc1067cc7573f64dee14e0cd9f108"

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

end S6_15768
-- END S6_15768

-- BEGIN S6_15769
namespace S6_15769

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,4,4],[1,2,3,5,5,5],[1,2,3,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5a730f9df1f169d115703ff419159777a0e43353b293f41eb219ad5fb7670bf1"

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

end S6_15769
-- END S6_15769

-- BEGIN S6_15770
namespace S6_15770

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,4,6],[1,2,3,4,5,6],[1,2,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "7ea5899ab71ed0890fd1e6641019ac1acc023058b2c757a84230a6fff405b00e"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (5 : Fin 6)
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

end S6_15770
-- END S6_15770

-- BEGIN S6_15771
namespace S6_15771

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,4,6],[1,2,3,5,5,6],[1,2,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "db62af9463dcf4c7ec7947d9e19b79e76484b0264eb5a0118d3e9c45751a16d5"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (5 : Fin 6)
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

end S6_15771
-- END S6_15771

-- BEGIN S6_15773
namespace S6_15773

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,3,4,5,6],[1,2,5,5,5,5],[1,2,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "dbd6d82bb7dadf01d23f077b4237bd577a14ba769cdc71e506f818623d7b5ccd"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)
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

end S6_15773
-- END S6_15773

-- BEGIN S6_15774
namespace S6_15774

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,3],[1,2,4,4,4,4],[1,2,5,5,5,5],[1,2,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "27afd923e5800104435761330a28b45cd6f4c9bded3222fd528243cdafdb7db9"

def embedding :
    Embedding SemigroupBasis.Generated.S3_15.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (3 : Fin 6)
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

end S6_15774
-- END S6_15774

-- BEGIN S6_15775
namespace S6_15775

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,6],[1,2,3,4,3,6],[1,2,3,3,5,6],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "7c612fff9134752aaad4dced47617f1094eaec79f2f5de09fa8998bb755d4fe4"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
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

end S6_15775
-- END S6_15775

-- BEGIN S6_15776
namespace S6_15776

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,6],[1,2,3,4,3,6],[1,2,5,5,5,6],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a4be52c477f361b73c430dcb8b449851fd1e8f55f7d633755565d7b751242bd2"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
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

end S6_15776
-- END S6_15776

-- BEGIN S6_15777
namespace S6_15777

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,6],[1,2,3,4,4,6],[1,2,3,4,5,6],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "43ce4da57ac61885db5b7aff31c961d338eab7c8e4a5d0f4b274242f0530e1f1"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
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

end S6_15777
-- END S6_15777

-- BEGIN S6_15778
namespace S6_15778

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,6],[1,2,3,4,4,6],[1,2,3,5,5,6],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "13926f00bc42bf61a98b9ab3d3d06a43b238a98b68284b051e0e841a83732044"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
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

end S6_15778
-- END S6_15778

-- BEGIN S6_15780
namespace S6_15780

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,6],[1,2,3,4,5,6],[1,2,5,5,5,6],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4dd746b1bda73b7ef87c055a21b3618634ce6107f459204818260da9badab851"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
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

end S6_15780
-- END S6_15780

-- BEGIN S6_15781
namespace S6_15781

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,3,6],[1,2,4,4,4,6],[1,2,5,5,5,6],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8340366f847e5ef86910f179f0e299b8a4dabfc30296a3eefa23c98ed66ec3be"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
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

end S6_15781
-- END S6_15781

-- BEGIN S6_15785
namespace S6_15785

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,5,6],[1,2,3,4,5,6],[1,5,5,5,5,5],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "3c6426540d507bb61153327b732634867409f23fffbfcd557902aa4a72ae44f7"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (4 : Fin 6)
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

end S6_15785
-- END S6_15785

-- BEGIN S6_15786
namespace S6_15786

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,3,5,6],[1,2,4,4,5,6],[1,5,5,5,5,5],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9dac6841ead3d41a5f7e4a374cbb52ec2d69662a7f58a286c832ab034e45ac99"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (4 : Fin 6)
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

end S6_15786
-- END S6_15786

-- BEGIN S6_15789
namespace S6_15789

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,2,3,4,5,6],[1,4,4,4,4,4],[1,5,5,5,5,5],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "eea0b820cdc364942f940ad1ca359f802b32ec5182fddc8eb876e8cf6f9271ec"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (1 : Fin 6) else if a = 1 then (2 : Fin 6) else (3 : Fin 6)
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

end S6_15789
-- END S6_15789

-- BEGIN S6_15790
namespace S6_15790

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,2],[1,3,3,3,3,3],[1,4,4,4,4,4],[1,5,5,5,5,5],[1,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "fa8a70ba6675a7a7094c47f815ac5247c71b57b56f3fdd3aeb48cf2f8f199918"

def embedding :
    Embedding SemigroupBasis.Generated.S3_15.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
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

end S6_15790
-- END S6_15790

-- BEGIN S6_15791
namespace S6_15791

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,2,2,6],[1,2,2,4,2,6],[1,2,2,2,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b1ea0eb22050919eda571270e87f6ef2e8f49e5e6e462690564946eb7202e68e"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15791
-- END S6_15791

-- BEGIN S6_15792
namespace S6_15792

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,2,2,6],[1,2,2,4,2,6],[1,5,5,5,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "06a1eeaf6aca396fa4032e5ea23fc96c4eeae255f2ef81d04d2ddbb1f05a96a5"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15792
-- END S6_15792

-- BEGIN S6_15793
namespace S6_15793

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,2,2,6],[1,2,2,4,4,6],[1,2,2,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "37983d0f35837a7a2463744c9112ea37e253d86dc314e88c95146e498fe962e0"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15793
-- END S6_15793

-- BEGIN S6_15794
namespace S6_15794

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,2,2,6],[1,2,2,4,4,6],[1,2,2,5,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "f929c90ce05f8f782296ff9becf1e9691532d05f4b9965d0c462fdfad026e5aa"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15794
-- END S6_15794

-- BEGIN S6_15796
namespace S6_15796

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,2,2,6],[1,2,2,4,5,6],[1,5,5,5,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9ccd293a5ab1f5bd56dbcb83599ce03f244c374f1b8f96ffbab569cf9dcc6503"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15796
-- END S6_15796

-- BEGIN S6_15797
namespace S6_15797

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,2,2,6],[1,4,4,4,4,6],[1,4,4,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8f58af4e3b651ef99352655a5ed33caf592bd429adb9b28f93426876be80ccb6"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15797
-- END S6_15797

-- BEGIN S6_15798
namespace S6_15798

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,2,2,6],[1,4,4,4,4,6],[1,5,5,5,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "1a7c05642d73b26bce4f60afd73db3cc2b1e18d504db228f6a33db93ebf7e858"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15798
-- END S6_15798

-- BEGIN S6_15799
namespace S6_15799

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,2,3,6],[1,2,2,4,4,6],[1,2,3,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e526bb75746104be057ffe0bd184f5c3a2469aac25664c2d3757d25566b0f02e"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15799
-- END S6_15799

-- BEGIN S6_15800
namespace S6_15800

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,2,3,6],[1,4,4,4,4,6],[1,2,3,2,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e2661118424c248e9e9ef5af4b800b6185eaf1fa8628d6bdf9d973abc82f4a56"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15800
-- END S6_15800

-- BEGIN S6_15801
namespace S6_15801

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,2,3,6],[1,4,4,4,4,6],[1,2,3,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ea34782283621c72e3438f241d89c152d4f422f084515453874517f61d920d0a"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15801
-- END S6_15801

-- BEGIN S6_15802
namespace S6_15802

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,2,3,6],[1,4,4,4,4,6],[1,2,5,2,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "53b52cc73e7021e497dfbb4bd7fccd976abf8987c1b077b7a4e6a73923e97d77"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15802
-- END S6_15802

-- BEGIN S6_15803
namespace S6_15803

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,2,3,6],[1,4,4,4,4,6],[1,4,5,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "12201a255927ab7adc985d51f695aaae6f2f4fa3085779a73fbb4b5e395aa8be"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15803
-- END S6_15803

-- BEGIN S6_15805
namespace S6_15805

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,2,5,6],[1,4,4,4,4,6],[1,5,5,5,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "04847f9ea3ae850b45b09abca3ed44ff1d276edc53cb67439ee86aa3b4bcc878"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15805
-- END S6_15805

-- BEGIN S6_15806
namespace S6_15806

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,3,3,6],[1,2,3,4,3,6],[1,2,3,3,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5b55e3680e88038f50b2a436ea4c15f509dfb6c84e5caf58218d7c637979a680"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15806
-- END S6_15806

-- BEGIN S6_15807
namespace S6_15807

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,3,3,6],[1,2,3,4,3,6],[1,2,5,5,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "aa16ae3acd62d3818d1859f732c63620f1b03004310d4be60daa7b56e5454e31"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15807
-- END S6_15807

-- BEGIN S6_15808
namespace S6_15808

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,3,3,6],[1,2,3,4,4,6],[1,2,3,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "3d2516c6f26da90941ff4493897bfbf36ca0dff823aac360df55aa8fe50ab894"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15808
-- END S6_15808

-- BEGIN S6_15809
namespace S6_15809

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,3,3,6],[1,2,3,4,4,6],[1,2,3,5,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "fcd4e0b88edd2d4f3ee05212ab714258cece527aea7dcdf296d6fb9491058191"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15809
-- END S6_15809

-- BEGIN S6_15811
namespace S6_15811

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,3,3,6],[1,2,3,4,5,6],[1,2,5,5,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5a5bc2cac4173171618e83e37a117d8021e4da886f6c01b50c8d457d055039e8"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15811
-- END S6_15811

-- BEGIN S6_15812
namespace S6_15812

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,3,3,6],[1,2,4,4,4,6],[1,2,5,5,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "bffcaa7ce69e69a97bd1cdb1d7d69a7b4c829311111021da176ae04a39a7b00a"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15812
-- END S6_15812

-- BEGIN S6_15815
namespace S6_15815

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,3,5,6],[1,2,3,4,5,6],[1,5,5,5,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "3e0cb1ebb1a29ffb2d6e4e647c744918814dc35a5837441e1715b720ae6e78fc"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15815
-- END S6_15815

-- BEGIN S6_15816
namespace S6_15816

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,2,2,2,2,6],[1,2,3,3,5,6],[1,2,4,4,5,6],[1,5,5,5,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a314f40c37b18d7cf3e4980fd6751288c7841db0dd61d6fa5805a567b6608b46"

def embedding :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
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

end S6_15816
-- END S6_15816

end SemigroupBasis.Generated.Order6EmbeddingTransfers

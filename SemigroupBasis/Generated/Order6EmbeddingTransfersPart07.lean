import SemigroupBasis.Generated.S3_5
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.Generated.S3_8
import SemigroupBasis.Generated.S3_9
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6EmbeddingTransfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S6_6632
namespace S6_6632

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,6],[1,1,1,2,2,6],[1,1,1,2,2,6],[1,2,2,4,4,6],[1,2,2,4,4,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4a0365ead250100e93d45842c752dec1b2b535ec937bba7d92f628604baa8f8f"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6632
-- END S6_6632

-- BEGIN S6_6636
namespace S6_6636

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,6],[1,1,1,2,2,6],[1,1,1,3,3,6],[1,2,3,4,4,6],[1,2,3,4,4,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "996fda6c01944a5a4aaa87a5a5137d10958a47ff3f08b0139dc7e2b18eede475"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6636
-- END S6_6636

-- BEGIN S6_6640
namespace S6_6640

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,1],[1,1,1,4,4,1],[4,4,4,4,4,4],[4,4,4,4,4,4],[1,1,1,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ba5c4ac2f124c972d0ef46d8ee6a20ebe145c8309872c941c5655359c7e7a512"

def embedding :
    Embedding SemigroupBasis.Generated.S3_5.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = saturatedPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = saturatedCommutativityLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = saturatedPrefixDuplicationLaw := rfl

theorem targetModels :
    Models table.semigroup (saturatedSupportBasis) := by
  intro e he
  simp only [saturatedSupportBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (saturatedSupportBasis) :=
  SemigroupBasis.Generated.S3_5.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6640
-- END S6_6640

-- BEGIN S6_6641
namespace S6_6641

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,1],[1,1,1,4,4,1],[4,4,4,4,4,4],[4,4,4,4,4,4],[1,1,1,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "79fe9807848559edfda9eb61ad4fc44e7bd9daf859b39d1a49fcf8f03f27443a"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6641
-- END S6_6641

-- BEGIN S6_6642
namespace S6_6642

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,1],[1,1,1,4,4,1],[4,4,4,4,4,4],[4,4,4,4,4,4],[1,1,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "01caa4c0b2a6391953f768d7058de39ff1bd9b4f4b434c8f780c267f9e0c041d"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6642
-- END S6_6642

-- BEGIN S6_6643
namespace S6_6643

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,1],[1,1,1,4,4,1],[4,4,4,4,4,4],[4,4,4,4,4,4],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ed28033a2bbbd9860628792f3ef9a27efafeced16a95c59e3fd53fb1bd923f76"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6643
-- END S6_6643

-- BEGIN S6_6644
namespace S6_6644

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,1],[1,1,1,4,4,1],[4,4,4,4,4,4],[4,4,4,4,4,4],[1,2,2,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "01390a5dc449b7384a43f39160d3e6562cdcc2bad91fd7a941c1036866e589c1"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6644
-- END S6_6644

-- BEGIN S6_6645
namespace S6_6645

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,1],[1,1,1,4,4,1],[4,4,4,4,4,4],[4,4,4,4,4,4],[1,2,2,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "117ad58e482e1a94514f94a870f9ca82f8b2c06ba0b46aa8ff515c68195e56f1"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6645
-- END S6_6645

-- BEGIN S6_6646
namespace S6_6646

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,1],[1,1,1,4,4,1],[4,4,4,4,4,4],[4,4,4,4,4,4],[1,2,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "24abde9aa020cd7d2fcb529c1a22d84bf56a05867500c52ddeb270c252678820"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6646
-- END S6_6646

-- BEGIN S6_6647
namespace S6_6647

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,1],[1,1,1,4,4,1],[4,4,4,4,4,4],[4,4,4,4,4,4],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "1ffdc36ce6f0d4fe6126087c01f0d2c36802fcef7dbd5916d080912b712c2b79"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6647
-- END S6_6647

-- BEGIN S6_6649
namespace S6_6649

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,1],[1,1,1,4,4,1],[4,4,4,4,4,4],[4,4,4,4,4,5],[1,1,1,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8f9932e23c8d7271f1db920a968ad9ebc6dcda8d33625acc6d41e27617df1c81"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6649
-- END S6_6649

-- BEGIN S6_6656
namespace S6_6656

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,1],[1,1,1,4,4,1],[4,4,4,4,4,4],[5,5,5,4,4,5],[1,1,1,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a55163b893fa9446a70c583b556851795a90993cdd68acf5f5966bec41d9b06a"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨1, [0]⟩, ⟨1, [0, 0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0]⟩⟩
def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw.reversed := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw.reversed := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw.reversed := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis finalMarkerThreeBasis) := by
  intro e he
  simp only [reversedBasis, finalMarkerThreeBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.opposite_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6656
-- END S6_6656

-- BEGIN S6_6665
namespace S6_6665

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,1],[1,1,1,4,4,3],[4,4,4,4,4,4],[4,4,4,4,4,4],[1,1,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "7f48fd560df9690ac6cef3eaa1c37d04f5ab3a38131ef58cc0271b574324da67"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6665
-- END S6_6665

-- BEGIN S6_6671
namespace S6_6671

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,1],[1,1,1,4,4,3],[4,4,4,4,4,4],[4,4,4,4,4,5],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4d05fc2b5ebd287ef51e06af4474d64a8ec475d9b0eb2ef37800e92c525e1b92"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6671
-- END S6_6671

-- BEGIN S6_6675
namespace S6_6675

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,1],[1,1,1,4,4,3],[4,4,4,4,4,4],[5,5,5,4,4,5],[1,1,1,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "83b7d84e6c0c20707ab8d3a650c9e69deca66cd8a38fb3d1b15736ca86547adb"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨1, [0]⟩, ⟨1, [0, 0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0]⟩⟩
def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw.reversed := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw.reversed := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw.reversed := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis finalMarkerThreeBasis) := by
  intro e he
  simp only [reversedBasis, finalMarkerThreeBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.opposite_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6675
-- END S6_6675

-- BEGIN S6_6683
namespace S6_6683

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,2],[1,1,1,4,4,2],[4,4,4,4,4,4],[4,4,4,4,4,4],[1,2,2,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e43033da3a1c95ee83e327f6b8ce382f78ee1877b011d03ff30069d440021a05"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6683
-- END S6_6683

-- BEGIN S6_6687
namespace S6_6687

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,2],[1,1,1,4,4,2],[4,4,4,4,4,4],[4,4,4,4,4,5],[1,2,2,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "7087a9c1b1b0c6e636655fa5920efad3756aef8d170d90326f24357aa1f74c00"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6687
-- END S6_6687

-- BEGIN S6_6690
namespace S6_6690

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,2],[1,1,1,4,4,2],[4,4,4,4,4,4],[5,5,5,4,4,5],[1,1,1,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "341a8776fe12d3ac2ccbef9f925184af2823b218fa117d3783eaef7eae06c7b5"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨1, [0]⟩, ⟨1, [0, 0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0]⟩⟩
def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw.reversed := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw.reversed := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw.reversed := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis finalMarkerThreeBasis) := by
  intro e he
  simp only [reversedBasis, finalMarkerThreeBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.opposite_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6690
-- END S6_6690

-- BEGIN S6_6696
namespace S6_6696

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,2],[1,1,1,4,4,3],[4,4,4,4,4,4],[4,4,4,4,4,4],[1,2,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "70f19322acea8711a847fb709c81656cbd1a104c18297bd27057504a0bab49ec"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6696
-- END S6_6696

-- BEGIN S6_6698
namespace S6_6698

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,2],[1,1,1,4,4,3],[4,4,4,4,4,4],[4,4,4,4,4,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "bf6e15c178c60b3d4dc5a6749fac9ec66f5011962dad25ed1233cc3c6505fe24"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6698
-- END S6_6698

-- BEGIN S6_6699
namespace S6_6699

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,2],[1,1,1,4,4,3],[4,4,4,4,4,4],[5,5,5,4,4,5],[1,1,1,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "1ebc59378011feafec29a2bf8e477dfd31bf4235b67295b30c82a0a8acb91164"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨1, [0]⟩, ⟨1, [0, 0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0]⟩⟩
def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw.reversed := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw.reversed := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw.reversed := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis finalMarkerThreeBasis) := by
  intro e he
  simp only [reversedBasis, finalMarkerThreeBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.opposite_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6699
-- END S6_6699

-- BEGIN S6_6707
namespace S6_6707

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,4],[1,1,1,4,4,4],[1,1,1,4,4,4],[4,4,4,4,4,4],[4,4,4,4,4,4],[4,4,4,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4c5c32ec6b6cba2be6e3e82d23a219f147bf865b21838f9cf76dbf6dbd7fba28"

def embedding :
    Embedding SemigroupBasis.Generated.S3_5.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = saturatedPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = saturatedCommutativityLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = saturatedPrefixDuplicationLaw := rfl

theorem targetModels :
    Models table.semigroup (saturatedSupportBasis) := by
  intro e he
  simp only [saturatedSupportBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (saturatedSupportBasis) :=
  SemigroupBasis.Generated.S3_5.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6707
-- END S6_6707

-- BEGIN S6_6708
namespace S6_6708

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,4],[1,1,1,4,4,4],[1,1,1,4,4,4],[4,4,4,4,4,4],[4,4,4,4,4,4],[4,4,4,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "eae14bd206798e5cdf39ff1b4e860cb0b45d04f4e133d62f0be3c996b49360b8"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6708
-- END S6_6708

-- BEGIN S6_6709
namespace S6_6709

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,4],[1,1,1,4,4,4],[1,1,1,4,4,4],[4,4,4,4,4,4],[4,4,4,4,4,4],[4,4,5,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "bd1e30997bd29e5e3ff719d112fbfbaac1de852eb49d408e7e1fd740070c026f"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6709
-- END S6_6709

-- BEGIN S6_6710
namespace S6_6710

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,4],[1,1,1,4,4,4],[1,1,1,4,4,4],[4,4,4,4,4,4],[4,4,4,4,4,4],[4,5,5,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cd69203dddbdc481a833fc56338a2bfb5020c8efa019241c40bb35658a6ddc9e"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6710
-- END S6_6710

-- BEGIN S6_6712
namespace S6_6712

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,4],[1,1,1,4,4,4],[1,1,1,4,4,4],[4,4,4,4,4,4],[4,4,4,4,4,5],[4,4,4,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "88295c2d0705a8730867e47b19b6719e68a83ab4286b14234055581b0d903814"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6712
-- END S6_6712

-- BEGIN S6_6713
namespace S6_6713

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,4],[1,1,1,4,4,4],[1,1,1,4,4,4],[4,4,4,4,4,4],[5,5,5,4,4,4],[4,4,4,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9bc01faef627ebba811d882e3c998d870f1380b1d5ec970efd98eec61aaaedb5"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨1, [0]⟩, ⟨1, [0, 0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0]⟩⟩
def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw.reversed := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw.reversed := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw.reversed := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis finalMarkerThreeBasis) := by
  intro e he
  simp only [reversedBasis, finalMarkerThreeBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.opposite_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6713
-- END S6_6713

-- BEGIN S6_6717
namespace S6_6717

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,4],[1,1,1,4,4,4],[1,1,1,4,4,5],[4,4,4,4,4,4],[4,4,4,4,4,5],[4,4,5,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "17127bd369a5965d9ca06f43d56af363f6603db1103bf98f47f37485d098c872"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6717
-- END S6_6717

-- BEGIN S6_6718
namespace S6_6718

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,4],[1,1,1,4,4,5],[1,1,1,4,4,5],[4,4,4,4,4,4],[4,4,4,4,4,5],[4,5,5,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2c3f5ce7759c78d89c72802d8e0fed7ab47cbc83d6849bc603bdca8518b58628"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6718
-- END S6_6718

-- BEGIN S6_6719
namespace S6_6719

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,6],[1,1,1,4,4,6],[1,1,1,4,4,6],[4,4,4,4,4,4],[4,4,4,4,4,4],[6,6,6,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4bc63105f334d517a11eaade2c2984b97b3e0ee6c45e5857907faa65845ea3ce"

def embedding :
    Embedding SemigroupBasis.Generated.S3_5.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = saturatedPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = saturatedCommutativityLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = saturatedPrefixDuplicationLaw := rfl

theorem targetModels :
    Models table.semigroup (saturatedSupportBasis) := by
  intro e he
  simp only [saturatedSupportBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (saturatedSupportBasis) :=
  SemigroupBasis.Generated.S3_5.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6719
-- END S6_6719

-- BEGIN S6_6721
namespace S6_6721

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,6],[1,1,1,4,4,6],[1,1,1,4,4,6],[4,4,4,4,4,4],[5,5,5,4,4,4],[6,6,6,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ec0aa763a2f682f1d3ed59272ebe43db5ecfb1ea197df2a8b06847dfaa5035d6"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨1, [0]⟩, ⟨1, [0, 0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0]⟩⟩
def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw.reversed := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw.reversed := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw.reversed := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis finalMarkerThreeBasis) := by
  intro e he
  simp only [reversedBasis, finalMarkerThreeBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.opposite_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6721
-- END S6_6721

-- BEGIN S6_6724
namespace S6_6724

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,6],[1,1,1,4,4,6],[1,1,1,4,4,6],[4,4,4,4,4,4],[5,5,5,4,4,5],[6,6,6,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "61e59f72fedde1908f5c0c0781da441701c1ed8ffbf00af428848731dc5c7b22"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨1, [0]⟩, ⟨1, [0, 0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0]⟩⟩
def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw.reversed := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw.reversed := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw.reversed := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis finalMarkerThreeBasis) := by
  intro e he
  simp only [reversedBasis, finalMarkerThreeBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.opposite_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6724
-- END S6_6724

-- BEGIN S6_6725
namespace S6_6725

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,6],[1,1,1,4,4,6],[1,1,1,4,4,6],[4,4,4,4,4,6],[4,4,4,4,4,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "55754d5f0b79c797bc9ce1f790570f0c6cecbfc2ec540345d4290f0f0080cb48"

def embedding :
    Embedding SemigroupBasis.Generated.S3_5.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = saturatedPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = saturatedCommutativityLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = saturatedPrefixDuplicationLaw := rfl

theorem targetModels :
    Models table.semigroup (saturatedSupportBasis) := by
  intro e he
  simp only [saturatedSupportBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (saturatedSupportBasis) :=
  SemigroupBasis.Generated.S3_5.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6725
-- END S6_6725

-- BEGIN S6_6728
namespace S6_6728

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,6],[1,1,1,4,4,6],[1,1,1,4,4,6],[4,4,4,4,4,6],[5,5,5,4,4,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "31363b0de32817da90213d08db78d21cdb241bd79217a0fe8d3ff01be12936ff"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨1, [0]⟩, ⟨1, [0, 0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0]⟩⟩
def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = finalMarkerPowerLaw.reversed := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = finalMarkerPrefixDuplicationLaw.reversed := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = finalMarkerCopyLaw.reversed := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = finalMarkerRotateLaw.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis finalMarkerThreeBasis) := by
  intro e he
  simp only [reversedBasis, finalMarkerThreeBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.opposite_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_6728
-- END S6_6728

-- BEGIN S6_6730
namespace S6_6730

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,5,1],[1,1,1,4,5,1],[1,1,1,4,5,1],[4,4,4,4,4,4],[5,5,5,4,4,5],[1,1,1,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c631f04e62a83da882055bcd360bbcbc3371f203840d56903244e190cc00915f"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6730
-- END S6_6730

-- BEGIN S6_6740
namespace S6_6740

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,5,1],[1,1,1,4,5,1],[1,1,1,4,5,3],[4,4,4,4,4,4],[5,5,5,4,4,5],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5bf6971ce3aadb7ebb0b331a7fa21641e5e60767d923d537a99682eaaf9f6692"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6740
-- END S6_6740

-- BEGIN S6_6746
namespace S6_6746

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,5,1],[1,1,1,4,5,2],[1,1,1,4,5,2],[4,4,4,4,4,4],[5,5,5,4,4,5],[1,2,2,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "036c9aaee6fb5c57f1dcfcc54ff55e864cdec47aace16c93fafd6795e1779da4"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6746
-- END S6_6746

-- BEGIN S6_6750
namespace S6_6750

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,5,1],[1,1,1,4,5,2],[1,1,1,4,5,3],[4,4,4,4,4,4],[5,5,5,4,4,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2c83ff3e2889d1e6b8e282c472387fe0dc6042efff9c08a14ab253799a8da4ca"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6750
-- END S6_6750

-- BEGIN S6_6752
namespace S6_6752

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,5,4],[1,1,1,4,5,4],[1,1,1,4,5,4],[4,4,4,4,4,4],[5,5,5,4,4,4],[4,4,4,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "77be818f7eaad07464f64a377b8521b822409045be0cdbedae3863ec74b1e11e"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6752
-- END S6_6752

-- BEGIN S6_6755
namespace S6_6755

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,5,6],[1,1,1,4,5,6],[1,1,1,4,5,6],[4,4,4,4,4,4],[5,5,5,4,4,4],[6,6,6,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cae9cd190de41039d0bf5aaf7f50f52661678b273c9673c1349802f347e9dcc8"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6755
-- END S6_6755

-- BEGIN S6_6758
namespace S6_6758

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,5,6],[1,1,1,4,5,6],[1,1,1,4,5,6],[4,4,4,4,4,4],[5,5,5,4,4,5],[6,6,6,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b0331b75df479636553db1ea6eb027ae0ed02834f6d34cd8a50569216166957b"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6758
-- END S6_6758

-- BEGIN S6_6759
namespace S6_6759

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,5,6],[1,1,1,4,5,6],[1,1,1,4,5,6],[4,4,4,4,4,6],[5,5,5,4,4,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5b3df71d536c93d370260611665212c6faf2aed15e8d364d93688e9e31f8cc60"

def embedding :
    Embedding SemigroupBasis.Generated.S3_8.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = exponentThreeLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = exponentCommutativityLaw := rfl

theorem targetModels :
    Models table.semigroup (commutativeExponentThreeBasis) := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (commutativeExponentThreeBasis) :=
  SemigroupBasis.Generated.S3_8.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6759
-- END S6_6759

-- BEGIN S6_6763
namespace S6_6763

/-- Exact one-based order-six catalogue table: `[[1,1,1,6,6,6],[1,1,1,6,6,6],[1,1,1,6,6,6],[6,6,6,4,4,6],[6,6,6,4,4,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "dfd1841838bc86359dacb32d516ebad5d8375e5a9014682656c2b5cb173ceebf"

def embedding :
    Embedding SemigroupBasis.Generated.S3_9.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = saturatedPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = saturatedCommutativityLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = saturatedPrefixDuplicationLaw := rfl

theorem targetModels :
    Models table.semigroup (saturatedSupportBasis) := by
  intro e he
  simp only [saturatedSupportBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (saturatedSupportBasis) :=
  SemigroupBasis.Generated.S3_9.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_6763
-- END S6_6763

-- BEGIN S6_7055
namespace S6_7055

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,1],[1,1,1,1,5,1],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0959572a58f555e505b4a300506b77bd7d55be42e95babe57c83efa0b8a0545f"

def embedding :
    Embedding SemigroupBasis.Generated.S3_5.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = saturatedPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = saturatedCommutativityLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = saturatedPrefixDuplicationLaw := rfl

theorem targetModels :
    Models table.semigroup (saturatedSupportBasis) := by
  intro e he
  simp only [saturatedSupportBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (saturatedSupportBasis) :=
  SemigroupBasis.Generated.S3_5.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_7055
-- END S6_7055

-- BEGIN S6_7056
namespace S6_7056

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,1],[1,1,1,1,5,1],[1,1,3,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4d6571bcf8302497a804d0305ff1cab633e0dfc6cdd9cef2f74e3a439cc5707a"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7056
-- END S6_7056

-- BEGIN S6_7057
namespace S6_7057

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,1],[1,1,1,1,5,1],[1,2,2,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2261062ac4bde6bfc85347ce4f4ddafb807d2d579ebdaad888ac7c392438deb8"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7057
-- END S6_7057

-- BEGIN S6_7058
namespace S6_7058

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,1],[1,1,1,1,5,1],[1,2,3,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "1854dc5ecb4e7449cab09cc9170857c84aa36eaabf1b100d38c4ae60783160f9"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7058
-- END S6_7058

-- BEGIN S6_7060
namespace S6_7060

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,1],[1,1,1,1,5,5],[1,1,1,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2a9b890a31db9e9b2dc3a83cb537f31f3bb6037f4710dbbdfbd537b63961b974"

def embedding :
    Embedding SemigroupBasis.Generated.S3_5.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = saturatedPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = saturatedCommutativityLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = saturatedPrefixDuplicationLaw := rfl

theorem targetModels :
    Models table.semigroup (saturatedSupportBasis) := by
  intro e he
  simp only [saturatedSupportBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (saturatedSupportBasis) :=
  SemigroupBasis.Generated.S3_5.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_7060
-- END S6_7060

-- BEGIN S6_7062
namespace S6_7062

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,1],[1,1,1,1,5,5],[1,1,3,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "47c539d42fb1cca700e21c8d4be7a95030dbb765303c6d0ac7c851b94b70b408"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7062
-- END S6_7062

-- BEGIN S6_7063
namespace S6_7063

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,1],[1,1,1,1,5,5],[1,2,2,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "13126035e7f8e9182be4bfdcc32967e8be27e3643801de90a8453f468cf2e9f0"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7063
-- END S6_7063

-- BEGIN S6_7064
namespace S6_7064

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,1],[1,1,1,1,5,5],[1,2,3,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2ecbc246369768000bf98117755472828b6638952d691b6090b74695ea1578e1"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7064
-- END S6_7064

-- BEGIN S6_7066
namespace S6_7066

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,1],[1,1,3,1,5,1],[1,2,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a4cedebe1a4759ed93042a15979a53974e61ac1a265210a74446fd5cfe103444"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7066
-- END S6_7066

-- BEGIN S6_7068
namespace S6_7068

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,1],[1,1,3,1,5,5],[1,1,3,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "120a696b6ea86231c2161eb93913671f974c8a09b399b1d3a0370d8ed06b8fcc"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7068
-- END S6_7068

-- BEGIN S6_7070
namespace S6_7070

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,1],[1,1,3,1,5,5],[1,2,3,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "66a73a3fa4b6e26bd7bd16679b80fa53e6e08ff3a8733dfb7f75ec8f65b5b49f"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7070
-- END S6_7070

-- BEGIN S6_7075
namespace S6_7075

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,1],[1,2,2,1,5,5],[1,2,2,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "951562df35333e33dbddd691b42a98106a46e594a9e0d8472644f68ba911127f"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7075
-- END S6_7075

-- BEGIN S6_7077
namespace S6_7077

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,1],[1,2,2,1,5,5],[1,2,3,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a9f5589b700ca515e3566c1355cf6ac5bc282d0a5d12921a5e3a3080662e7153"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7077
-- END S6_7077

-- BEGIN S6_7082
namespace S6_7082

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,1],[1,2,3,1,5,5],[1,2,3,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e437a0240c5d87652815f09f187310d7d76d7670a4bd68801ffbbba5e4986872"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7082
-- END S6_7082

-- BEGIN S6_7088
namespace S6_7088

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,4],[1,1,1,1,5,5],[1,1,1,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "1ba0e8ad95babe4962c6721cf01281ae44723d5a6050ae2ab8087dec53e8c859"

def embedding :
    Embedding SemigroupBasis.Generated.S3_5.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = saturatedPowerLaw := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = saturatedCommutativityLaw := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = saturatedPrefixDuplicationLaw := rfl

theorem targetModels :
    Models table.semigroup (saturatedSupportBasis) := by
  intro e he
  simp only [saturatedSupportBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (saturatedSupportBasis) :=
  SemigroupBasis.Generated.S3_5.representative_basis.inheritAlongEmbedding embedding targetModels

end S6_7088
-- END S6_7088

-- BEGIN S6_7089
namespace S6_7089

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,4],[1,1,1,1,5,5],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "74b5a9c75edc55ac8d2b5d1512d61cea8b4978e17b99d44ad9251661b0f68509"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7089
-- END S6_7089

-- BEGIN S6_7090
namespace S6_7090

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,4],[1,1,1,1,5,5],[1,2,2,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cce5da56c449e45b3927a4298eedfb32c1238fed21cd6999d7d4d695d67ec190"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7090
-- END S6_7090

-- BEGIN S6_7091
namespace S6_7091

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,4],[1,1,1,1,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "f2c497bcd23a85033935511d1f45713d0547da304a4aa5f636a0d94759127d80"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7091
-- END S6_7091

-- BEGIN S6_7092
namespace S6_7092

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,4],[1,1,3,1,5,1],[1,1,1,4,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0898092eadd448ffdf0ae99313194b5ceca493b7776c4406f7cdd8cc4d61dc7e"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7092
-- END S6_7092

-- BEGIN S6_7094
namespace S6_7094

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,4],[1,1,3,1,5,1],[1,2,1,4,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "7982661104dcfdd681f098e5709fc8d2180c9f6520764d123816fb8c6294a91d"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7094
-- END S6_7094

-- BEGIN S6_7095
namespace S6_7095

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,4,1,4],[1,1,3,1,5,5],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "baabc508b33d9539321d783d2e4850d20e7ba0574e11581e3389dfbbd46d7321"

def embedding :
    Embedding SemigroupBasis.Generated.S3_6.table.semigroup
      table.semigroup where
  toFun := fun a : Fin 3 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 1) :=
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

theorem targetModels :
    Models table.semigroup (finalMarkerThreeBasis) := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (finalMarkerThreeBasis) :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (finalMarkerThreeBasis)) :=
  representative_basis.oppositeReversed

end S6_7095
-- END S6_7095

end SemigroupBasis.Generated.Order6EmbeddingTransfers

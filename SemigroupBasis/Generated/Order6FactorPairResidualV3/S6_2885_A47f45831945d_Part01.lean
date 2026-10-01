import SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorPairResidualV3.S6_2885_A47f45831945d_Part01

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S6_2886
namespace S6_2886

/-- Exact selected representative table, one-based: `[[1,1,3,3,3,1],[1,1,3,3,3,1],[3,3,1,1,1,3],[3,3,1,1,1,3],[3,3,1,1,2,3],[1,1,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "15f5760197f7bd8b83dc47e65cf52a816556bfe520671adec87e4728ba300f9a"

/-- Exact one-based coordinate maps: `[[1,1,3,4,3,6],[1,2,3,3,5,1]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,1,3,4,3,6],[1,2,3,3,5,1]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,1,3,4,3,6],[1,2,3,3,5,1]] := by decide

def coordinateValue (i : Fin 2) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (4 : Fin 6) else (0 : Fin 6)

def coordinateHom (i : Fin 2) :
    Hom (SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceSemigroup) (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0, 0]⟩⟩
def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 0, 1]⟩, ⟨0, [0, 1]⟩⟩
def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0, 1, 2]⟩, ⟨0, [1, 2]⟩⟩
def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 1, 1]⟩⟩
def finiteLaw5 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
def finiteLaw6 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1, 1]⟩, ⟨0, [1, 0]⟩⟩
def finiteLaw7 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 1, 0]⟩⟩
def finiteLaw8 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩
def finiteLaw9 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceLaw0 := rfl
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceLaw1 := rfl
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceLaw2 := rfl
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceLaw3 := rfl
theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceLaw4 := rfl
theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceLaw5 := rfl
theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceLaw6 := rfl
theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceLaw7 := rfl
theorem finiteLaw8_map :
    finiteLaw8.map Fin.val = SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceLaw8 := rfl
theorem finiteLaw9_map :
    finiteLaw9.map Fin.val = SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceLaw9 := rfl

theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he
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
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)
  · subst e
    rw [← finiteLaw5_map]
    exact table.checkIdentityNat_sound finiteLaw5 (by decide)
  · subst e
    rw [← finiteLaw6_map]
    exact table.checkIdentityNat_sound finiteLaw6 (by decide)
  · subst e
    rw [← finiteLaw7_map]
    exact table.checkIdentityNat_sound finiteLaw7 (by decide)
  · subst e
    rw [← finiteLaw8_map]
    exact table.checkIdentityNat_sound finiteLaw8 (by decide)
  · subst e
    rw [← finiteLaw9_map]
    exact table.checkIdentityNat_sound finiteLaw9 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2885.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_2886
-- END S6_2886

end SemigroupBasis.Generated.Order6FactorPairResidualV3.S6_2885_A47f45831945d_Part01

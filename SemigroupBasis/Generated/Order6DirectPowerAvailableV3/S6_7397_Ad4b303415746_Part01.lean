import SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3.S6_7397_Ad4b303415746_Part01

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S6_12666
namespace S6_12666

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,3,1,3,1],[1,2,1,4,1,2],[1,1,5,1,5,1],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2f24100321fe20b20031b4a0d2bc6ebdc388d779283d63595c40ec0694cd504f"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,3,1,1],[1,1,1,1,1,3],[3,3,3,3,5,3],[1,1,2,4,1,6]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,3,1,1],[1,1,1,1,1,3],[3,3,3,3,5,3],[1,1,2,4,1,6]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,3,1,1],[1,1,1,1,1,3],[3,3,3,3,5,3],[1,1,2,4,1,6]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (2 : Fin 6) else if i = 3 then if a = 0 then (2 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (4 : Fin 6) else (2 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (0 : Fin 6) else (5 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 1) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw0).map (fun value => (0 : Fin 1))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw2 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw2).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw3 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw3).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw4 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw4).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw5 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw5).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw1 := by decide
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw2 := by decide
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw3 := by decide
theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw4 := by decide
theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw5 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he
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

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_12666
-- END S6_12666

-- BEGIN S6_12707
namespace S6_12707

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,3,1,3,3],[1,2,1,4,1,2],[1,1,5,1,5,5],[1,1,3,1,3,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b9dfc4bd035fa0f7132806a3e178e9ed76644ac53c0922c6c0e9a2ac0278d4d9"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,3,1,1],[1,1,1,1,1,3],[3,3,3,3,5,3],[1,1,2,4,1,6]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,3,1,1],[1,1,1,1,1,3],[3,3,3,3,5,3],[1,1,2,4,1,6]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,3,1,1],[1,1,1,1,1,3],[3,3,3,3,5,3],[1,1,2,4,1,6]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (2 : Fin 6) else if i = 3 then if a = 0 then (2 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (4 : Fin 6) else (2 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (0 : Fin 6) else (5 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 1) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw0).map (fun value => (0 : Fin 1))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw2 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw2).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw3 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw3).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw4 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw4).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw5 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw5).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw1 := by decide
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw2 := by decide
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw3 := by decide
theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw4 := by decide
theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceLaw5 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he
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

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7397.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_12707
-- END S6_12707

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3.S6_7397_Ad4b303415746_Part01

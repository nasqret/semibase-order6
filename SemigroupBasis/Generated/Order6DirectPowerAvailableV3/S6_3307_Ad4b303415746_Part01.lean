import SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3.S6_3307_Ad4b303415746_Part01

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S6_7348
namespace S6_7348

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,1,1,4,4,1],[1,1,1,5,5,1],[1,2,3,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d62049b22772ec9c01b64d2f30b6f7ad6ecd653acc74664f798fd81b382bb9d7"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,1,1,4],[4,4,4,4,5,4],[1,1,2,1,1,6],[1,1,1,3,1,6]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,1,1,4],[4,4,4,4,5,4],[1,1,2,1,1,6],[1,1,1,3,1,6]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,1,1,4],[4,4,4,4,5,4],[1,1,2,1,1,6],[1,1,1,3,1,6]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if i = 2 then if a = 0 then (3 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (3 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (0 : Fin 6) else (5 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 1) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw0).map (fun value => (0 : Fin 1))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw2 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw2).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw3 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw3).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw4 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw4).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw5 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw5).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw6 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw6).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw7 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw7).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw8 : Identity (Fin 4) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw8).map (fun value => if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (2 : Fin 4) else (3 : Fin 4))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw1 := by decide
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw2 := by decide
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw3 := by decide
theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw4 := by decide
theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw5 := by decide
theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw6 := by decide
theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw7 := by decide
theorem finiteLaw8_map :
    finiteLaw8.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw8 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he
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

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_7348
-- END S6_7348

-- BEGIN S6_7364
namespace S6_7364

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,1,1,4,4,4],[1,1,1,5,5,5],[1,2,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "503bd6c70afc5d7208735f4f69d6def5ef63c5f5eae6b19aff2283d94d4eca42"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,1,1,4],[4,4,4,4,5,4],[1,1,2,1,1,6],[1,1,1,3,1,6]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,1,1,4],[4,4,4,4,5,4],[1,1,2,1,1,6],[1,1,1,3,1,6]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,1,1,4],[4,4,4,4,5,4],[1,1,2,1,1,6],[1,1,1,3,1,6]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if i = 2 then if a = 0 then (3 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (3 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (0 : Fin 6) else (5 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 1) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw0).map (fun value => (0 : Fin 1))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw2 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw2).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw3 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw3).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw4 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw4).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw5 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw5).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw6 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw6).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw7 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw7).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw8 : Identity (Fin 4) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw8).map (fun value => if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (2 : Fin 4) else (3 : Fin 4))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw1 := by decide
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw2 := by decide
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw3 := by decide
theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw4 := by decide
theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw5 := by decide
theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw6 := by decide
theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw7 := by decide
theorem finiteLaw8_map :
    finiteLaw8.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw8 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he
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

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_7364
-- END S6_7364

-- BEGIN S6_7447
namespace S6_7447

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,2,1,4,1,1],[5,5,5,5,5,5],[1,1,3,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "f4d2071d5246193ca446c92aee0b3501d0bdb2c95dde92c50c9ebe030bbefc87"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,1,5,1],[1,1,1,1,1,4],[1,1,2,1,1,4],[1,1,1,3,1,6]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,1,5,1],[1,1,1,1,1,4],[1,1,2,1,1,4],[1,1,1,3,1,6]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,1,5,1],[1,1,1,1,1,4],[1,1,2,1,1,4],[1,1,1,3,1,6]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (4 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (0 : Fin 6) else (5 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 1) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw0).map (fun value => (0 : Fin 1))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw2 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw2).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw3 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw3).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw4 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw4).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw5 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw5).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw6 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw6).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw7 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw7).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw8 : Identity (Fin 4) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw8).map (fun value => if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (2 : Fin 4) else (3 : Fin 4))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw1 := by decide
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw2 := by decide
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw3 := by decide
theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw4 := by decide
theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw5 := by decide
theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw6 := by decide
theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw7 := by decide
theorem finiteLaw8_map :
    finiteLaw8.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw8 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he
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

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_7447
-- END S6_7447

-- BEGIN S6_7457
namespace S6_7457

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,2,1,4,4,1],[1,2,1,5,5,1],[1,1,3,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "1cc988fde391409cd7713e7393631fae131f449a8daa47e338f55e51537e890d"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,1,1,4],[1,1,2,1,1,4],[4,4,4,4,5,4],[1,1,1,3,1,6]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,1,1,4],[1,1,2,1,1,4],[4,4,4,4,5,4],[1,1,1,3,1,6]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,1,1,4],[1,1,2,1,1,4],[4,4,4,4,5,4],[1,1,1,3,1,6]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if i = 3 then if a = 0 then (3 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (0 : Fin 6) else (5 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 1) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw0).map (fun value => (0 : Fin 1))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw2 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw2).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw3 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw3).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw4 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw4).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw5 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw5).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw6 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw6).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw7 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw7).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw8 : Identity (Fin 4) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw8).map (fun value => if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (2 : Fin 4) else (3 : Fin 4))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw1 := by decide
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw2 := by decide
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw3 := by decide
theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw4 := by decide
theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw5 := by decide
theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw6 := by decide
theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw7 := by decide
theorem finiteLaw8_map :
    finiteLaw8.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw8 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he
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

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_7457
-- END S6_7457

-- BEGIN S6_7466
namespace S6_7466

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,2,1,4,4,4],[1,2,1,5,5,5],[1,2,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "539f7c67e798d7a5922254a75ecdb01312edb488d5274e5d7bca4e96f938daab"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,1,1,4],[1,1,2,1,1,4],[4,4,4,4,5,4],[1,1,1,3,1,6]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,1,1,4],[1,1,2,1,1,4],[4,4,4,4,5,4],[1,1,1,3,1,6]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,1,1,4],[1,1,2,1,1,4],[4,4,4,4,5,4],[1,1,1,3,1,6]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if i = 3 then if a = 0 then (3 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (0 : Fin 6) else (5 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 1) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw0).map (fun value => (0 : Fin 1))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw2 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw2).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw3 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw3).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw4 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw4).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw5 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw5).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw6 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw6).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw7 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw7).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw8 : Identity (Fin 4) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw8).map (fun value => if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (2 : Fin 4) else (3 : Fin 4))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw1 := by decide
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw2 := by decide
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw3 := by decide
theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw4 := by decide
theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw5 := by decide
theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw6 := by decide
theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw7 := by decide
theorem finiteLaw8_map :
    finiteLaw8.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw8 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he
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

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_7466
-- END S6_7466

-- BEGIN S6_7597
namespace S6_7597

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,2,1,4,1,1],[1,1,3,1,5,5],[1,1,3,1,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "6a77352d323bff445030e705ca05089169292ace79e521cb8fcd00e0823fd87b"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,1,1,4],[1,1,2,1,1,4],[1,1,1,3,1,5],[5,5,5,5,6,5]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,1,1,4],[1,1,2,1,1,4],[1,1,1,3,1,5],[5,5,5,5,6,5]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,1,1,4],[1,1,2,1,1,4],[1,1,1,3,1,5],[5,5,5,5,6,5]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (0 : Fin 6) else (4 : Fin 6) else if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (5 : Fin 6) else (4 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 1) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw0).map (fun value => (0 : Fin 1))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw2 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw2).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw3 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw3).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw4 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw4).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw5 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw5).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw6 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw6).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw7 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw7).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw8 : Identity (Fin 4) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw8).map (fun value => if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (2 : Fin 4) else (3 : Fin 4))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw1 := by decide
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw2 := by decide
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw3 := by decide
theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw4 := by decide
theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw5 := by decide
theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw6 := by decide
theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw7 := by decide
theorem finiteLaw8_map :
    finiteLaw8.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw8 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he
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

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_7597
-- END S6_7597

-- BEGIN S6_7700
namespace S6_7700

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,3,3,3],[1,1,3,4,4,4],[1,1,3,5,5,5],[1,2,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c4898bf683c8c76acc5e52af6c8ed78fed0e40c3d5e2b7f94e0fe94801201940"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,1,1,4],[1,1,1,3,1,4],[4,4,4,4,5,4],[1,1,2,1,1,6]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,1,1,4],[1,1,1,3,1,4],[4,4,4,4,5,4],[1,1,2,1,1,6]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,1,1,4],[1,1,1,3,1,4],[4,4,4,4,5,4],[1,1,2,1,1,6]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if i = 3 then if a = 0 then (3 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (5 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 1) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw0).map (fun value => (0 : Fin 1))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw2 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw2).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw3 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw3).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw4 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw4).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw5 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw5).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw6 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw6).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw7 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw7).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw8 : Identity (Fin 4) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw8).map (fun value => if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (2 : Fin 4) else (3 : Fin 4))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw1 := by decide
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw2 := by decide
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw3 := by decide
theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw4 := by decide
theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw5 := by decide
theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw6 := by decide
theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw7 := by decide
theorem finiteLaw8_map :
    finiteLaw8.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceLaw8 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he
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

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3307.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_7700
-- END S6_7700

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3.S6_3307_Ad4b303415746_Part01

import SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3.S6_5959_Ad4b303415746_Part01

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S6_8907
namespace S6_8907

/-- Exact selected representative table, one-based: `[[1,1,3,1,5,5],[1,1,3,1,5,5],[3,3,1,3,5,5],[1,2,3,4,5,6],[5,5,5,5,5,5],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "7ddb72b6b12a17541f86df62b95e8e5b75dbb94e37d8bbfa053f8fc3b990106c"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,4,4,1],[1,1,2,4,4,1],[5,5,5,1,3,5],[6,6,6,4,4,5]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,4,4,1],[1,1,2,4,4,1],[5,5,5,1,3,5],[6,6,6,4,4,5]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,4,4,1],[1,1,2,4,4,1],[5,5,5,1,3,5],[6,6,6,4,4,5]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (2 : Fin 6) else (4 : Fin 6) else if a = 0 then (5 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (5 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (3 : Fin 6) else (4 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_8907
-- END S6_8907

-- BEGIN S6_8918
namespace S6_8918

/-- Exact selected representative table, one-based: `[[1,1,3,1,5,6],[1,1,3,1,5,6],[3,3,1,3,5,6],[1,2,3,4,5,6],[5,5,5,5,5,5],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "dae1d255ca3d385e4a154e318034439d7a583944af79e2c3c988c8b7758e3a9b"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,4,4,1],[1,1,2,4,4,1],[6,6,6,1,1,5],[5,5,5,1,3,5]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,4,4,1],[1,1,2,4,4,1],[6,6,6,1,1,5],[5,5,5,1,3,5]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,4,4,1],[1,1,2,4,4,1],[6,6,6,1,1,5],[5,5,5,1,3,5]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (5 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (5 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (4 : Fin 6) else if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (2 : Fin 6) else (4 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_8918
-- END S6_8918

-- BEGIN S6_10183
namespace S6_10183

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,3,4,1,1],[1,1,4,3,1,1],[1,2,1,1,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "faae4bd4da3405fdb181810fd4594dfc44516d91157088ce7eeb91f2f7ca5f96"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,1,3,4,1],[1,1,2,5,5,1],[6,6,6,5,5,1]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,1,3,4,1],[1,1,2,5,5,1],[6,6,6,5,5,1]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,1,3,4,1],[1,1,2,5,5,1],[6,6,6,5,5,1]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 0 then (5 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (5 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (4 : Fin 6) else (0 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_10183
-- END S6_10183

-- BEGIN S6_10195
namespace S6_10195

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,3,4,1,3],[1,1,4,3,1,4],[5,5,5,5,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "6a63417aa42bd498c818c594f200cbb6174df3274cac4d7e2f72927fce304f5f"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,1,3,4,1],[1,1,2,6,6,1],[5,5,5,6,6,1]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,1,3,4,1],[1,1,2,6,6,1],[5,5,5,6,6,1]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,1,3,4,1],[1,1,2,6,6,1],[5,5,5,6,6,1]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (5 : Fin 6) else (0 : Fin 6) else if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (5 : Fin 6) else (0 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_10195
-- END S6_10195

-- BEGIN S6_10199
namespace S6_10199

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,3,4,1,6],[1,1,4,3,1,6],[1,2,1,1,5,1],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "036b1317fb057cb39306ec0102c03671fdfd37b98d3092f3e5d2f6e043f820d7"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,3,3,1],[6,6,6,3,3,1],[1,1,1,3,4,1],[1,1,2,5,5,1]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,3,3,1],[6,6,6,3,3,1],[1,1,1,3,4,1],[1,1,2,5,5,1]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,3,3,1],[6,6,6,3,3,1],[1,1,1,3,4,1],[1,1,2,5,5,1]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (5 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (5 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (4 : Fin 6) else (0 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_10199
-- END S6_10199

-- BEGIN S6_10216
namespace S6_10216

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,3,4,3,6],[1,1,4,3,4,6],[1,2,3,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ab8a878881331f546f087190ff4c08dd3a52c5b2a8c23c9f634f1fa0d29977c8"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,3,3,1],[6,6,6,3,3,1],[1,1,1,3,4,1],[1,1,2,5,5,1]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,3,3,1],[6,6,6,3,3,1],[1,1,1,3,4,1],[1,1,2,5,5,1]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,3,3,1],[6,6,6,3,3,1],[1,1,1,3,4,1],[1,1,2,5,5,1]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (5 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (5 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (4 : Fin 6) else (0 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_10216
-- END S6_10216

-- BEGIN S6_10364
namespace S6_10364

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,4,1,1],[1,2,4,3,1,1],[1,1,1,1,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "760afb7d1bc248506a387170fbef72fac3f84c0805e219ac479b791f1cfbe84b"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[6,6,6,5,5,1]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[6,6,6,5,5,1]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[6,6,6,5,5,1]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 0 then (5 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (5 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (4 : Fin 6) else (0 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_10364
-- END S6_10364

-- BEGIN S6_10370
namespace S6_10370

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,4,1,3],[1,2,4,3,1,4],[5,5,5,5,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "6bc83395678a8bca7fd1ddc8f43d76cfb29c526564233c0841341641511b3545"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[5,5,5,6,6,1]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[5,5,5,6,6,1]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[5,5,5,6,6,1]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (5 : Fin 6) else (0 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_10370
-- END S6_10370

-- BEGIN S6_10394
namespace S6_10394

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,4,5,6],[1,2,4,3,5,6],[1,1,5,5,5,5],[1,1,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "69b1c9df3f685210c4113a707f1e40f22522746ed25f324e3afb8b7110a4c9e8"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[6,6,6,3,3,5]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[6,6,6,3,3,5]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[6,6,6,3,3,5]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 0 then (5 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (5 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (4 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_10394
-- END S6_10394

-- BEGIN S6_10402
namespace S6_10402

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,4,5,6],[1,2,4,3,5,6],[1,2,5,5,5,5],[1,2,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "77f5b6531ae54da909705c46303f0a7441431dde5b8b093db3be42a8cd46345e"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[6,6,6,3,3,5]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[6,6,6,3,3,5]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[6,6,6,3,3,5]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 0 then (5 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (5 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (4 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_10402
-- END S6_10402

-- BEGIN S6_10676
namespace S6_10676

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[5,5,3,4,5,3],[5,5,4,3,5,4],[5,5,5,5,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "6d4db78520ca8495aecd7626a35cca16f8c5bc0b4a08a40b12c58899a1250f1d"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,6,6,1],[1,1,2,6,6,1],[5,5,5,6,6,1],[5,5,5,3,4,5]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,6,6,1],[1,1,2,6,6,1],[5,5,5,6,6,1],[5,5,5,3,4,5]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,6,6,1],[1,1,2,6,6,1],[5,5,5,6,6,1],[5,5,5,3,4,5]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (5 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (5 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (5 : Fin 6) else (0 : Fin 6) else if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (3 : Fin 6) else (4 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_10676
-- END S6_10676

-- BEGIN S6_10681
namespace S6_10681

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[5,5,3,4,5,5],[5,5,4,3,5,5],[5,5,5,5,5,5],[1,2,5,5,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 3 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "332aa8290c2d78015b5118d6b523c6ba2c8f2abb0a784064f8e4ddceb0fdf73f"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,6,6,1],[1,1,2,6,6,1],[5,5,5,6,6,1],[5,5,5,3,4,5]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,6,6,1],[1,1,2,6,6,1],[5,5,5,6,6,1],[5,5,5,3,4,5]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,6,6,1],[1,1,2,6,6,1],[5,5,5,6,6,1],[5,5,5,3,4,5]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (5 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (5 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (5 : Fin 6) else (0 : Fin 6) else if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (3 : Fin 6) else (4 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_10681
-- END S6_10681

-- BEGIN S6_11748
namespace S6_11748

/-- Exact selected representative table, one-based: `[[1,1,1,1,5,6],[1,1,1,1,5,6],[1,2,3,4,5,6],[1,2,4,3,5,6],[5,5,5,5,5,5],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cde76ce2371fea112721429e8c43c9d71b4b46003e15151e442767a228e2a30e"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[6,6,6,1,1,5]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[6,6,6,1,1,5]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[6,6,6,1,1,5]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 0 then (5 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (5 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (4 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceLaw1 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5959.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_11748
-- END S6_11748

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3.S6_5959_Ad4b303415746_Part01

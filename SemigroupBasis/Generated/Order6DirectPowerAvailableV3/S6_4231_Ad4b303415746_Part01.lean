import SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3.S6_4231_Ad4b303415746_Part01

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S6_6990
namespace S6_6990

/-- Exact selected representative table, one-based: `[[1,2,2,1,2,6],[2,1,1,2,1,6],[2,1,1,2,1,6],[4,5,5,4,5,6],[5,4,4,5,4,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b632a42884bcd96c47cb0d53aa9a7c2ea1c9da2bff9cb103ad830e7eac65cd80"

/-- Exact one-based coordinate maps: `[[1,2,2,2,1,1],[1,2,3,2,1,1],[1,2,2,3,1,1],[6,6,6,6,1,1],[6,6,6,6,4,1]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,2,2,1,1],[1,2,3,2,1,1],[1,2,2,3,1,1],[6,6,6,6,1,1],[6,6,6,6,4,1]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,2,2,1,1],[1,2,3,2,1,1],[1,2,2,3,1,1],[6,6,6,6,1,1],[6,6,6,6,4,1]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (1 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (1 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (5 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (5 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 0 then (5 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (5 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw2 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw2).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw3 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw3).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw1 := by decide
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw2 := by decide
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw3 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
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

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_6990
-- END S6_6990

-- BEGIN S6_9069
namespace S6_9069

/-- Exact selected representative table, one-based: `[[1,2,2,4,4,4],[2,1,1,4,4,4],[2,1,1,4,4,4],[4,4,4,4,4,4],[4,4,4,4,5,5],[4,4,4,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 2 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "23aa09abccd6f42f9aa74bc214bd0d5ca05aab38d6cc951033e38e909f8d883c"

/-- Exact one-based coordinate maps: `[[1,2,2,2,1,1],[1,2,3,2,1,1],[1,2,2,3,1,1],[4,4,4,4,1,1],[4,4,4,4,6,5]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,2,2,1,1],[1,2,3,2,1,1],[1,2,2,3,1,1],[4,4,4,4,1,1],[4,4,4,4,6,5]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,2,2,1,1],[1,2,3,2,1,1],[1,2,2,3,1,1],[4,4,4,4,1,1],[4,4,4,4,6,5]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (1 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (1 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (3 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 0 then (3 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (5 : Fin 6) else (4 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw2 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw2).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw3 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw3).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw1 := by decide
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw2 := by decide
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceLaw3 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
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

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4231.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_9069
-- END S6_9069

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3.S6_4231_Ad4b303415746_Part01

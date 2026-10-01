import SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3.S6_2855_Ad4b303415746_Part01

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S6_9578
namespace S6_9578

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,2,1,1,3],[1,1,1,4,5,1],[1,1,1,5,4,1],[1,2,3,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "220506333edf97b5ee429722ec685e435f647941a1116da336d357b67a893231"

/-- Exact one-based coordinate maps: `[[1,1,2,1,1,1],[1,1,1,1,1,4],[4,4,4,5,4,4],[1,1,1,1,2,6],[1,2,1,1,3,6]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,1,2,1,1,1],[1,1,1,1,1,4],[4,4,4,5,4,4],[1,1,1,1,2,6],[1,2,1,1,3,6]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,1,2,1,1,1],[1,1,1,1,1,4],[4,4,4,5,4,4],[1,1,1,1,2,6],[1,2,1,1,3,6]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if i = 2 then if a = 0 then (3 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (3 : Fin 6) else (3 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (2 : Fin 6) else (5 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 1) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceLaw1).map (fun value => (0 : Fin 1))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceLaw1 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_9578
-- END S6_9578

-- BEGIN S6_9579
namespace S6_9579

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,2,1,1,3],[1,1,1,4,5,4],[1,1,1,5,4,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5b284a8367c83d8be7e1ee713dc5a9c1dfc978679ef382b955ebe5c7bdc3db87"

/-- Exact one-based coordinate maps: `[[1,1,2,1,1,1],[1,1,1,1,1,4],[4,4,4,5,4,4],[1,1,1,1,2,6],[1,2,1,1,3,6]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,1,2,1,1,1],[1,1,1,1,1,4],[4,4,4,5,4,4],[1,1,1,1,2,6],[1,2,1,1,3,6]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,1,2,1,1,1],[1,1,1,1,1,4],[4,4,4,5,4,4],[1,1,1,1,2,6],[1,2,1,1,3,6]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if i = 2 then if a = 0 then (3 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (3 : Fin 6) else (3 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (2 : Fin 6) else (5 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceLaw0).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw1 : Identity (Fin 1) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceLaw1).map (fun value => (0 : Fin 1))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceLaw1 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2855.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_9579
-- END S6_9579

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3.S6_2855_Ad4b303415746_Part01

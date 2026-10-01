import SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3.S6_5954_Ad4b303415746_Part02

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S6_10194
namespace S6_10194

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,3,4,1,3],[1,1,4,3,1,4],[5,5,5,5,5,5],[1,2,3,4,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "6669653b8f6cb66361e4ce488bcdea8cdf33795710d5cbe9fd0632e330a320bf"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,1,3,4,1],[5,5,5,5,5,1],[1,1,2,6,6,1]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,1,3,4,1],[5,5,5,5,5,1],[1,1,2,6,6,1]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,1,3,4,1],[5,5,5,5,5,1],[1,1,2,6,6,1]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (5 : Fin 6) else (0 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 1) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw0).map (fun value => (0 : Fin 1))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw2 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw2).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw3 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw3).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw4 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw4).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw5 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw5).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw6 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw6).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw7 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw7).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw8 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw8).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw9 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw9).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw10 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw10).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw11 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw11).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw12 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw12).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw13 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw13).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw14 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw14).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw15 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw15).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw16 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw16).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw17 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw17).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw18 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw18).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw19 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw19).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw20 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw20).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw21 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw21).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw22 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw22).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw1 := by decide
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw2 := by decide
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw3 := by decide
theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw4 := by decide
theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw5 := by decide
theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw6 := by decide
theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw7 := by decide
theorem finiteLaw8_map :
    finiteLaw8.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw8 := by decide
theorem finiteLaw9_map :
    finiteLaw9.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw9 := by decide
theorem finiteLaw10_map :
    finiteLaw10.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw10 := by decide
theorem finiteLaw11_map :
    finiteLaw11.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw11 := by decide
theorem finiteLaw12_map :
    finiteLaw12.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw12 := by decide
theorem finiteLaw13_map :
    finiteLaw13.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw13 := by decide
theorem finiteLaw14_map :
    finiteLaw14.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw14 := by decide
theorem finiteLaw15_map :
    finiteLaw15.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw15 := by decide
theorem finiteLaw16_map :
    finiteLaw16.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw16 := by decide
theorem finiteLaw17_map :
    finiteLaw17.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw17 := by decide
theorem finiteLaw18_map :
    finiteLaw18.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw18 := by decide
theorem finiteLaw19_map :
    finiteLaw19.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw19 := by decide
theorem finiteLaw20_map :
    finiteLaw20.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw20 := by decide
theorem finiteLaw21_map :
    finiteLaw21.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw21 := by decide
theorem finiteLaw22_map :
    finiteLaw22.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw22 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
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
  · subst e
    rw [← finiteLaw10_map]
    exact table.checkIdentityNat_sound finiteLaw10 (by decide)
  · subst e
    rw [← finiteLaw11_map]
    exact table.checkIdentityNat_sound finiteLaw11 (by decide)
  · subst e
    rw [← finiteLaw12_map]
    exact table.checkIdentityNat_sound finiteLaw12 (by decide)
  · subst e
    rw [← finiteLaw13_map]
    exact table.checkIdentityNat_sound finiteLaw13 (by decide)
  · subst e
    rw [← finiteLaw14_map]
    exact table.checkIdentityNat_sound finiteLaw14 (by decide)
  · subst e
    rw [← finiteLaw15_map]
    exact table.checkIdentityNat_sound finiteLaw15 (by decide)
  · subst e
    rw [← finiteLaw16_map]
    exact table.checkIdentityNat_sound finiteLaw16 (by decide)
  · subst e
    rw [← finiteLaw17_map]
    exact table.checkIdentityNat_sound finiteLaw17 (by decide)
  · subst e
    rw [← finiteLaw18_map]
    exact table.checkIdentityNat_sound finiteLaw18 (by decide)
  · subst e
    rw [← finiteLaw19_map]
    exact table.checkIdentityNat_sound finiteLaw19 (by decide)
  · subst e
    rw [← finiteLaw20_map]
    exact table.checkIdentityNat_sound finiteLaw20 (by decide)
  · subst e
    rw [← finiteLaw21_map]
    exact table.checkIdentityNat_sound finiteLaw21 (by decide)
  · subst e
    rw [← finiteLaw22_map]
    exact table.checkIdentityNat_sound finiteLaw22 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_10194
-- END S6_10194

-- BEGIN S6_10680
namespace S6_10680

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[5,5,3,4,5,5],[5,5,4,3,5,5],[5,5,5,5,5,5],[1,2,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 3 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c4ebf7e6de8cbcf3dd4680e391e514aa12c32ffff99bbd67309673fd4e2e8e1e"

/-- Exact one-based coordinate maps: `[[1,2,1,1,1,1],[5,5,5,3,3,1],[5,5,5,3,4,1],[1,1,2,6,6,1]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[5,5,5,3,3,1],[5,5,5,3,4,1],[1,1,2,6,6,1]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[5,5,5,3,3,1],[5,5,5,3,4,1],[1,1,2,6,6,1]] := by decide

def coordinateValue (i : Fin 4) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (5 : Fin 6) else (0 : Fin 6)

def coordinateHom (i : Fin 4) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceSemigroup) (table.semigroup.pi (Fin 4)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 1) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw0).map (fun value => (0 : Fin 1))
def finiteLaw1 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw1).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw2 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw2).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw3 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw3).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw4 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw4).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw5 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw5).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw6 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw6).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw7 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw7).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw8 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw8).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw9 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw9).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw10 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw10).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw11 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw11).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw12 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw12).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw13 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw13).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw14 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw14).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw15 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw15).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw16 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw16).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw17 : Identity (Fin 2) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw17).map (fun value => if value = 0 then (0 : Fin 2) else (1 : Fin 2))
def finiteLaw18 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw18).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw19 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw19).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw20 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw20).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw21 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw21).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))
def finiteLaw22 : Identity (Fin 3) :=
  (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw22).map (fun value => if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3))

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw0 := by decide
theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw1 := by decide
theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw2 := by decide
theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw3 := by decide
theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw4 := by decide
theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw5 := by decide
theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw6 := by decide
theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw7 := by decide
theorem finiteLaw8_map :
    finiteLaw8.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw8 := by decide
theorem finiteLaw9_map :
    finiteLaw9.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw9 := by decide
theorem finiteLaw10_map :
    finiteLaw10.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw10 := by decide
theorem finiteLaw11_map :
    finiteLaw11.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw11 := by decide
theorem finiteLaw12_map :
    finiteLaw12.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw12 := by decide
theorem finiteLaw13_map :
    finiteLaw13.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw13 := by decide
theorem finiteLaw14_map :
    finiteLaw14.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw14 := by decide
theorem finiteLaw15_map :
    finiteLaw15.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw15 := by decide
theorem finiteLaw16_map :
    finiteLaw16.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw16 := by decide
theorem finiteLaw17_map :
    finiteLaw17.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw17 := by decide
theorem finiteLaw18_map :
    finiteLaw18.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw18 := by decide
theorem finiteLaw19_map :
    finiteLaw19.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw19 := by decide
theorem finiteLaw20_map :
    finiteLaw20.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw20 := by decide
theorem finiteLaw21_map :
    finiteLaw21.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw21 := by decide
theorem finiteLaw22_map :
    finiteLaw22.map Fin.val = SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceLaw22 := by decide

set_option maxHeartbeats 2000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
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
  · subst e
    rw [← finiteLaw10_map]
    exact table.checkIdentityNat_sound finiteLaw10 (by decide)
  · subst e
    rw [← finiteLaw11_map]
    exact table.checkIdentityNat_sound finiteLaw11 (by decide)
  · subst e
    rw [← finiteLaw12_map]
    exact table.checkIdentityNat_sound finiteLaw12 (by decide)
  · subst e
    rw [← finiteLaw13_map]
    exact table.checkIdentityNat_sound finiteLaw13 (by decide)
  · subst e
    rw [← finiteLaw14_map]
    exact table.checkIdentityNat_sound finiteLaw14 (by decide)
  · subst e
    rw [← finiteLaw15_map]
    exact table.checkIdentityNat_sound finiteLaw15 (by decide)
  · subst e
    rw [← finiteLaw16_map]
    exact table.checkIdentityNat_sound finiteLaw16 (by decide)
  · subst e
    rw [← finiteLaw17_map]
    exact table.checkIdentityNat_sound finiteLaw17 (by decide)
  · subst e
    rw [← finiteLaw18_map]
    exact table.checkIdentityNat_sound finiteLaw18 (by decide)
  · subst e
    rw [← finiteLaw19_map]
    exact table.checkIdentityNat_sound finiteLaw19 (by decide)
  · subst e
    rw [← finiteLaw20_map]
    exact table.checkIdentityNat_sound finiteLaw20 (by decide)
  · subst e
    rw [← finiteLaw21_map]
    exact table.checkIdentityNat_sound finiteLaw21 (by decide)
  · subst e
    rw [← finiteLaw22_map]
    exact table.checkIdentityNat_sound finiteLaw22 (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.sourceBasis)) :=
  representative_basis.oppositeReversed

end S6_10680
-- END S6_10680

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3.S6_5954_Ad4b303415746_Part02

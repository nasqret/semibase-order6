import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.Profile15Completeness
import SemigroupBasis.TransferPower

/-! Seven literal section-A tables, their actual B16 endpoints and literal
opposites. Four siblings use separating hom families. S6_8862 and S6_9008
instead use nine- and thirteen-element subpower quotients. Every finite
multiplication, injection and section equation is checked in Lean. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.ClassEndpoints

open SemigroupBasis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

namespace S6_8862

/-- Exact one-based catalogue table SHA256: 29fc1fcb3be856fe5023caa47dba2b0781daee615118fadc50be03978b793076. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0) else if b = 1 then (0) else if b = 2 then (2) else if b = 3 then (0) else if b = 4 then (0) else 0) else if a = 1 then (if b = 0 then (0) else if b = 1 then (0) else if b = 2 then (2) else if b = 3 then (0) else if b = 4 then (0) else 1) else if a = 2 then (if b = 0 then (2) else if b = 1 then (2) else if b = 2 then (0) else if b = 3 then (2) else if b = 4 then (2) else 2) else if a = 3 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (2) else if b = 3 then (3) else if b = 4 then (3) else 3) else if a = 4 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (2) else if b = 3 then (4) else if b = 4 then (4) else 4) else if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (2) else if b = 3 then (3) else if b = 4 then (4) else 5

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1, 1, 3, 1, 1, 1], [1, 1, 3, 1, 1, 2], [3, 3, 1, 3, 3, 3], [1, 2, 3, 4, 4, 4], [1, 2, 3, 5, 5, 5], [1, 2, 3, 4, 5, 6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) =
      catalogueRows := by decide

theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

def auxiliaryMul (a b : Fin 9) : Fin 9 :=
  if a = 0 then (if b = 0 then (4) else if b = 1 then (5) else if b = 2 then (4) else if b = 3 then (0) else if b = 4 then (4) else if b = 5 then (5) else if b = 6 then (5) else if b = 7 then (4) else 5) else if a = 1 then (if b = 0 then (6) else if b = 1 then (7) else if b = 2 then (5) else if b = 3 then (1) else if b = 4 then (5) else if b = 5 then (4) else if b = 6 then (0) else if b = 7 then (1) else 4) else if a = 2 then (if b = 0 then (2) else if b = 1 then (8) else if b = 2 then (2) else if b = 3 then (2) else if b = 4 then (2) else if b = 5 then (8) else if b = 6 then (8) else if b = 7 then (2) else 8) else if a = 3 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (2) else if b = 3 then (3) else if b = 4 then (4) else if b = 5 then (5) else if b = 6 then (6) else if b = 7 then (7) else 8) else if a = 4 then (if b = 0 then (4) else if b = 1 then (5) else if b = 2 then (4) else if b = 3 then (4) else if b = 4 then (4) else if b = 5 then (5) else if b = 6 then (5) else if b = 7 then (4) else 5) else if a = 5 then (if b = 0 then (5) else if b = 1 then (4) else if b = 2 then (5) else if b = 3 then (5) else if b = 4 then (5) else if b = 5 then (4) else if b = 6 then (4) else if b = 7 then (5) else 4) else if a = 6 then (if b = 0 then (5) else if b = 1 then (4) else if b = 2 then (5) else if b = 3 then (6) else if b = 4 then (5) else if b = 5 then (4) else if b = 6 then (4) else if b = 7 then (5) else 4) else if a = 7 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (4) else if b = 3 then (7) else if b = 4 then (4) else if b = 5 then (5) else if b = 6 then (6) else if b = 7 then (7) else 5) else if b = 0 then (8) else if b = 1 then (2) else if b = 2 then (8) else if b = 3 then (8) else if b = 4 then (8) else if b = 5 then (2) else if b = 6 then (2) else if b = 7 then (8) else 2

def coordinate (a : Fin 9) (i : Fin 3) : Fin 6 :=
  if a = 0 then (if i = 0 then (1) else if i = 1 then (3) else 0) else if a = 1 then (if i = 0 then (3) else if i = 1 then (3) else 2) else if a = 2 then (if i = 0 then (0) else if i = 1 then (4) else 0) else if a = 3 then (if i = 0 then (5) else if i = 1 then (5) else 0) else if a = 4 then (if i = 0 then (0) else if i = 1 then (3) else 0) else if a = 5 then (if i = 0 then (0) else if i = 1 then (3) else 2) else if a = 6 then (if i = 0 then (1) else if i = 1 then (3) else 2) else if a = 7 then (if i = 0 then (3) else if i = 1 then (3) else 0) else if i = 0 then (0) else if i = 1 then (4) else 2

theorem coordinate_mul : ∀ (a b : Fin 9) (i : Fin 3),
    coordinate (auxiliaryMul a b) i = mul (coordinate a i) (coordinate b i) := by decide

theorem coordinate_injective : ∀ a b : Fin 9,
    (∀ i : Fin 3, coordinate a i = coordinate b i) → a = b := by decide

def auxiliaryTable : FiniteTable where
  order := 9
  mul := auxiliaryMul
  assoc := by
    intro a b c
    apply coordinate_injective
    intro i
    simp only [coordinate_mul]
    exact table.semigroup.assoc (coordinate a i) (coordinate b i) (coordinate c i)

def subEmbedding : Embedding auxiliaryTable.semigroup (table.semigroup.pi (Fin 3)) where
  toFun := coordinate
  map_mul := by
    intro a b
    funext i
    exact coordinate_mul a b i
  injective := by
    intro a b equal
    apply coordinate_injective
    intro i
    exact congrFun equal i

def quotientMap (a : Fin 9) : Fin 6 :=
  if a = 0 then (1) else if a = 1 then (3) else if a = 2 then (4) else if a = 3 then (5) else if a = 4 then (0) else if a = 5 then (0) else if a = 6 then (1) else if a = 7 then (2) else 4

def quotientSection (a : Fin 6) : Fin 9 :=
  if a = 0 then (4) else if a = 1 then (0) else if a = 2 then (7) else if a = 3 then (1) else if a = 4 then (2) else 3

def quotient : SplitSurjection auxiliaryTable.semigroup Representative.table.semigroup where
  toFun := quotientMap
  map_mul := by decide
  preimage := quotientSection
  right_inverse := by decide

theorem basisFor : BasisFor table.semigroup basis :=
  Representative.basisFor.inheritAlongPowerDivisor subEmbedding quotient models

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_8862

namespace S6_9008

/-- Exact one-based catalogue table SHA256: c162745631c2221b451d80b80f52cf63a5ccd0dd6570ccc7e5dfbc7e0acaa509. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (1) else if b = 3 then (0) else if b = 4 then (0) else 0) else if a = 1 then (if b = 0 then (1) else if b = 1 then (0) else if b = 2 then (0) else if b = 3 then (1) else if b = 4 then (1) else 1) else if a = 2 then (if b = 0 then (1) else if b = 1 then (0) else if b = 2 then (0) else if b = 3 then (1) else if b = 4 then (1) else 2) else if a = 3 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (2) else if b = 3 then (3) else if b = 4 then (3) else 3) else if a = 4 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (2) else if b = 3 then (4) else if b = 4 then (4) else 4) else if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (2) else if b = 3 then (3) else if b = 4 then (4) else 5

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1, 2, 2, 1, 1, 1], [2, 1, 1, 2, 2, 2], [2, 1, 1, 2, 2, 3], [1, 2, 3, 4, 4, 4], [1, 2, 3, 5, 5, 5], [1, 2, 3, 4, 5, 6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) =
      catalogueRows := by decide

theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

def auxiliaryMul (a b : Fin 13) : Fin 13 :=
  if a = 0 then (if b = 0 then (4) else if b = 1 then (5) else if b = 2 then (6) else if b = 3 then (0) else if b = 4 then (6) else if b = 5 then (9) else if b = 6 then (4) else if b = 7 then (9) else if b = 8 then (6) else if b = 9 then (5) else if b = 10 then (4) else if b = 11 then (5) else 9) else if a = 1 then (if b = 0 then (7) else if b = 1 then (8) else if b = 2 then (9) else if b = 3 then (1) else if b = 4 then (9) else if b = 5 then (6) else if b = 6 then (5) else if b = 7 then (0) else if b = 8 then (1) else if b = 9 then (4) else if b = 10 then (5) else if b = 11 then (4) else 6) else if a = 2 then (if b = 0 then (10) else if b = 1 then (11) else if b = 2 then (2) else if b = 3 then (2) else if b = 4 then (2) else if b = 5 then (12) else if b = 6 then (10) else if b = 7 then (12) else if b = 8 then (2) else if b = 9 then (11) else if b = 10 then (10) else if b = 11 then (11) else 12) else if a = 3 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (2) else if b = 3 then (3) else if b = 4 then (4) else if b = 5 then (5) else if b = 6 then (6) else if b = 7 then (7) else if b = 8 then (8) else if b = 9 then (9) else if b = 10 then (10) else if b = 11 then (11) else 12) else if a = 4 then (if b = 0 then (6) else if b = 1 then (9) else if b = 2 then (4) else if b = 3 then (4) else if b = 4 then (4) else if b = 5 then (5) else if b = 6 then (6) else if b = 7 then (5) else if b = 8 then (4) else if b = 9 then (9) else if b = 10 then (6) else if b = 11 then (9) else 5) else if a = 5 then (if b = 0 then (9) else if b = 1 then (6) else if b = 2 then (5) else if b = 3 then (5) else if b = 4 then (5) else if b = 5 then (4) else if b = 6 then (9) else if b = 7 then (4) else if b = 8 then (5) else if b = 9 then (6) else if b = 10 then (9) else if b = 11 then (6) else 4) else if a = 6 then (if b = 0 then (4) else if b = 1 then (5) else if b = 2 then (6) else if b = 3 then (6) else if b = 4 then (6) else if b = 5 then (9) else if b = 6 then (4) else if b = 7 then (9) else if b = 8 then (6) else if b = 9 then (5) else if b = 10 then (4) else if b = 11 then (5) else 9) else if a = 7 then (if b = 0 then (9) else if b = 1 then (6) else if b = 2 then (5) else if b = 3 then (7) else if b = 4 then (5) else if b = 5 then (4) else if b = 6 then (9) else if b = 7 then (4) else if b = 8 then (5) else if b = 9 then (6) else if b = 10 then (9) else if b = 11 then (6) else 4) else if a = 8 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (4) else if b = 3 then (8) else if b = 4 then (4) else if b = 5 then (5) else if b = 6 then (6) else if b = 7 then (7) else if b = 8 then (8) else if b = 9 then (9) else if b = 10 then (6) else if b = 11 then (9) else 5) else if a = 9 then (if b = 0 then (5) else if b = 1 then (4) else if b = 2 then (9) else if b = 3 then (9) else if b = 4 then (9) else if b = 5 then (6) else if b = 6 then (5) else if b = 7 then (6) else if b = 8 then (9) else if b = 9 then (4) else if b = 10 then (5) else if b = 11 then (4) else 6) else if a = 10 then (if b = 0 then (2) else if b = 1 then (12) else if b = 2 then (10) else if b = 3 then (10) else if b = 4 then (10) else if b = 5 then (11) else if b = 6 then (2) else if b = 7 then (11) else if b = 8 then (10) else if b = 9 then (12) else if b = 10 then (2) else if b = 11 then (12) else 11) else if a = 11 then (if b = 0 then (12) else if b = 1 then (2) else if b = 2 then (11) else if b = 3 then (11) else if b = 4 then (11) else if b = 5 then (10) else if b = 6 then (12) else if b = 7 then (10) else if b = 8 then (11) else if b = 9 then (2) else if b = 10 then (12) else if b = 11 then (2) else 10) else if b = 0 then (11) else if b = 1 then (10) else if b = 2 then (12) else if b = 3 then (12) else if b = 4 then (12) else if b = 5 then (2) else if b = 6 then (11) else if b = 7 then (2) else if b = 8 then (12) else if b = 9 then (10) else if b = 10 then (11) else if b = 11 then (10) else 2

def coordinate (a : Fin 13) (i : Fin 4) : Fin 6 :=
  if a = 0 then (if i = 0 then (0) else if i = 1 then (3) else if i = 2 then (0) else 2) else if a = 1 then (if i = 0 then (3) else if i = 1 then (3) else if i = 2 then (1) else 3) else if a = 2 then (if i = 0 then (0) else if i = 1 then (4) else if i = 2 then (0) else 0) else if a = 3 then (if i = 0 then (5) else if i = 1 then (5) else if i = 2 then (0) else 5) else if a = 4 then (if i = 0 then (0) else if i = 1 then (3) else if i = 2 then (0) else 0) else if a = 5 then (if i = 0 then (0) else if i = 1 then (3) else if i = 2 then (1) else 1) else if a = 6 then (if i = 0 then (0) else if i = 1 then (3) else if i = 2 then (0) else 1) else if a = 7 then (if i = 0 then (0) else if i = 1 then (3) else if i = 2 then (1) else 2) else if a = 8 then (if i = 0 then (3) else if i = 1 then (3) else if i = 2 then (0) else 3) else if a = 9 then (if i = 0 then (0) else if i = 1 then (3) else if i = 2 then (1) else 0) else if a = 10 then (if i = 0 then (0) else if i = 1 then (4) else if i = 2 then (0) else 1) else if a = 11 then (if i = 0 then (0) else if i = 1 then (4) else if i = 2 then (1) else 0) else if i = 0 then (0) else if i = 1 then (4) else if i = 2 then (1) else 1

theorem coordinate_mul : ∀ (a b : Fin 13) (i : Fin 4),
    coordinate (auxiliaryMul a b) i = mul (coordinate a i) (coordinate b i) := by decide

theorem coordinate_injective : ∀ a b : Fin 13,
    (∀ i : Fin 4, coordinate a i = coordinate b i) → a = b := by decide

def auxiliaryTable : FiniteTable where
  order := 13
  mul := auxiliaryMul
  assoc := by
    intro a b c
    apply coordinate_injective
    intro i
    simp only [coordinate_mul]
    exact table.semigroup.assoc (coordinate a i) (coordinate b i) (coordinate c i)

def subEmbedding : Embedding auxiliaryTable.semigroup (table.semigroup.pi (Fin 4)) where
  toFun := coordinate
  map_mul := by
    intro a b
    funext i
    exact coordinate_mul a b i
  injective := by
    intro a b equal
    apply coordinate_injective
    intro i
    exact congrFun equal i

def quotientMap (a : Fin 13) : Fin 6 :=
  if a = 0 then (1) else if a = 1 then (3) else if a = 2 then (4) else if a = 3 then (5) else if a = 4 then (0) else if a = 5 then (0) else if a = 6 then (0) else if a = 7 then (1) else if a = 8 then (2) else if a = 9 then (0) else if a = 10 then (4) else if a = 11 then (4) else 4

def quotientSection (a : Fin 6) : Fin 13 :=
  if a = 0 then (4) else if a = 1 then (0) else if a = 2 then (8) else if a = 3 then (1) else if a = 4 then (2) else 3

def quotient : SplitSurjection auxiliaryTable.semigroup Representative.table.semigroup where
  toFun := quotientMap
  map_mul := by decide
  preimage := quotientSection
  right_inverse := by decide

theorem basisFor : BasisFor table.semigroup basis :=
  Representative.basisFor.inheritAlongPowerDivisor subEmbedding quotient models

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_9008

namespace S6_10960

abbrev table : FiniteTable := Representative.table

theorem models : Models table.semigroup basis := Representative.models

theorem basisFor : BasisFor table.semigroup basis := Representative.basisFor

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  Representative.basisForOpposite

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  basisForOpposite.1

end S6_10960

namespace S6_10973

/-- Exact one-based catalogue table SHA256: 09d1a74b9cc8302a11564d93e82d885ceebab89dbe5c9b3fc459471ce231d3fe. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0) else if b = 1 then (0) else if b = 2 then (0) else if b = 3 then (0) else if b = 4 then (0) else 0) else if a = 1 then (if b = 0 then (0) else if b = 1 then (0) else if b = 2 then (0) else if b = 3 then (0) else if b = 4 then (0) else 1) else if a = 2 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (2) else if b = 3 then (3) else if b = 4 then (4) else 2) else if a = 3 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (3) else if b = 3 then (2) else if b = 4 then (4) else 3) else if a = 4 then (if b = 0 then (4) else if b = 1 then (4) else if b = 2 then (4) else if b = 3 then (4) else if b = 4 then (4) else 4) else if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (2) else if b = 3 then (3) else if b = 4 then (4) else 5

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 2], [1, 2, 3, 4, 5, 3], [1, 2, 4, 3, 5, 4], [5, 5, 5, 5, 5, 5], [1, 2, 3, 4, 5, 6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) =
      catalogueRows := by decide

theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

def rootHom0Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0) else if a = 1 then (1) else if a = 2 then (2) else if a = 3 then (3) else if a = 4 then (0) else 5

def rootHom0 : Hom Representative.table.semigroup table.semigroup where
  toFun := rootHom0Map
  map_mul := by decide

def rootHom1Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0) else if a = 1 then (0) else if a = 2 then (0) else if a = 3 then (0) else if a = 4 then (4) else 2

def rootHom1 : Hom Representative.table.semigroup table.semigroup where
  toFun := rootHom1Map
  map_mul := by decide

def family (i : Fin 2) : Hom Representative.table.semigroup table.semigroup :=
  if i = 0 then (rootHom0) else rootHom1

theorem family_separates : ∀ a b : Fin 6,
    (∀ i : Fin 2, (family i).toFun a = (family i).toFun b) → a = b := by decide

def rootPowerEmbedding : Embedding Representative.table.semigroup
    (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms family family_separates

theorem basisFor : BasisFor table.semigroup basis :=
  Representative.basisFor.inheritAlongPowerEmbedding rootPowerEmbedding models

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_10973

namespace S6_11386

/-- Exact one-based catalogue table SHA256: 86aec3e66ddafd014aaaaa16ed584c61bb174f0e0f05dc7d3197baae080b294d. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0) else if b = 1 then (0) else if b = 2 then (0) else if b = 3 then (0) else if b = 4 then (0) else 0) else if a = 1 then (if b = 0 then (0) else if b = 1 then (0) else if b = 2 then (1) else if b = 3 then (1) else if b = 4 then (0) else 0) else if a = 2 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (2) else if b = 3 then (3) else if b = 4 then (4) else 5) else if a = 3 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (3) else if b = 3 then (2) else if b = 4 then (4) else 5) else if a = 4 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (4) else if b = 3 then (4) else if b = 4 then (4) else 0) else if b = 0 then (5) else if b = 1 then (5) else if b = 2 then (5) else if b = 3 then (5) else if b = 4 then (5) else 5

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1], [1, 1, 2, 2, 1, 1], [1, 2, 3, 4, 5, 6], [1, 2, 4, 3, 5, 6], [1, 2, 5, 5, 5, 1], [6, 6, 6, 6, 6, 6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) =
      catalogueRows := by decide

theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

def rootHom0Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0) else if a = 1 then (1) else if a = 2 then (4) else if a = 3 then (4) else if a = 4 then (5) else 2

def rootHom0 : Hom Representative.table.semigroup table.semigroup where
  toFun := rootHom0Map
  map_mul := by decide

def rootHom1Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0) else if a = 1 then (0) else if a = 2 then (2) else if a = 3 then (3) else if a = 4 then (0) else 2

def rootHom1 : Hom Representative.table.semigroup table.semigroup where
  toFun := rootHom1Map
  map_mul := by decide

def family (i : Fin 2) : Hom Representative.table.semigroup table.semigroup :=
  if i = 0 then (rootHom0) else rootHom1

theorem family_separates : ∀ a b : Fin 6,
    (∀ i : Fin 2, (family i).toFun a = (family i).toFun b) → a = b := by decide

def rootPowerEmbedding : Embedding Representative.table.semigroup
    (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms family family_separates

theorem basisFor : BasisFor table.semigroup basis :=
  Representative.basisFor.inheritAlongPowerEmbedding rootPowerEmbedding models

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_11386

namespace S6_11388

/-- Exact one-based catalogue table SHA256: 97be9f3df010373a6e66134fbf2162a1dbcbc4aa262630479433a9d047650459. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0) else if b = 1 then (0) else if b = 2 then (0) else if b = 3 then (0) else if b = 4 then (0) else 0) else if a = 1 then (if b = 0 then (0) else if b = 1 then (0) else if b = 2 then (1) else if b = 3 then (1) else if b = 4 then (0) else 0) else if a = 2 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (2) else if b = 3 then (3) else if b = 4 then (4) else 5) else if a = 3 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (3) else if b = 3 then (2) else if b = 4 then (4) else 5) else if a = 4 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (4) else if b = 3 then (4) else if b = 4 then (4) else 4) else if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (5) else if b = 3 then (5) else if b = 4 then (5) else 5

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1], [1, 1, 2, 2, 1, 1], [1, 2, 3, 4, 5, 6], [1, 2, 4, 3, 5, 6], [1, 2, 5, 5, 5, 5], [1, 2, 6, 6, 6, 6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) =
      catalogueRows := by decide

theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

def rootHom0Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0) else if a = 1 then (1) else if a = 2 then (4) else if a = 3 then (4) else if a = 4 then (0) else 2

def rootHom0 : Hom Representative.table.semigroup table.semigroup where
  toFun := rootHom0Map
  map_mul := by decide

def rootHom1Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0) else if a = 1 then (0) else if a = 2 then (2) else if a = 3 then (3) else if a = 4 then (0) else 2

def rootHom1 : Hom Representative.table.semigroup table.semigroup where
  toFun := rootHom1Map
  map_mul := by decide

def rootHom2Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (4) else if a = 1 then (4) else if a = 2 then (4) else if a = 3 then (4) else if a = 4 then (5) else 2

def rootHom2 : Hom Representative.table.semigroup table.semigroup where
  toFun := rootHom2Map
  map_mul := by decide

def family (i : Fin 3) : Hom Representative.table.semigroup table.semigroup :=
  if i = 0 then (rootHom0) else if i = 1 then (rootHom1) else rootHom2

theorem family_separates : ∀ a b : Fin 6,
    (∀ i : Fin 3, (family i).toFun a = (family i).toFun b) → a = b := by decide

def rootPowerEmbedding : Embedding Representative.table.semigroup
    (table.semigroup.pi (Fin 3)) :=
  Embedding.ofSeparatingHoms family family_separates

theorem basisFor : BasisFor table.semigroup basis :=
  Representative.basisFor.inheritAlongPowerEmbedding rootPowerEmbedding models

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_11388

namespace S6_11391

/-- Exact one-based catalogue table SHA256: 0d4484e1b4faf1b61f6ef9b336d6af0e72bc2c237f8652b7d7d1c20dd9928b44. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0) else if b = 1 then (0) else if b = 2 then (0) else if b = 3 then (0) else if b = 4 then (0) else 0) else if a = 1 then (if b = 0 then (0) else if b = 1 then (0) else if b = 2 then (1) else if b = 3 then (1) else if b = 4 then (0) else 0) else if a = 2 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (2) else if b = 3 then (3) else if b = 4 then (4) else 5) else if a = 3 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (3) else if b = 3 then (2) else if b = 4 then (4) else 5) else if a = 4 then (if b = 0 then (0) else if b = 1 then (1) else if b = 2 then (4) else if b = 3 then (4) else if b = 4 then (4) else 5) else if b = 0 then (5) else if b = 1 then (5) else if b = 2 then (5) else if b = 3 then (5) else if b = 4 then (5) else 5

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1], [1, 1, 2, 2, 1, 1], [1, 2, 3, 4, 5, 6], [1, 2, 4, 3, 5, 6], [1, 2, 5, 5, 5, 6], [6, 6, 6, 6, 6, 6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) =
      catalogueRows := by decide

theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

def rootHom0Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0) else if a = 1 then (1) else if a = 2 then (4) else if a = 3 then (4) else if a = 4 then (0) else 2

def rootHom0 : Hom Representative.table.semigroup table.semigroup where
  toFun := rootHom0Map
  map_mul := by decide

def rootHom1Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0) else if a = 1 then (0) else if a = 2 then (0) else if a = 3 then (0) else if a = 4 then (5) else 2

def rootHom1 : Hom Representative.table.semigroup table.semigroup where
  toFun := rootHom1Map
  map_mul := by decide

def rootHom2Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0) else if a = 1 then (0) else if a = 2 then (2) else if a = 3 then (3) else if a = 4 then (0) else 2

def rootHom2 : Hom Representative.table.semigroup table.semigroup where
  toFun := rootHom2Map
  map_mul := by decide

def family (i : Fin 3) : Hom Representative.table.semigroup table.semigroup :=
  if i = 0 then (rootHom0) else if i = 1 then (rootHom1) else rootHom2

theorem family_separates : ∀ a b : Fin 6,
    (∀ i : Fin 3, (family i).toFun a = (family i).toFun b) → a = b := by decide

def rootPowerEmbedding : Embedding Representative.table.semigroup
    (table.semigroup.pi (Fin 3)) :=
  Embedding.ofSeparatingHoms family family_separates

theorem basisFor : BasisFor table.semigroup basis :=
  Representative.basisFor.inheritAlongPowerEmbedding rootPowerEmbedding models

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_11391

end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.ClassEndpoints

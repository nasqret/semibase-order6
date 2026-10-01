import SemigroupBasis.CoRoots.Order6Day13.S1193.S1193Presentation
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.Subdirect

/-! The literal S6_1193 table is a subdirect product of the opposites of
S3_6 and S5_110. All multiplication, section and separation checks are finite.
No unit or homomorphic section is assumed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day13.S1193

open SemigroupBasis

def leftTable : FiniteTable where
  order := 3
  mul := fun a b => Generated.S3_6.table.mul b a
  assoc := by decide

def rightTable : FiniteTable where
  order := 5
  mul := fun a b => Generated.Catalogue.S5_110.table.mul b a
  assoc := by decide

theorem leftRows_exact :
    List.ofFn (fun a : Fin 3 => List.ofFn (fun b : Fin 3 => (leftTable.mul a b).val)) =
      [[0, 0, 0], [0, 0, 1], [0, 0, 2]] := by decide

theorem rightRows_exact :
    List.ofFn (fun a : Fin 5 => List.ofFn (fun b : Fin 5 => (rightTable.mul a b).val)) =
      [[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 2],
       [0, 0, 0, 0, 3], [0, 1, 2, 3, 4]] := by decide

theorem leftStructure_exact :
    leftTable.semigroup = Generated.S3_6.table.semigroup.opposite := rfl

theorem rightStructure_exact :
    rightTable.semigroup = Generated.Catalogue.S5_110.table.semigroup.opposite := rfl

private def toFin3 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem leftModels : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFin3 (by decide)

theorem rightModels : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFin3 (by decide)

namespace S6_1193

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0 else
  if a = 1 then (if b = 5 then 1 else 0) else
  if a = 2 then (if b = 5 then 2 else 0) else
  if a = 3 then (if b = 5 then 3 else 0) else
  if a = 4 then (if b = 2 then 1 else if b = 3 then 1 else if b = 5 then 4 else 0) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else
   if b = 3 then 2 else if b = 4 then 4 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,3],[1,1,1,1,1,4],[1,1,2,2,1,5],[1,2,3,3,5,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) =
      catalogueRows := by decide

theorem oppositeRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 =>
      (table.semigroup.opposite.mul a b).val)) =
      [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2],
       [0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 0, 4], [0, 1, 2, 3, 4, 5]] := by decide

theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFin3 (by decide)

def leftMap (a : Fin 6) : Fin 3 :=
  if a = 3 then 1 else if a = 5 then 2 else 0

def leftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 3 else 5

def leftQuotient : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := leftMap
  map_mul := by decide
  preimage := leftSection
  right_inverse := by intro value; exact by decide +revert

def rightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 3 else
  if a = 3 then 3 else if a = 4 then 2 else 4

def rightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 4 else
  if a = 3 then 2 else 5

def rightQuotient : SplitSurjection table.semigroup rightTable.semigroup where
  toFun := rightMap
  map_mul := by decide
  preimage := rightSection
  right_inverse := by intro value; exact by decide +revert

theorem pair_injective :
    Function.Injective (fun a : Fin 6 => (leftMap a, rightMap a)) := by
  intro a b
  exact by decide +revert

def pair : SubdirectPair table.semigroup leftTable.semigroup rightTable.semigroup where
  left := leftQuotient
  right := rightQuotient
  jointlyInjective := pair_injective

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy leftTable.semigroup ∧ identity.SatisfiedBy rightTable.semigroup :=
  pair.satisfiedBy_iff identity

end S6_1193
end SemigroupBasis.CoRoots.Order6Day13.S1193

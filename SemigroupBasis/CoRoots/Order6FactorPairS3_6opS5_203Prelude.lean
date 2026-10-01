import SemigroupBasis.Generated.S3_6
import SemigroupBasis.CoRoots.S5_203Family
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Order6.FactorPairJoin

/-!
# Workload87: exact raw15 and the two original split-subdirect contracts

The actual left factor is the OPPOSITE of catalogue S3_6, not S3_8 and
not direct S3_6. The exact raw presentation is sound but incomplete;
this finite interface makes no completeness or factor-separation claim.
Its tables and quotient maps come from the original direct17 payloads
for S6_2675 and S6_2677. Historical S1/S3 legacy rank031 is not a proof
authorization: current ownership is S2's msg-0379/msg-0380 family claim.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_203

open SemigroupBasis

def leftTable : FiniteTable where
  order := 3
  mul := fun left right => Generated.S3_6.table.mul right left
  assoc := by decide

abbrev rightTable : FiniteTable := SemigroupBasis.CoRoots.S5_203.table

theorem leftTable_eq_actual_opposite :
    leftTable.semigroup = Generated.S3_6.table.semigroup.opposite := rfl

theorem leftTable_rows_exact :
    List.ofFn (fun (a : Fin 3) => List.ofFn (fun (b : Fin 3) => (leftTable.mul a b).val)) =
      [[0, 0, 0], [0, 0, 1], [0, 0, 2]] := by decide

private def w (head : Nat) (tail : List Nat) : Word Nat := Word.mk head tail

/-- Literal ordered raw15 from both authenticated original payloads. -/
def basis : List (Identity Nat) :=
  [ Identity.mk (w 0 [0, 0])       (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1])    (w 0 [0, 1]),
    Identity.mk (w 0 [0, 1, 0])    (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1, 1]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1, 2]) (w 0 [1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 0, 2, 2]),
    Identity.mk (w 0 [1, 0])       (w 0 [1, 1, 0, 0]),
    Identity.mk (w 0 [1, 0])       (w 1 [0, 1]),
    Identity.mk (w 0 [1, 0, 2])    (w 0 [1, 1, 0, 2]),
    Identity.mk (w 0 [1, 1, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 1, 2, 2]) (w 0 [1, 2, 2]),
    Identity.mk (w 0 [1, 2, 0])    (w 0 [2, 1, 0]),
    Identity.mk (w 0 [1, 2, 1])    (w 0 [1, 2, 2, 1]),
    Identity.mk (w 0 [1, 2, 1])    (w 0 [1, 2, 2, 2]) ]

def displayedBasisSHA256 : String :=
  "fab0229399fbef8c465b98e240d1a537d6dad902c59e31e0bf937c44b99cb5f7"

theorem basis_length : basis.length = 15 := rfl

def toFinThree (letter : Nat) : Fin 3 := ⟨letter % 3, Nat.mod_lt _ (by decide)⟩

theorem leftModels : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)

theorem rightModels : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

def commonLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 2 else 5

def commonRightMap (value : Fin 6) : Fin 5 :=
  if value = 1 then 1
  else if value = 3 then 2
  else if value = 4 then 3
  else if value = 5 then 4
  else 0

def commonRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 3
  else if value = 3 then 4
  else 5

namespace S6_2675

def sourceTableSHA256 : String :=
  "989c1808d540adef8bf4fecb7737bbedec5db1a4f7d2cad52edf57cb5f8eda25"

def mul (left right : Fin 6) : Fin 6 :=
  if left.val < 2 then 0
  else if left = 2 then if right = 5 then 2 else 0
  else if left.val < 5 then if right = 4 then 1 else 0
  else if right = 2 then 0 else if right = 4 then 3 else right

theorem table_rows_exact :
    List.ofFn (fun (a : Fin 6) => List.ofFn (fun (b : Fin 6) => (mul a b).val)) =
      [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0],
       [0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0],
       [0, 0, 0, 0, 1, 0], [0, 1, 0, 3, 3, 5]] := by decide

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def leftMap (value : Fin 6) : Fin 3 :=
  if value = 2 then 1 else if value = 5 then 2 else 0

theorem maps_exact :
    List.ofFn (fun (value : Fin 6) => (leftMap value).val) = [0, 0, 1, 0, 0, 2] ∧
    List.ofFn (fun (value : Fin 6) => (commonRightMap value).val) = [0, 1, 0, 2, 3, 4] := by decide

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := leftMap
  map_mul := by decide
  preimage := commonLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRight : SplitSurjection table.semigroup rightTable.semigroup where
  toFun := commonRightMap
  map_mul := by decide
  preimage := commonRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftTable.semigroup rightTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

theorem models_raw : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

end S6_2675

namespace S6_2677

def sourceTableSHA256 : String :=
  "8d1de1b5edb1996f09a0cec557aea9a8fdadceccbfe25d2bfd2c53a6dae2fe5b"

def mul (left right : Fin 6) : Fin 6 :=
  if left.val < 2 then 0
  else if left = 2 then if right = 5 then 2 else 0
  else if left = 3 then if right = 4 then 1 else 0
  else if left = 4 then if right = 4 then 1 else if right = 5 then 2 else 0
  else if right = 2 then 0 else if right = 4 then 3 else right

theorem table_rows_exact :
    List.ofFn (fun (a : Fin 6) => List.ofFn (fun (b : Fin 6) => (mul a b).val)) =
      [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0],
       [0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0],
       [0, 0, 0, 0, 1, 2], [0, 1, 0, 3, 3, 5]] := by decide

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def leftMap (value : Fin 6) : Fin 3 :=
  if value = 2 ∨ value = 4 then 1 else if value = 5 then 2 else 0

theorem maps_exact :
    List.ofFn (fun (value : Fin 6) => (leftMap value).val) = [0, 0, 1, 0, 1, 2] ∧
    List.ofFn (fun (value : Fin 6) => (commonRightMap value).val) = [0, 1, 0, 2, 3, 4] := by decide

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := leftMap
  map_mul := by decide
  preimage := commonLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRight : SplitSurjection table.semigroup rightTable.semigroup where
  toFun := commonRightMap
  map_mul := by decide
  preimage := commonRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftTable.semigroup rightTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

theorem models_raw : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

end S6_2677

end SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_203

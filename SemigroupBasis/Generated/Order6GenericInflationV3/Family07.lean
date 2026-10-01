import SemigroupBasis.PowerProductizedInflation
import SemigroupBasis.Generated.NormalBandTransfersLayer2

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6GenericInflationV3.Family07

open SemigroupBasis
open SemigroupBasis.PowerProductizedInflation

-- Family signature: d93b898f92628651e29ee68c1dade9b8463c2593359ffdb683d2d1342463ac01
def extra : Nat := 1

def retained : List (Identity Nat) :=
  [{ lhs := { head := 0, tail := [1, 2, 0] }, rhs := { head := 0, tail := [2, 1, 0] } }]

def sourceBasis : List (Identity Nat) :=
  [sourcePowerLaw extra] ++ retained

def targetBasis : List (Identity Nat) :=
  PowerProductizedInflation.basis extra retained

theorem sourceBasis_certificate :
    sourceBasis =
      [{ lhs := { head := 0, tail := [] }, rhs := { head := 0, tail := [0] } },
       { lhs := { head := 0, tail := [1, 2, 0] }, rhs := { head := 0, tail := [2, 1, 0] } }] := by
  decide

theorem targetBasis_certificate :
    targetBasis =
      [{ lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 1] } },
       { lhs := { head := 0, tail := [1, 2, 0] }, rhs := { head := 0, tail := [2, 1, 0] } }] := by
  decide

theorem sourceMembership (identity : Identity Nat) :
    identity ∈ sourceBasis <->
      Or (identity = sourcePowerLaw extra) (identity ∈ retained) := by
  simp [sourceBasis]

theorem retainedProducts :
    forall identity, identity ∈ retained ->
      And (Ne identity.lhs.tail []) (Ne identity.rhs.tail []) := by
  intro identity member
  simp [retained] at member
  subst identity
  decide

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

namespace S6_14023

-- Recovered packet case: 6fb65dd6c8f316e7b17ee7f87ebe36ec8a2554dbcee59bf8ebb267f8e2a60499
-- Target table: 2297a7b48a547a57c9a463b8816fc7eefdb3a145f7edd2739e3217cc95d2a65d
-- Oriented source table: d9c5d557277ae511189dbb0e8a1d9a6741f544a8e2c032643cf111859962103f
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 4 4 right else
    if left = 1 then row6 0 0 0 0 4 4 right else
      if left = 2 then row6 0 0 2 0 4 4 right else
        if left = 3 then row6 3 3 3 3 5 5 right else
          if left = 4 then row6 0 0 0 0 4 4 right else
            row6 3 3 3 3 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 =>
      (table.semigroup.mul left right).val + 1

theorem tableOneBased_certificate :
    tableOneBased =
      [[1, 1, 1, 1, 5, 5],
        [1, 1, 1, 1, 5, 5],
        [1, 1, 3, 1, 5, 5],
        [4, 4, 4, 4, 6, 6],
        [1, 1, 1, 1, 5, 5],
        [4, 4, 4, 4, 6, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (2 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.Generated.Catalogue.S5_1142.table.semigroup) table.semigroup where
  toFun := embeddingValue
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def retractValue (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else
    if value = 1 then (0 : Fin 5) else
      if value = 2 then (1 : Fin 5) else
        if value = 3 then (2 : Fin 5) else
          if value = 4 then (3 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.Generated.Catalogue.S5_1142.table.semigroup) table.semigroup where
  embedding := embedding
  retract := retractValue
  retract_embedding := by
    intro value
    exact by decide +revert
  product_represented := by
    intro left right
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine Exists.intro (1 : Fin 6) ?_
  intro sourceValue
  exact by decide +revert

theorem sourceBasis_eq_catalogue :
    sourceBasis = (SemigroupBasis.Examples.normalBandBasis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.Generated.Catalogue.S5_1142.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.Generated.NormalBandTransfers.S5_1142.representative_basis

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14023

namespace S6_14089

-- Recovered packet case: 0a0a6c4412cdbd229f6a93560094b8a2c61657b9691345d3feea9cd9478fed51
-- Target table: d7d5cf249260a153be97d5dcb586fc00d0fd1fc3f805c0d89d8c9903cc479a2c
-- Oriented source table: d9c5d557277ae511189dbb0e8a1d9a6741f544a8e2c032643cf111859962103f
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 4 4 right else
    if left = 1 then row6 0 0 0 0 4 4 right else
      if left = 2 then row6 2 2 2 2 5 5 right else
        if left = 3 then row6 2 2 2 3 5 5 right else
          if left = 4 then row6 0 0 0 0 4 4 right else
            row6 2 2 2 2 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 =>
      (table.semigroup.mul left right).val + 1

theorem tableOneBased_certificate :
    tableOneBased =
      [[1, 1, 1, 1, 5, 5],
        [1, 1, 1, 1, 5, 5],
        [3, 3, 3, 3, 6, 6],
        [3, 3, 3, 4, 6, 6],
        [1, 1, 1, 1, 5, 5],
        [3, 3, 3, 3, 6, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (2 : Fin 6) else
    if value = 1 then (3 : Fin 6) else
      if value = 2 then (0 : Fin 6) else
        if value = 3 then (5 : Fin 6) else
          (4 : Fin 6)

def embedding : Embedding (SemigroupBasis.Generated.Catalogue.S5_1142.table.semigroup) table.semigroup where
  toFun := embeddingValue
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def retractValue (value : Fin 6) : Fin 5 :=
  if value = 0 then (2 : Fin 5) else
    if value = 1 then (2 : Fin 5) else
      if value = 2 then (0 : Fin 5) else
        if value = 3 then (1 : Fin 5) else
          if value = 4 then (4 : Fin 5) else
            (3 : Fin 5)

def inflation : Inflation (SemigroupBasis.Generated.Catalogue.S5_1142.table.semigroup) table.semigroup where
  embedding := embedding
  retract := retractValue
  retract_embedding := by
    intro value
    exact by decide +revert
  product_represented := by
    intro left right
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine Exists.intro (1 : Fin 6) ?_
  intro sourceValue
  exact by decide +revert

theorem sourceBasis_eq_catalogue :
    sourceBasis = (SemigroupBasis.Examples.normalBandBasis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.Generated.Catalogue.S5_1142.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.Generated.NormalBandTransfers.S5_1142.representative_basis

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14089

namespace S6_14333

-- Recovered packet case: 4d429e77ca949ae0dbfd038f1c0ddb93cbc648e8b834ca210d8d25a24f9887af
-- Target table: f41dc97e7fec9d9e388455b29877c0d8aac3907cff48886d714837598f9cd4c7
-- Oriented source table: d9c5d557277ae511189dbb0e8a1d9a6741f544a8e2c032643cf111859962103f
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 3 3 3 right else
    if left = 1 then row6 0 0 0 3 3 3 right else
      if left = 2 then row6 2 2 2 4 4 4 right else
        if left = 3 then row6 0 0 0 3 3 3 right else
          if left = 4 then row6 2 2 2 4 4 4 right else
            row6 2 2 2 4 4 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 =>
      (table.semigroup.mul left right).val + 1

theorem tableOneBased_certificate :
    tableOneBased =
      [[1, 1, 1, 4, 4, 4],
        [1, 1, 1, 4, 4, 4],
        [3, 3, 3, 5, 5, 5],
        [1, 1, 1, 4, 4, 4],
        [3, 3, 3, 5, 5, 5],
        [3, 3, 3, 5, 5, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (4 : Fin 6) else
    if value = 1 then (5 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (2 : Fin 6) else
          (0 : Fin 6)

def embedding : Embedding (SemigroupBasis.Generated.Catalogue.S5_1142.table.semigroup) table.semigroup where
  toFun := embeddingValue
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def retractValue (value : Fin 6) : Fin 5 :=
  if value = 0 then (4 : Fin 5) else
    if value = 1 then (4 : Fin 5) else
      if value = 2 then (3 : Fin 5) else
        if value = 3 then (2 : Fin 5) else
          if value = 4 then (0 : Fin 5) else
            (1 : Fin 5)

def inflation : Inflation (SemigroupBasis.Generated.Catalogue.S5_1142.table.semigroup) table.semigroup where
  embedding := embedding
  retract := retractValue
  retract_embedding := by
    intro value
    exact by decide +revert
  product_represented := by
    intro left right
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine Exists.intro (1 : Fin 6) ?_
  intro sourceValue
  exact by decide +revert

theorem sourceBasis_eq_catalogue :
    sourceBasis = (SemigroupBasis.Examples.normalBandBasis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.Generated.Catalogue.S5_1142.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.Generated.NormalBandTransfers.S5_1142.representative_basis

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14333

namespace S6_14550

-- Recovered packet case: be2c1c280a44d2c6aeae46e3764293328d043df96146b35528da80a48a046be3
-- Target table: 524ca147869717aef8df916d794c594125b185fb5b4aa51ac50dbe809315fbbd
-- Oriented source table: d9c5d557277ae511189dbb0e8a1d9a6741f544a8e2c032643cf111859962103f
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 2 4 4 right else
    if left = 1 then row6 0 0 2 2 4 4 right else
      if left = 2 then row6 2 2 2 2 4 4 right else
        if left = 3 then row6 3 3 3 3 5 5 right else
          if left = 4 then row6 2 2 2 2 4 4 right else
            row6 3 3 3 3 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 =>
      (table.semigroup.mul left right).val + 1

theorem tableOneBased_certificate :
    tableOneBased =
      [[1, 1, 3, 3, 5, 5],
        [1, 1, 3, 3, 5, 5],
        [3, 3, 3, 3, 5, 5],
        [4, 4, 4, 4, 6, 6],
        [3, 3, 3, 3, 5, 5],
        [4, 4, 4, 4, 6, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (2 : Fin 6) else
    if value = 1 then (0 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.Generated.Catalogue.S5_1142.table.semigroup) table.semigroup where
  toFun := embeddingValue
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def retractValue (value : Fin 6) : Fin 5 :=
  if value = 0 then (1 : Fin 5) else
    if value = 1 then (1 : Fin 5) else
      if value = 2 then (0 : Fin 5) else
        if value = 3 then (2 : Fin 5) else
          if value = 4 then (3 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.Generated.Catalogue.S5_1142.table.semigroup) table.semigroup where
  embedding := embedding
  retract := retractValue
  retract_embedding := by
    intro value
    exact by decide +revert
  product_represented := by
    intro left right
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine Exists.intro (1 : Fin 6) ?_
  intro sourceValue
  exact by decide +revert

theorem sourceBasis_eq_catalogue :
    sourceBasis = (SemigroupBasis.Examples.normalBandBasis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.Generated.Catalogue.S5_1142.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.Generated.NormalBandTransfers.S5_1142.representative_basis

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14550

end SemigroupBasis.Generated.Order6GenericInflationV3.Family07

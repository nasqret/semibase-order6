import SemigroupBasis.PowerProductizedInflation
import SemigroupBasis.CoRoots.S5_505Family

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6GenericInflationV3.Family02

open SemigroupBasis
open SemigroupBasis.PowerProductizedInflation

-- Family signature: 096421d5e3acfe79f6f605a151b78c4084f6d9580f04111130e96b4abfdef3f3
def extra : Nat := 4

def retained : List (Identity Nat) :=
  [{ lhs := { head := 0, tail := [1] }, rhs := { head := 1, tail := [0] } }]

def sourceBasis : List (Identity Nat) :=
  [sourcePowerLaw extra] ++ retained

def targetBasis : List (Identity Nat) :=
  PowerProductizedInflation.basis extra retained

theorem sourceBasis_certificate :
    sourceBasis =
      [{ lhs := { head := 0, tail := [] }, rhs := { head := 0, tail := [0, 0, 0, 0] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 1, tail := [0] } }] := by
  decide

theorem targetBasis_certificate :
    targetBasis =
      [{ lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [0, 0, 0, 0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 0, 1, 0, 1, 0, 1, 0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 1, 1, 1, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 1, tail := [0] } }] := by
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

namespace S6_5324

-- Recovered packet case: c98298831b5587ece63736a4530bde68ba6a8af16b8422900da001119334d76f
-- Target table: 18fe4ea1cff7836d3fddbfe567bceab4e87050402914736877a883a61b7a14ba
-- Oriented source table: a45f43b0faff1fc0474b48b80cef67cf131fc1dc1cd1c4e4c037c0ad97e61952
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 0 3 4 0 right else
    if left = 1 then row6 1 0 1 4 3 1 right else
      if left = 2 then row6 0 1 0 3 4 0 right else
        if left = 3 then row6 3 4 3 1 0 3 right else
          if left = 4 then row6 4 3 4 0 1 4 right else
            row6 0 1 0 3 4 5 right

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
      [[1, 2, 1, 4, 5, 1],
        [2, 1, 2, 5, 4, 2],
        [1, 2, 1, 4, 5, 1],
        [4, 5, 4, 2, 1, 4],
        [5, 4, 5, 1, 2, 5],
        [1, 2, 1, 4, 5, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (1 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_505Family.S5_505.table.semigroup) table.semigroup where
  toFun := embeddingValue
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def retractValue (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else
    if value = 1 then (1 : Fin 5) else
      if value = 2 then (0 : Fin 5) else
        if value = 3 then (2 : Fin 5) else
          if value = 4 then (3 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.CoRoots.S5_505Family.S5_505.table.semigroup) table.semigroup where
  embedding := embedding
  retract := retractValue
  retract_embedding := by
    intro value
    exact by decide +revert
  product_represented := by
    intro left right
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine Exists.intro (2 : Fin 6) ?_
  intro sourceValue
  exact by decide +revert

theorem sourceBasis_eq_catalogue :
    sourceBasis = (SemigroupBasis.CoRoots.S5_505.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_505Family.S5_505.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_505Family.S5_505.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_5324

namespace S6_5327

-- Recovered packet case: 39db4a4294de994ea50d7a025ee4209f4c28519c2040dc1d0bb0bb49c30c5882
-- Target table: af7b94ddcd550c9d1b7469601f864ddbe21da63fa08f8198de392bdca4f29fe7
-- Oriented source table: e240f3d7f193c6895aa58055b85d5e063aad9f50386ab7ac7e21ec144575ad00
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 0 3 4 5 right else
    if left = 1 then row6 1 0 1 4 3 5 right else
      if left = 2 then row6 0 1 0 3 4 5 right else
        if left = 3 then row6 3 4 3 1 0 5 right else
          if left = 4 then row6 4 3 4 0 1 5 right else
            row6 5 5 5 5 5 5 right

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
      [[1, 2, 1, 4, 5, 6],
        [2, 1, 2, 5, 4, 6],
        [1, 2, 1, 4, 5, 6],
        [4, 5, 4, 2, 1, 6],
        [5, 4, 5, 1, 2, 6],
        [6, 6, 6, 6, 6, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (1 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_505Family.S5_506.table.semigroup) table.semigroup where
  toFun := embeddingValue
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def retractValue (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else
    if value = 1 then (1 : Fin 5) else
      if value = 2 then (0 : Fin 5) else
        if value = 3 then (2 : Fin 5) else
          if value = 4 then (3 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.CoRoots.S5_505Family.S5_506.table.semigroup) table.semigroup where
  embedding := embedding
  retract := retractValue
  retract_embedding := by
    intro value
    exact by decide +revert
  product_represented := by
    intro left right
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine Exists.intro (2 : Fin 6) ?_
  intro sourceValue
  exact by decide +revert

theorem sourceBasis_eq_catalogue :
    sourceBasis = (SemigroupBasis.CoRoots.S5_505.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_505Family.S5_506.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_505Family.S5_506.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_5327

namespace S6_5328

-- Recovered packet case: 55181208b74675809bbae74adbc68ec6c2536ce05d3bbb57c110848d3bf35fd7
-- Target table: 135c97b70a87dc37d46ca86b15a88ca80b9874d9f1fa6cab696caff307c0f8bc
-- Oriented source table: a45f43b0faff1fc0474b48b80cef67cf131fc1dc1cd1c4e4c037c0ad97e61952
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 1 3 4 0 right else
    if left = 1 then row6 1 0 0 4 3 1 right else
      if left = 2 then row6 1 0 0 4 3 1 right else
        if left = 3 then row6 3 4 4 1 0 3 right else
          if left = 4 then row6 4 3 3 0 1 4 right else
            row6 0 1 1 3 4 5 right

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
      [[1, 2, 2, 4, 5, 1],
        [2, 1, 1, 5, 4, 2],
        [2, 1, 1, 5, 4, 2],
        [4, 5, 5, 2, 1, 4],
        [5, 4, 4, 1, 2, 5],
        [1, 2, 2, 4, 5, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (1 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_505Family.S5_505.table.semigroup) table.semigroup where
  toFun := embeddingValue
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def retractValue (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else
    if value = 1 then (1 : Fin 5) else
      if value = 2 then (1 : Fin 5) else
        if value = 3 then (2 : Fin 5) else
          if value = 4 then (3 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.CoRoots.S5_505Family.S5_505.table.semigroup) table.semigroup where
  embedding := embedding
  retract := retractValue
  retract_embedding := by
    intro value
    exact by decide +revert
  product_represented := by
    intro left right
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine Exists.intro (2 : Fin 6) ?_
  intro sourceValue
  exact by decide +revert

theorem sourceBasis_eq_catalogue :
    sourceBasis = (SemigroupBasis.CoRoots.S5_505.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_505Family.S5_505.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_505Family.S5_505.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_5328

namespace S6_5331

-- Recovered packet case: 8104f40d3cf5772e9e5996cc957b858e384c1fc125515e64cd7a09a877e999fa
-- Target table: 651fba18359a71c3cf38a3c17a4b1a077701b2a8fe604a970cee35ae566181be
-- Oriented source table: e240f3d7f193c6895aa58055b85d5e063aad9f50386ab7ac7e21ec144575ad00
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 1 3 4 5 right else
    if left = 1 then row6 1 0 0 4 3 5 right else
      if left = 2 then row6 1 0 0 4 3 5 right else
        if left = 3 then row6 3 4 4 1 0 5 right else
          if left = 4 then row6 4 3 3 0 1 5 right else
            row6 5 5 5 5 5 5 right

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
      [[1, 2, 2, 4, 5, 6],
        [2, 1, 1, 5, 4, 6],
        [2, 1, 1, 5, 4, 6],
        [4, 5, 5, 2, 1, 6],
        [5, 4, 4, 1, 2, 6],
        [6, 6, 6, 6, 6, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (1 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_505Family.S5_506.table.semigroup) table.semigroup where
  toFun := embeddingValue
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def retractValue (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else
    if value = 1 then (1 : Fin 5) else
      if value = 2 then (1 : Fin 5) else
        if value = 3 then (2 : Fin 5) else
          if value = 4 then (3 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.CoRoots.S5_505Family.S5_506.table.semigroup) table.semigroup where
  embedding := embedding
  retract := retractValue
  retract_embedding := by
    intro value
    exact by decide +revert
  product_represented := by
    intro left right
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine Exists.intro (2 : Fin 6) ?_
  intro sourceValue
  exact by decide +revert

theorem sourceBasis_eq_catalogue :
    sourceBasis = (SemigroupBasis.CoRoots.S5_505.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_505Family.S5_506.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_505Family.S5_506.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_5331

namespace S6_9335

-- Recovered packet case: e57fa2c78c5947f7dc1b47a90e34c67d817252b11716a921e9849c08b225ef4b
-- Target table: 99067ce84fdc17407bf3e6251222e10322165e04c083b9b872b6004c41947d56
-- Oriented source table: a45f43b0faff1fc0474b48b80cef67cf131fc1dc1cd1c4e4c037c0ad97e61952
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 2 2 4 0 right else
    if left = 1 then row6 1 0 4 4 2 1 right else
      if left = 2 then row6 2 4 1 1 0 2 right else
        if left = 3 then row6 2 4 1 1 0 2 right else
          if left = 4 then row6 4 2 0 0 1 4 right else
            row6 0 1 2 2 4 5 right

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
      [[1, 2, 3, 3, 5, 1],
        [2, 1, 5, 5, 3, 2],
        [3, 5, 2, 2, 1, 3],
        [3, 5, 2, 2, 1, 3],
        [5, 3, 1, 1, 2, 5],
        [1, 2, 3, 3, 5, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (1 : Fin 6) else
      if value = 2 then (2 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_505Family.S5_505.table.semigroup) table.semigroup where
  toFun := embeddingValue
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def retractValue (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else
    if value = 1 then (1 : Fin 5) else
      if value = 2 then (2 : Fin 5) else
        if value = 3 then (2 : Fin 5) else
          if value = 4 then (3 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.CoRoots.S5_505Family.S5_505.table.semigroup) table.semigroup where
  embedding := embedding
  retract := retractValue
  retract_embedding := by
    intro value
    exact by decide +revert
  product_represented := by
    intro left right
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine Exists.intro (3 : Fin 6) ?_
  intro sourceValue
  exact by decide +revert

theorem sourceBasis_eq_catalogue :
    sourceBasis = (SemigroupBasis.CoRoots.S5_505.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_505Family.S5_505.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_505Family.S5_505.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_9335

namespace S6_9338

-- Recovered packet case: 647924a6d402afa55468c88a573eac31a2f1bf577819b6fec26ce4273678b897
-- Target table: 7fa25ac0478b657c73d525e58c524968800898318c1b8af8954781a12680cb40
-- Oriented source table: e240f3d7f193c6895aa58055b85d5e063aad9f50386ab7ac7e21ec144575ad00
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 2 2 4 5 right else
    if left = 1 then row6 1 0 4 4 2 5 right else
      if left = 2 then row6 2 4 1 1 0 5 right else
        if left = 3 then row6 2 4 1 1 0 5 right else
          if left = 4 then row6 4 2 0 0 1 5 right else
            row6 5 5 5 5 5 5 right

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
      [[1, 2, 3, 3, 5, 6],
        [2, 1, 5, 5, 3, 6],
        [3, 5, 2, 2, 1, 6],
        [3, 5, 2, 2, 1, 6],
        [5, 3, 1, 1, 2, 6],
        [6, 6, 6, 6, 6, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (1 : Fin 6) else
      if value = 2 then (2 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_505Family.S5_506.table.semigroup) table.semigroup where
  toFun := embeddingValue
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def retractValue (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else
    if value = 1 then (1 : Fin 5) else
      if value = 2 then (2 : Fin 5) else
        if value = 3 then (2 : Fin 5) else
          if value = 4 then (3 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.CoRoots.S5_505Family.S5_506.table.semigroup) table.semigroup where
  embedding := embedding
  retract := retractValue
  retract_embedding := by
    intro value
    exact by decide +revert
  product_represented := by
    intro left right
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine Exists.intro (3 : Fin 6) ?_
  intro sourceValue
  exact by decide +revert

theorem sourceBasis_eq_catalogue :
    sourceBasis = (SemigroupBasis.CoRoots.S5_505.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_505Family.S5_506.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_505Family.S5_506.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_9338

namespace S6_9400

-- Recovered packet case: 5f7c4366b0df63a30f07ce6000dc30e202350161cd5e4abb0335c450d821ff39
-- Target table: 79c0047ed0c9b048e3082e553b16f8c40d787d1d26525eeb6f429f4cce09ea8e
-- Oriented source table: a45f43b0faff1fc0474b48b80cef67cf131fc1dc1cd1c4e4c037c0ad97e61952
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 2 3 0 0 right else
    if left = 1 then row6 1 0 3 2 1 1 right else
      if left = 2 then row6 2 3 1 0 2 2 right else
        if left = 3 then row6 3 2 0 1 3 3 right else
          if left = 4 then row6 0 1 2 3 4 4 right else
            row6 0 1 2 3 4 4 right

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
      [[1, 2, 3, 4, 1, 1],
        [2, 1, 4, 3, 2, 2],
        [3, 4, 2, 1, 3, 3],
        [4, 3, 1, 2, 4, 4],
        [1, 2, 3, 4, 5, 5],
        [1, 2, 3, 4, 5, 5]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (1 : Fin 6) else
      if value = 2 then (2 : Fin 6) else
        if value = 3 then (3 : Fin 6) else
          (4 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_505Family.S5_505.table.semigroup) table.semigroup where
  toFun := embeddingValue
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def retractValue (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else
    if value = 1 then (1 : Fin 5) else
      if value = 2 then (2 : Fin 5) else
        if value = 3 then (3 : Fin 5) else
          if value = 4 then (4 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.CoRoots.S5_505Family.S5_505.table.semigroup) table.semigroup where
  embedding := embedding
  retract := retractValue
  retract_embedding := by
    intro value
    exact by decide +revert
  product_represented := by
    intro left right
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine Exists.intro (5 : Fin 6) ?_
  intro sourceValue
  exact by decide +revert

theorem sourceBasis_eq_catalogue :
    sourceBasis = (SemigroupBasis.CoRoots.S5_505.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_505Family.S5_505.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_505Family.S5_505.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_9400

namespace S6_9403

-- Recovered packet case: 0c917b1a6def68bdae85952b7348741d8107158f900a41e7c1cd394edb0dac3e
-- Target table: ce5c9c968c109f6f822a62fb3288786815398726d98f6e3cdd8f2e0b151f8dc4
-- Oriented source table: e240f3d7f193c6895aa58055b85d5e063aad9f50386ab7ac7e21ec144575ad00
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 2 3 4 4 right else
    if left = 1 then row6 1 0 3 2 4 4 right else
      if left = 2 then row6 2 3 1 0 4 4 right else
        if left = 3 then row6 3 2 0 1 4 4 right else
          if left = 4 then row6 4 4 4 4 4 4 right else
            row6 4 4 4 4 4 4 right

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
      [[1, 2, 3, 4, 5, 5],
        [2, 1, 4, 3, 5, 5],
        [3, 4, 2, 1, 5, 5],
        [4, 3, 1, 2, 5, 5],
        [5, 5, 5, 5, 5, 5],
        [5, 5, 5, 5, 5, 5]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (1 : Fin 6) else
      if value = 2 then (2 : Fin 6) else
        if value = 3 then (3 : Fin 6) else
          (4 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_505Family.S5_506.table.semigroup) table.semigroup where
  toFun := embeddingValue
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def retractValue (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else
    if value = 1 then (1 : Fin 5) else
      if value = 2 then (2 : Fin 5) else
        if value = 3 then (3 : Fin 5) else
          if value = 4 then (4 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.CoRoots.S5_505Family.S5_506.table.semigroup) table.semigroup where
  embedding := embedding
  retract := retractValue
  retract_embedding := by
    intro value
    exact by decide +revert
  product_represented := by
    intro left right
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine Exists.intro (5 : Fin 6) ?_
  intro sourceValue
  exact by decide +revert

theorem sourceBasis_eq_catalogue :
    sourceBasis = (SemigroupBasis.CoRoots.S5_505.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_505Family.S5_506.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_505Family.S5_506.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_9403

end SemigroupBasis.Generated.Order6GenericInflationV3.Family02

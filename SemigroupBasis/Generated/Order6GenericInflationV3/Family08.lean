import SemigroupBasis.PowerProductizedInflation
import SemigroupBasis.CoRoots.S5_1092Family

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6GenericInflationV3.Family08

open SemigroupBasis
open SemigroupBasis.PowerProductizedInflation

-- Family signature: 479e4454605037e90738338898c0628e61502140f3a20ed9e3d80c65130b7b91
def extra : Nat := 1

def retained : List (Identity Nat) :=
  [{ lhs := { head := 0, tail := [2, 1, 0] }, rhs := { head := 0, tail := [2, 0, 1, 0] } }]

def sourceBasis : List (Identity Nat) :=
  [sourcePowerLaw extra] ++ retained

def targetBasis : List (Identity Nat) :=
  PowerProductizedInflation.basis extra retained

theorem sourceBasis_certificate :
    sourceBasis =
      [{ lhs := { head := 0, tail := [] }, rhs := { head := 0, tail := [0] } },
       { lhs := { head := 0, tail := [2, 1, 0] }, rhs := { head := 0, tail := [2, 0, 1, 0] } }] := by
  decide

theorem targetBasis_certificate :
    targetBasis =
      [{ lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 1] } },
       { lhs := { head := 0, tail := [2, 1, 0] }, rhs := { head := 0, tail := [2, 0, 1, 0] } }] := by
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

namespace S6_14203

-- Recovered packet case: 2395c6ebf930bffffb270c80c1d2d45d0f984373e7cd464fc81b41b31cd23044
-- Target table: e4d069ab963167ad17e42e63028e58add0c41320eb4da913d5dea32c814cc54a
-- Oriented source table: 0c71048fa447a9357845a3dd57d5206caaf78d9cf834f59ab06c6005093d9490
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 4 5 right else
    if left = 1 then row6 0 0 0 0 4 5 right else
      if left = 2 then row6 0 0 2 3 4 5 right else
        if left = 3 then row6 3 3 3 3 4 5 right else
          if left = 4 then row6 4 4 4 4 4 5 right else
            row6 4 4 5 4 4 5 right

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
      [[1, 1, 1, 1, 5, 6],
        [1, 1, 1, 1, 5, 6],
        [1, 1, 3, 4, 5, 6],
        [4, 4, 4, 4, 5, 6],
        [5, 5, 5, 5, 5, 6],
        [5, 5, 6, 5, 5, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (4 : Fin 6) else
    if value = 1 then (0 : Fin 6) else
      if value = 2 then (5 : Fin 6) else
        if value = 3 then (2 : Fin 6) else
          (3 : Fin 6)

def embedding : Embedding (SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup.opposite) table.semigroup where
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
      if value = 2 then (3 : Fin 5) else
        if value = 3 then (4 : Fin 5) else
          if value = 4 then (0 : Fin 5) else
            (2 : Fin 5)

def inflation : Inflation (SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup.opposite) table.semigroup where
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
    sourceBasis = (reversedBasis SemigroupBasis.CoRoots.S5_1092.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup.opposite) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1092Family.S5_1092.basis_complete.oppositeReversed

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14203

namespace S6_14204

-- Recovered packet case: 8969039901b32c88211d77e167d439c9d1fa64aab56884d4eed9a966ac90c816
-- Target table: 3b8392a9857219c88602724492adf8d1db4d124850b46f0c0b643347d2cbd0bb
-- Oriented source table: 441f97a6de573aaa712ac1c6d76c8f392c0666f5b6ff0fe4f92f4d893ca517a2
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 4 5 right else
    if left = 1 then row6 0 0 0 0 4 5 right else
      if left = 2 then row6 0 0 2 3 4 5 right else
        if left = 3 then row6 3 3 3 3 4 5 right else
          if left = 4 then row6 4 4 4 4 4 5 right else
            row6 5 5 5 5 4 5 right

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
      [[1, 1, 1, 1, 5, 6],
        [1, 1, 1, 1, 5, 6],
        [1, 1, 3, 4, 5, 6],
        [4, 4, 4, 4, 5, 6],
        [5, 5, 5, 5, 5, 6],
        [6, 6, 6, 6, 5, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (4 : Fin 6) else
    if value = 1 then (0 : Fin 6) else
      if value = 2 then (2 : Fin 6) else
        if value = 3 then (3 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup.opposite) table.semigroup where
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
      if value = 2 then (2 : Fin 5) else
        if value = 3 then (3 : Fin 5) else
          if value = 4 then (0 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup.opposite) table.semigroup where
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
    sourceBasis = (reversedBasis SemigroupBasis.CoRoots.S5_1092.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup.opposite) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1092Family.S5_1135.basis_complete.oppositeReversed

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14204

end SemigroupBasis.Generated.Order6GenericInflationV3.Family08

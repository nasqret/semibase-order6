import SemigroupBasis.PowerProductizedInflation
import SemigroupBasis.CoRoots.S5_1149

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6GenericInflationV3.Family03

open SemigroupBasis
open SemigroupBasis.PowerProductizedInflation

-- Family signature: fcd5bc714cdd74fce68a73cb97279bab1c7800bf97ef81ae6afa1ee1bdead539
def extra : Nat := 3

def retained : List (Identity Nat) :=
  [{ lhs := { head := 0, tail := [0, 1] }, rhs := { head := 0, tail := [1, 0] } }]

def sourceBasis : List (Identity Nat) :=
  [sourcePowerLaw extra] ++ retained

def targetBasis : List (Identity Nat) :=
  PowerProductizedInflation.basis extra retained

theorem sourceBasis_certificate :
    sourceBasis =
      [{ lhs := { head := 0, tail := [] }, rhs := { head := 0, tail := [0, 0, 0] } },
       { lhs := { head := 0, tail := [0, 1] }, rhs := { head := 0, tail := [1, 0] } }] := by
  decide

theorem targetBasis_certificate :
    targetBasis =
      [{ lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [0, 0, 0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 0, 1, 0, 1, 0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 1, 1, 1] } },
       { lhs := { head := 0, tail := [0, 1] }, rhs := { head := 0, tail := [1, 0] } }] := by
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

namespace S6_14906

-- Recovered packet case: 9beae4ddc1199a36dc5e0f9110671a2be312e99fe825132d190e1d15be0f7bcf
-- Target table: 0b9f52fb2333b6853da2763421a4a385d7ddfdee0faf6075f524a703f29002b6
-- Oriented source table: c1320589ecc73d229511b0036d49a5a5c56e0d2c1a234d3411bc95e4ef77593d
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 2 3 4 5 right else
        if left = 3 then row6 3 3 3 3 3 3 right else
          if left = 4 then row6 0 0 4 3 5 2 right else
            row6 0 0 5 3 2 4 right

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
      [[1, 1, 1, 1, 1, 1],
        [1, 1, 1, 1, 1, 1],
        [1, 1, 3, 4, 5, 6],
        [4, 4, 4, 4, 4, 4],
        [1, 1, 5, 4, 6, 3],
        [1, 1, 6, 4, 3, 5]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (2 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1149.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1149.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1149.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1149.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1149.representative_basis

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14906

namespace S6_14958

-- Recovered packet case: cd4e2310e6f1e7f7c4f5e53250fe80de6a5b99c6dde0c8af678aaa6d15685e0d
-- Target table: b8c7289666e61fafea1b5a9a7a3e2b3982819cee8c5fbe141e87048807489a84
-- Oriented source table: c1320589ecc73d229511b0036d49a5a5c56e0d2c1a234d3411bc95e4ef77593d
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 3 4 5 right else
    if left = 1 then row6 0 0 2 3 4 5 right else
      if left = 2 then row6 2 2 2 2 2 2 right else
        if left = 3 then row6 3 3 3 3 3 3 right else
          if left = 4 then row6 4 4 2 3 5 0 right else
            row6 5 5 2 3 0 4 right

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
      [[1, 1, 3, 4, 5, 6],
        [1, 1, 3, 4, 5, 6],
        [3, 3, 3, 3, 3, 3],
        [4, 4, 4, 4, 4, 4],
        [5, 5, 3, 4, 6, 1],
        [6, 6, 3, 4, 1, 5]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (2 : Fin 6) else
    if value = 1 then (0 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1149.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1149.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1149.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1149.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1149.representative_basis

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14958

namespace S6_15920

-- Recovered packet case: bdc28bcedff0f3869a3cd8ad45cd2f29a913f96ca9abe7570cea3a1cb1700de4
-- Target table: 0ba2efadb579772b6178cddf72ff21d23c70852e32c3db8efe5f3d97c918ab17
-- Oriented source table: c1320589ecc73d229511b0036d49a5a5c56e0d2c1a234d3411bc95e4ef77593d
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 1 2 3 4 4 right else
      if left = 2 then row6 2 2 2 2 2 2 right else
        if left = 3 then row6 0 3 2 4 1 1 right else
          if left = 4 then row6 0 4 2 1 3 3 right else
            row6 0 4 2 1 3 3 right

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
      [[1, 1, 1, 1, 1, 1],
        [1, 2, 3, 4, 5, 5],
        [3, 3, 3, 3, 3, 3],
        [1, 4, 3, 5, 2, 2],
        [1, 5, 3, 2, 4, 4],
        [1, 5, 3, 2, 4, 4]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (1 : Fin 6) else
      if value = 2 then (2 : Fin 6) else
        if value = 3 then (3 : Fin 6) else
          (4 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1149.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1149.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1149.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1149.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1149.representative_basis

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_15920

end SemigroupBasis.Generated.Order6GenericInflationV3.Family03

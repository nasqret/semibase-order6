import SemigroupBasis.PowerProductizedInflation
import SemigroupBasis.CoRoots.S5_1007Family

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6GenericInflationV3.Family01

open SemigroupBasis
open SemigroupBasis.PowerProductizedInflation

-- Family signature: 71409eb339d9d8318bec6bb120941a6241d8690eacb37c626eac9dd26e4a8acb
def extra : Nat := 6

def retained : List (Identity Nat) :=
  [{ lhs := { head := 0, tail := [1] }, rhs := { head := 1, tail := [0] } }]

def sourceBasis : List (Identity Nat) :=
  [sourcePowerLaw extra] ++ retained

def targetBasis : List (Identity Nat) :=
  PowerProductizedInflation.basis extra retained

theorem sourceBasis_certificate :
    sourceBasis =
      [{ lhs := { head := 0, tail := [] }, rhs := { head := 0, tail := [0, 0, 0, 0, 0, 0] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 1, tail := [0] } }] := by
  decide

theorem targetBasis_certificate :
    targetBasis =
      [{ lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [0, 0, 0, 0, 0, 0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 1, 1, 1, 1, 1, 1] } },
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

namespace S6_9112

-- Recovered packet case: 4b39707d88b62cb33d0b7f640ed1593fee573323ce4605a17a27274339badb2f
-- Target table: 0710271918eaca541c247520bc68273a1ef4585fe34237837a58ec6396ed81ae
-- Oriented source table: 4de9384273ca1ad629280f8bdc19a20671988baad07daed6862c43918de3adee
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 0 0 0 right else
    if left = 1 then row6 0 0 2 0 0 0 right else
      if left = 2 then row6 2 2 0 2 2 2 right else
        if left = 3 then row6 0 0 2 3 4 5 right else
          if left = 4 then row6 0 0 2 4 5 3 right else
            row6 0 0 2 5 3 4 right

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
      [[1, 1, 3, 1, 1, 1],
        [1, 1, 3, 1, 1, 1],
        [3, 3, 1, 3, 3, 3],
        [1, 1, 3, 4, 5, 6],
        [1, 1, 3, 5, 6, 4],
        [1, 1, 3, 6, 4, 5]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (2 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1007.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1007Family.S5_1007.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_9112

namespace S6_9115

-- Recovered packet case: 1e50551c1639338099281b7d9afa20fc0e0583e695b3cc903ba24e13c56e69de
-- Target table: c43686dcc49f429434706d897bf4eecb53d0a07eb5df8a99a527684c447ff462
-- Oriented source table: 6a95203d6fb8cae714630d904ae35b509f97f614e98600c7c688f88ffb22de9d
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 3 4 5 right else
    if left = 1 then row6 0 0 2 3 4 5 right else
      if left = 2 then row6 2 2 0 3 4 5 right else
        if left = 3 then row6 3 3 3 3 4 5 right else
          if left = 4 then row6 4 4 4 4 5 3 right else
            row6 5 5 5 5 3 4 right

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
        [3, 3, 1, 4, 5, 6],
        [4, 4, 4, 4, 5, 6],
        [5, 5, 5, 5, 6, 4],
        [6, 6, 6, 6, 4, 5]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (2 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1007.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1007Family.S5_1008.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_9115

namespace S6_9116

-- Recovered packet case: cc159ac44621cbb0521ba60b6600f4f65de29a436c298df0f80d28cd9bac59d4
-- Target table: 50fa98a55d6e4af360387941e81c9508889e3062ea4abafce5a9f519aba565a1
-- Oriented source table: 4de9384273ca1ad629280f8bdc19a20671988baad07daed6862c43918de3adee
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 1 0 0 0 right else
    if left = 1 then row6 1 0 0 1 1 1 right else
      if left = 2 then row6 1 0 0 1 1 1 right else
        if left = 3 then row6 0 1 1 3 4 5 right else
          if left = 4 then row6 0 1 1 4 5 3 right else
            row6 0 1 1 5 3 4 right

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
      [[1, 2, 2, 1, 1, 1],
        [2, 1, 1, 2, 2, 2],
        [2, 1, 1, 2, 2, 2],
        [1, 2, 2, 4, 5, 6],
        [1, 2, 2, 5, 6, 4],
        [1, 2, 2, 6, 4, 5]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (1 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1007.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1007Family.S5_1007.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_9116

namespace S6_9119

-- Recovered packet case: d25954ddd5d3bb5cbc593b6c355749404bc627801e5f61d9cdc067a31a3f3dc7
-- Target table: 4eb299b055f91c06fb8a8fd0329afc9d9f7e5793fa1753b6d8779f149aa5d2e5
-- Oriented source table: 6a95203d6fb8cae714630d904ae35b509f97f614e98600c7c688f88ffb22de9d
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 1 3 4 5 right else
    if left = 1 then row6 1 0 0 3 4 5 right else
      if left = 2 then row6 1 0 0 3 4 5 right else
        if left = 3 then row6 3 3 3 3 4 5 right else
          if left = 4 then row6 4 4 4 4 5 3 right else
            row6 5 5 5 5 3 4 right

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
        [2, 1, 1, 4, 5, 6],
        [2, 1, 1, 4, 5, 6],
        [4, 4, 4, 4, 5, 6],
        [5, 5, 5, 5, 6, 4],
        [6, 6, 6, 6, 4, 5]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (1 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1007.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1007Family.S5_1008.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_9119

namespace S6_11931

-- Recovered packet case: 6ded1bd42de45c14783e110951fbc4978941ab4cef4fd99d0616392a37f991c3
-- Target table: 67b71cef90a7b45b88e00e4bcded829615c7a64adfa346bac67c3e8f4924f9c9
-- Oriented source table: 6a95203d6fb8cae714630d904ae35b509f97f614e98600c7c688f88ffb22de9d
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 4 5 right else
    if left = 1 then row6 0 0 0 0 4 5 right else
      if left = 2 then row6 0 0 2 3 4 5 right else
        if left = 3 then row6 0 0 3 2 4 5 right else
          if left = 4 then row6 4 4 4 4 5 0 right else
            row6 5 5 5 5 0 4 right

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
        [1, 1, 4, 3, 5, 6],
        [5, 5, 5, 5, 6, 1],
        [6, 6, 6, 6, 1, 5]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (2 : Fin 6) else
    if value = 1 then (3 : Fin 6) else
      if value = 2 then (0 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup) table.semigroup where
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
          if value = 4 then (3 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1007.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1007Family.S5_1008.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_11931

namespace S6_11936

-- Recovered packet case: e3222e580295a82ab42582625308620b268a6d9c819ba854166bd496237b8169
-- Target table: af74ae49f54a626ecd729fcbbe4df68577ff9b90dcee880f072eb94af9b5e2fa
-- Oriented source table: 4de9384273ca1ad629280f8bdc19a20671988baad07daed6862c43918de3adee
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 3 4 5 right else
    if left = 1 then row6 0 0 2 3 4 5 right else
      if left = 2 then row6 2 2 2 3 2 2 right else
        if left = 3 then row6 3 3 3 2 3 3 right else
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
        [3, 3, 3, 4, 3, 3],
        [4, 4, 4, 3, 4, 4],
        [5, 5, 3, 4, 6, 1],
        [6, 6, 3, 4, 1, 5]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (2 : Fin 6) else
    if value = 1 then (3 : Fin 6) else
      if value = 2 then (0 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup) table.semigroup where
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
          if value = 4 then (3 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1007.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1007Family.S5_1007.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_11936

namespace S6_14986

-- Recovered packet case: 7d030f3c5c0bba2b692124f65baa30eed8056382ce4dc6b661d2d9e243f96313
-- Target table: ecb59126bfaafd99357cbb0db723954c54cd04b57ce6a565443b69b918031a1e
-- Oriented source table: 4de9384273ca1ad629280f8bdc19a20671988baad07daed6862c43918de3adee
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 0 0 0 0 right else
    if left = 1 then row6 1 0 1 1 1 1 right else
      if left = 2 then row6 0 1 2 3 4 4 right else
        if left = 3 then row6 0 1 3 4 2 2 right else
          if left = 4 then row6 0 1 4 2 3 3 right else
            row6 0 1 4 2 3 3 right

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
      [[1, 2, 1, 1, 1, 1],
        [2, 1, 2, 2, 2, 2],
        [1, 2, 3, 4, 5, 5],
        [1, 2, 4, 5, 3, 3],
        [1, 2, 5, 3, 4, 4],
        [1, 2, 5, 3, 4, 4]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (1 : Fin 6) else
      if value = 2 then (2 : Fin 6) else
        if value = 3 then (3 : Fin 6) else
          (4 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1007.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1007Family.S5_1007.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14986

namespace S6_14987

-- Recovered packet case: 827a3bd6321e0b9d10c37179868e9fc3bbf77c5fc4dbc507df750077fdf46559
-- Target table: 9259b9bca6fc9652b3a06267472ab2a89bddc399a3fe643d5d3b1b7cbc6e4999
-- Oriented source table: 6a95203d6fb8cae714630d904ae35b509f97f614e98600c7c688f88ffb22de9d
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 2 3 4 4 right else
    if left = 1 then row6 1 0 2 3 4 4 right else
      if left = 2 then row6 2 2 2 3 4 4 right else
        if left = 3 then row6 3 3 3 4 2 2 right else
          if left = 4 then row6 4 4 4 2 3 3 right else
            row6 4 4 4 2 3 3 right

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
        [2, 1, 3, 4, 5, 5],
        [3, 3, 3, 4, 5, 5],
        [4, 4, 4, 5, 3, 3],
        [5, 5, 5, 3, 4, 4],
        [5, 5, 5, 3, 4, 4]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (1 : Fin 6) else
      if value = 2 then (2 : Fin 6) else
        if value = 3 then (3 : Fin 6) else
          (4 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1007.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1007Family.S5_1008.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14987

end SemigroupBasis.Generated.Order6GenericInflationV3.Family01

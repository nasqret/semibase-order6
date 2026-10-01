import SemigroupBasis.PowerProductizedInflation
import SemigroupBasis.CoRoots.S5_1146

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6GenericInflationV3.Family04

open SemigroupBasis
open SemigroupBasis.PowerProductizedInflation

-- Family signature: 6bfef55331f4a722a98d1d72d80cf112ccb71c11498762b95443102005d9b705
def extra : Nat := 3

def retained : List (Identity Nat) :=
  [{ lhs := { head := 0, tail := [1, 2] }, rhs := { head := 0, tail := [2, 1] } }]

def sourceBasis : List (Identity Nat) :=
  [sourcePowerLaw extra] ++ retained

def targetBasis : List (Identity Nat) :=
  PowerProductizedInflation.basis extra retained

theorem sourceBasis_certificate :
    sourceBasis =
      [{ lhs := { head := 0, tail := [] }, rhs := { head := 0, tail := [0, 0, 0] } },
       { lhs := { head := 0, tail := [1, 2] }, rhs := { head := 0, tail := [2, 1] } }] := by
  decide

theorem targetBasis_certificate :
    targetBasis =
      [{ lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [0, 0, 0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 0, 1, 0, 1, 0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 1, 1, 1] } },
       { lhs := { head := 0, tail := [1, 2] }, rhs := { head := 0, tail := [2, 1] } }] := by
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

namespace S6_14901

-- Recovered packet case: d3b5bbc24ca3e26d12b4399b51667b499998754b570405b52367cbd2424255fc
-- Target table: 623950e5e713dc2c1669728891c43a593b53d54f62be9a0b5a10902b753e3b87
-- Oriented source table: d4201f78868e998ae873a51bfd4aadbdffc5057a203a3004b788d26fd63a9173
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 2 0 4 5 right else
        if left = 3 then row6 3 3 3 3 3 3 right else
          if left = 4 then row6 0 0 4 0 5 2 right else
            row6 0 0 5 0 2 4 right

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
        [1, 1, 3, 1, 5, 6],
        [4, 4, 4, 4, 4, 4],
        [1, 1, 5, 1, 6, 3],
        [1, 1, 6, 1, 3, 5]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (2 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1146.S5_1146.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1146.S5_1146.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1146.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1146.S5_1146.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1146.S5_1146.representative_basis

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14901

namespace S6_14911

-- Recovered packet case: f298553f2beec729d910870145e160de1ad493d74cba426c3cd7c6e4a5d8edb7
-- Target table: edd3cd31fdebeaf0f3088eca05d52223698ee496629ae195310e3d8ec4fc1a31
-- Oriented source table: d4201f78868e998ae873a51bfd4aadbdffc5057a203a3004b788d26fd63a9173
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 2 2 2 2 2 2 right else
        if left = 3 then row6 2 2 2 3 4 5 right else
          if left = 4 then row6 2 2 2 4 5 3 right else
            row6 2 2 2 5 3 4 right

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
        [3, 3, 3, 3, 3, 3],
        [3, 3, 3, 4, 5, 6],
        [3, 3, 3, 5, 6, 4],
        [3, 3, 3, 6, 4, 5]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (2 : Fin 6) else
    if value = 1 then (3 : Fin 6) else
      if value = 2 then (0 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1146.S5_1146.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1146.S5_1146.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1146.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1146.S5_1146.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1146.S5_1146.representative_basis

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14911

namespace S6_14930

-- Recovered packet case: b0121cca3ce5e4627545267aa0f95f459545dd54cb16a076485d5154b8477ff0
-- Target table: 6f255e9317f89cd4884ba37af9e15113f94b497d48b092790fffb07c8ae33c3f
-- Oriented source table: e8a49abc3547db06a30968eea47aace636d7da69d466b6339b0c58e6bfeba958
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 4 5 right else
    if left = 1 then row6 0 0 0 0 4 5 right else
      if left = 2 then row6 0 0 2 2 4 5 right else
        if left = 3 then row6 0 0 3 3 4 5 right else
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
        [1, 1, 3, 3, 5, 6],
        [1, 1, 4, 4, 5, 6],
        [5, 5, 5, 5, 6, 1],
        [6, 6, 6, 6, 1, 5]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (2 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1146.S5_1152.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1146.S5_1152.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1146.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1146.S5_1152.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1146.S5_1152.representative_basis

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14930

namespace S6_14949

-- Recovered packet case: 4b04e974573e90baf9970cec3a9bd83fb0ed13ed2c8b6f77eea92fb364359b08
-- Target table: 4398a6f91b140a9aa7fa8a6017e0b70b07cc12fd32f17b1e2f84b502317b19fd
-- Oriented source table: e8a49abc3547db06a30968eea47aace636d7da69d466b6339b0c58e6bfeba958
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 3 4 5 right else
    if left = 1 then row6 0 0 0 3 4 5 right else
      if left = 2 then row6 2 2 2 3 4 5 right else
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
      [[1, 1, 1, 4, 5, 6],
        [1, 1, 1, 4, 5, 6],
        [3, 3, 3, 4, 5, 6],
        [4, 4, 4, 4, 5, 6],
        [5, 5, 5, 5, 6, 4],
        [6, 6, 6, 6, 4, 5]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (3 : Fin 6) else
    if value = 1 then (0 : Fin 6) else
      if value = 2 then (2 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1146.S5_1152.table.semigroup) table.semigroup where
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
        if value = 3 then (0 : Fin 5) else
          if value = 4 then (3 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1146.S5_1152.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1146.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1146.S5_1152.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1146.S5_1152.representative_basis

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14949

namespace S6_14954

-- Recovered packet case: e02a42596e41f197c510f76f4452d26ffc99a90b292eb46a517c1e728a962d0a
-- Target table: b9b12df9613406da91689b08b4b950667b3034b374b22fd800cc14034631c3e2
-- Oriented source table: d4201f78868e998ae873a51bfd4aadbdffc5057a203a3004b788d26fd63a9173
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 2 4 5 right else
    if left = 1 then row6 0 0 2 2 4 5 right else
      if left = 2 then row6 2 2 2 2 2 2 right else
        if left = 3 then row6 3 3 3 3 3 3 right else
          if left = 4 then row6 4 4 2 2 5 0 right else
            row6 5 5 2 2 0 4 right

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
      [[1, 1, 3, 3, 5, 6],
        [1, 1, 3, 3, 5, 6],
        [3, 3, 3, 3, 3, 3],
        [4, 4, 4, 4, 4, 4],
        [5, 5, 3, 3, 6, 1],
        [6, 6, 3, 3, 1, 5]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (2 : Fin 6) else
    if value = 1 then (0 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1146.S5_1146.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1146.S5_1146.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1146.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1146.S5_1146.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1146.S5_1146.representative_basis

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14954

namespace S6_15915

-- Recovered packet case: 8b2e449c6babb4c87656bd40462973b5e77e4c939eb4f1fb5f6d160d9d5bcdeb
-- Target table: 72a0b44e5ae118ace1952ba2eae19657cbb21a0598cf0d1072703e3a0daf1ef9
-- Oriented source table: d4201f78868e998ae873a51bfd4aadbdffc5057a203a3004b788d26fd63a9173
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 1 0 3 4 4 right else
      if left = 2 then row6 2 2 2 2 2 2 right else
        if left = 3 then row6 0 3 0 4 1 1 right else
          if left = 4 then row6 0 4 0 1 3 3 right else
            row6 0 4 0 1 3 3 right

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
        [1, 2, 1, 4, 5, 5],
        [3, 3, 3, 3, 3, 3],
        [1, 4, 1, 5, 2, 2],
        [1, 5, 1, 2, 4, 4],
        [1, 5, 1, 2, 4, 4]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (1 : Fin 6) else
      if value = 2 then (2 : Fin 6) else
        if value = 3 then (3 : Fin 6) else
          (4 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1146.S5_1146.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1146.S5_1146.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1146.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1146.S5_1146.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1146.S5_1146.representative_basis

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_15915

namespace S6_15930

-- Recovered packet case: ac48ba352b4131af0d8b395680024dec6a16425797fc7657f82efffdddc64e0b
-- Target table: dc1556d8f4a19161cef09384e2ffa68ab166b2791410d7f667cec98ba245115d
-- Oriented source table: e8a49abc3547db06a30968eea47aace636d7da69d466b6339b0c58e6bfeba958
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 3 4 4 right else
    if left = 1 then row6 0 1 1 3 4 4 right else
      if left = 2 then row6 0 2 2 3 4 4 right else
        if left = 3 then row6 3 3 3 4 0 0 right else
          if left = 4 then row6 4 4 4 0 3 3 right else
            row6 4 4 4 0 3 3 right

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
      [[1, 1, 1, 4, 5, 5],
        [1, 2, 2, 4, 5, 5],
        [1, 3, 3, 4, 5, 5],
        [4, 4, 4, 5, 1, 1],
        [5, 5, 5, 1, 4, 4],
        [5, 5, 5, 1, 4, 4]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (1 : Fin 6) else
      if value = 2 then (2 : Fin 6) else
        if value = 3 then (3 : Fin 6) else
          (4 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1146.S5_1152.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1146.S5_1152.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1146.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1146.S5_1152.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1146.S5_1152.representative_basis

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_15930

end SemigroupBasis.Generated.Order6GenericInflationV3.Family04

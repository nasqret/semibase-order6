import SemigroupBasis.PowerProductizedInflation
import SemigroupBasis.CoRoots.S5_1089Family

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6GenericInflationV3.Family05

open SemigroupBasis
open SemigroupBasis.PowerProductizedInflation

-- Family signature: 09fb0355e48395db3dfcff56135aba3f2c8c58ab79681777077538033514cedf
def extra : Nat := 1

def retained : List (Identity Nat) :=
  [{ lhs := { head := 0, tail := [1, 2] }, rhs := { head := 0, tail := [2, 1, 2] } }]

def sourceBasis : List (Identity Nat) :=
  [sourcePowerLaw extra] ++ retained

def targetBasis : List (Identity Nat) :=
  PowerProductizedInflation.basis extra retained

theorem sourceBasis_certificate :
    sourceBasis =
      [{ lhs := { head := 0, tail := [] }, rhs := { head := 0, tail := [0] } },
       { lhs := { head := 0, tail := [1, 2] }, rhs := { head := 0, tail := [2, 1, 2] } }] := by
  decide

theorem targetBasis_certificate :
    targetBasis =
      [{ lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 1] } },
       { lhs := { head := 0, tail := [1, 2] }, rhs := { head := 0, tail := [2, 1, 2] } }] := by
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

namespace S6_12175

-- Recovered packet case: f7bd464da6f145fbbe21d423deb232a45f4c6403a5ac03b50e0d364803dea8a8
-- Target table: 48ede2b305910257e723498bc7a67223729d687ebd179f145789a2b107b37d50
-- Oriented source table: 3a9e0a2cc202e7f174aab1f5fe9d21b2dd43c125f63a163e6713249045c7c5a9
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 2 0 2 5 right else
        if left = 3 then row6 3 3 3 3 3 3 right else
          if left = 4 then row6 0 0 2 0 4 5 right else
            row6 0 0 2 0 5 5 right

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
        [1, 1, 3, 1, 3, 6],
        [4, 4, 4, 4, 4, 4],
        [1, 1, 3, 1, 5, 6],
        [1, 1, 3, 1, 6, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (2 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1089.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1089.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1089.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1089.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1089Family.S5_1089.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_12175

namespace S6_12520

-- Recovered packet case: 80460d4305b157953fd4a4871cc1971cc7bc8e7fd7b1b6f71e48cb68d54dd41f
-- Target table: bb9f33fe4982099150241b6e268f404f85a02ffe35aece8b505a374209221c74
-- Oriented source table: 3a9e0a2cc202e7f174aab1f5fe9d21b2dd43c125f63a163e6713249045c7c5a9
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 2 2 2 2 2 2 right else
        if left = 3 then row6 2 2 2 3 3 5 right else
          if left = 4 then row6 2 2 2 3 4 5 right else
            row6 2 2 2 3 5 5 right

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
        [3, 3, 3, 4, 4, 6],
        [3, 3, 3, 4, 5, 6],
        [3, 3, 3, 4, 6, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (2 : Fin 6) else
    if value = 1 then (3 : Fin 6) else
      if value = 2 then (0 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1089.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1089.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1089.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1089.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1089Family.S5_1089.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_12520

namespace S6_14024

-- Recovered packet case: ae3f1de0ae84d6aea06d7af0b1f2f8a7481aae84a56d35195193449af224c5fb
-- Target table: a6b3f56a76bc18be7783f0a221d2b3280c12b1c45097ff32a8fd4f9bb0dfe8f2
-- Oriented source table: 918e692a3299260b96b85d98b1fcd936517eed1890509b2deef692d502486076
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 4 4 right else
    if left = 1 then row6 0 0 0 0 4 4 right else
      if left = 2 then row6 0 0 2 0 4 4 right else
        if left = 3 then row6 3 3 3 3 5 5 right else
          if left = 4 then row6 0 0 4 0 4 4 right else
            row6 3 3 5 3 5 5 right

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
        [1, 1, 5, 1, 5, 5],
        [4, 4, 6, 4, 6, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (2 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1143.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1143.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1089.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1143.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1089Family.S5_1143.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14024

namespace S6_14090

-- Recovered packet case: c26e20e01cea571d86b59f3ec7b57042913951c0081fec03da78ae3aeb581094
-- Target table: c5dd2f3ae1932e5841405ca9c6e47971de6d1a82d62016795a2a36daf12de9eb
-- Oriented source table: 918e692a3299260b96b85d98b1fcd936517eed1890509b2deef692d502486076
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 4 4 right else
    if left = 1 then row6 0 0 0 0 4 4 right else
      if left = 2 then row6 2 2 2 2 5 5 right else
        if left = 3 then row6 2 2 2 3 5 5 right else
          if left = 4 then row6 0 0 0 4 4 4 right else
            row6 2 2 2 5 5 5 right

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
        [1, 1, 1, 5, 5, 5],
        [3, 3, 3, 6, 6, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (2 : Fin 6) else
    if value = 1 then (3 : Fin 6) else
      if value = 2 then (0 : Fin 6) else
        if value = 3 then (5 : Fin 6) else
          (4 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1143.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1143.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1089.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1143.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1089Family.S5_1143.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14090

namespace S6_14551

-- Recovered packet case: 7dc4a24d68eb99268d9903cdd5a38129537088808863ed70e631b2569df009dc
-- Target table: 3b1231e220e8d288d589d5e67ac68079490fa95cbbc7944808747421d8bc05aa
-- Oriented source table: 918e692a3299260b96b85d98b1fcd936517eed1890509b2deef692d502486076
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 2 4 4 right else
    if left = 1 then row6 0 0 2 2 4 4 right else
      if left = 2 then row6 2 2 2 2 4 4 right else
        if left = 3 then row6 3 3 3 3 5 5 right else
          if left = 4 then row6 4 4 2 2 4 4 right else
            row6 5 5 3 3 5 5 right

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
        [5, 5, 3, 3, 5, 5],
        [6, 6, 4, 4, 6, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (2 : Fin 6) else
    if value = 1 then (0 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1143.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1143.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1089.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1143.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1089Family.S5_1143.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14551

namespace S6_14564

-- Recovered packet case: ca1f9ff8ac1de8e396e4a875223dcd7df9e808b0dc3eb1eb3d4c14f128322514
-- Target table: 64f5468ef71847051a41885c33f895cda2a79d05f889873c4a6778179526e613
-- Oriented source table: 3a9e0a2cc202e7f174aab1f5fe9d21b2dd43c125f63a163e6713249045c7c5a9
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 2 4 5 right else
    if left = 1 then row6 0 0 2 2 4 5 right else
      if left = 2 then row6 2 2 2 2 2 2 right else
        if left = 3 then row6 3 3 3 3 3 3 right else
          if left = 4 then row6 4 4 2 2 4 5 right else
            row6 5 5 2 2 4 5 right

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
        [5, 5, 3, 3, 5, 6],
        [6, 6, 3, 3, 5, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (2 : Fin 6) else
    if value = 1 then (4 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (0 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1089.table.semigroup) table.semigroup where
  toFun := embeddingValue
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def retractValue (value : Fin 6) : Fin 5 :=
  if value = 0 then (3 : Fin 5) else
    if value = 1 then (3 : Fin 5) else
      if value = 2 then (0 : Fin 5) else
        if value = 3 then (2 : Fin 5) else
          if value = 4 then (1 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1089.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1089.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.CoRoots.S5_1089Semantics.S5_1089.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1089Family.S5_1089.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14564

end SemigroupBasis.Generated.Order6GenericInflationV3.Family05

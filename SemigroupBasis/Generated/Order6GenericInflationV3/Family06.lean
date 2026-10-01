import SemigroupBasis.PowerProductizedInflation
import SemigroupBasis.CoRoots.S5_1092Family

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6GenericInflationV3.Family06

open SemigroupBasis
open SemigroupBasis.PowerProductizedInflation

-- Family signature: 07e0d2be66cb83b3969c69c6e06cc619ee05c00514a98710384849cee69e8dd9
def extra : Nat := 1

def retained : List (Identity Nat) :=
  [{ lhs := { head := 0, tail := [1, 2, 0] }, rhs := { head := 0, tail := [1, 0, 2, 0] } }]

def sourceBasis : List (Identity Nat) :=
  [sourcePowerLaw extra] ++ retained

def targetBasis : List (Identity Nat) :=
  PowerProductizedInflation.basis extra retained

theorem sourceBasis_certificate :
    sourceBasis =
      [{ lhs := { head := 0, tail := [] }, rhs := { head := 0, tail := [0] } },
       { lhs := { head := 0, tail := [1, 2, 0] }, rhs := { head := 0, tail := [1, 0, 2, 0] } }] := by
  decide

theorem targetBasis_certificate :
    targetBasis =
      [{ lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 0, 1] } },
       { lhs := { head := 0, tail := [1] }, rhs := { head := 0, tail := [1, 1] } },
       { lhs := { head := 0, tail := [1, 2, 0] }, rhs := { head := 0, tail := [1, 0, 2, 0] } }] := by
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

namespace S6_12178

-- Recovered packet case: ee418caef0bc2cc901f4c6f592ad4906890643d73caf721103c973c74832969c
-- Target table: 98151fd01785ab05d634e293fd4570b7cf736a9ca132d9295f06fe8b5079d53d
-- Oriented source table: 076fc9b142d0b8734a2ae2778feee26037c4429bbfa6ba79b3cae0874c0627b1
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 2 0 2 5 right else
        if left = 3 then row6 3 3 3 3 3 3 right else
          if left = 4 then row6 0 0 2 3 4 5 right else
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
        [1, 1, 3, 4, 5, 6],
        [1, 1, 3, 1, 6, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (2 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1092.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1092Family.S5_1092.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_12178

namespace S6_12315

-- Recovered packet case: 63cdf66016d164203f233adbcad6c1ce218abd580a7819629a74c7e534a4313f
-- Target table: 8f7cc9a12e4c0f17b201151074b0591c61fa388bb6d31a34e90da362fac6f8a1
-- Oriented source table: f54383105b3e100aaee9e753acff66cc281cf9fdeeb209bfd2d61966072c3af6
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 2 2 4 5 right else
        if left = 3 then row6 0 0 2 3 4 5 right else
          if left = 4 then row6 0 0 2 4 4 5 right else
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
      [[1, 1, 1, 1, 1, 1],
        [1, 1, 1, 1, 1, 1],
        [1, 1, 3, 3, 5, 6],
        [1, 1, 3, 4, 5, 6],
        [1, 1, 3, 5, 5, 6],
        [6, 6, 6, 6, 6, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else
    if value = 1 then (2 : Fin 6) else
      if value = 2 then (3 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1092.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1092Family.S5_1135.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_12315

namespace S6_12351

-- Recovered packet case: aeb382ecf78e7b29479baa401f2695919a5aaffc24bb491d81177c401e689d5e
-- Target table: f33b000796188c2dda7a03d340c07026b0df21e3a9f372726888b5c76f61645c
-- Oriented source table: 076fc9b142d0b8734a2ae2778feee26037c4429bbfa6ba79b3cae0874c0627b1
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 2 3 4 5 right else
        if left = 3 then row6 3 3 3 3 3 3 right else
          if left = 4 then row6 3 3 4 3 4 5 right else
            row6 3 3 5 3 4 5 right

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
        [4, 4, 5, 4, 5, 6],
        [4, 4, 6, 4, 5, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (3 : Fin 6) else
    if value = 1 then (4 : Fin 6) else
      if value = 2 then (0 : Fin 6) else
        if value = 3 then (2 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup) table.semigroup where
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
      if value = 2 then (3 : Fin 5) else
        if value = 3 then (0 : Fin 5) else
          if value = 4 then (1 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1092.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1092Family.S5_1092.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_12351

namespace S6_14052

-- Recovered packet case: 1b47d832f89fdeba0d1f809f5774163bd053d7406b03114ca938492664b95119
-- Target table: 3201e420c7b8f20c19390f6c56fe2616892da708d0f43dc77ddf7743d8fbc25b
-- Oriented source table: 3017d74accc2e43ed71034e6fde4f1ae2bc6b72ee1f5dac7a84cb08aa13eb779
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 4 4 right else
    if left = 1 then row6 0 0 0 0 4 4 right else
      if left = 2 then row6 0 0 2 3 4 5 right else
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
        [1, 1, 3, 4, 5, 6],
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

def embedding : Embedding (SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1092.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1092Family.S5_1144.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14052

namespace S6_14594

-- Recovered packet case: eefece60b251413f48368ab4bcad3a1c2ab7eebc54612c484cff7f4f0dfd3f30
-- Target table: 619d2421273c52c50e0a6d43dbd43110d10f1f0b687d58099e19ad04b62a4509
-- Oriented source table: 076fc9b142d0b8734a2ae2778feee26037c4429bbfa6ba79b3cae0874c0627b1
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 3 4 5 right else
    if left = 1 then row6 0 0 2 3 4 5 right else
      if left = 2 then row6 2 2 2 2 2 2 right else
        if left = 3 then row6 3 3 2 3 2 5 right else
          if left = 4 then row6 4 4 4 4 4 4 right else
            row6 5 5 2 3 2 5 right

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
        [4, 4, 3, 4, 3, 6],
        [5, 5, 5, 5, 5, 5],
        [6, 6, 3, 4, 3, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (2 : Fin 6) else
    if value = 1 then (3 : Fin 6) else
      if value = 2 then (4 : Fin 6) else
        if value = 3 then (0 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup) table.semigroup where
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
        if value = 3 then (1 : Fin 5) else
          if value = 4 then (2 : Fin 5) else
            (4 : Fin 5)

def inflation : Inflation (SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1092.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1092Family.S5_1092.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14594

namespace S6_14604

-- Recovered packet case: 6cab2da13c49d2ee12040c6c268e50462d0f34310abc00a608027287e7193a7d
-- Target table: ea7b698bdf36e172f6bfa1336e5074b7ab54b5105e70d9df52f52d6b5a60974c
-- Oriented source table: f54383105b3e100aaee9e753acff66cc281cf9fdeeb209bfd2d61966072c3af6
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 3 4 5 right else
    if left = 1 then row6 0 0 2 3 4 5 right else
      if left = 2 then row6 2 2 2 2 2 2 right else
        if left = 3 then row6 3 3 2 3 4 5 right else
          if left = 4 then row6 4 4 2 3 4 5 right else
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
      [[1, 1, 3, 4, 5, 6],
        [1, 1, 3, 4, 5, 6],
        [3, 3, 3, 3, 3, 3],
        [4, 4, 3, 4, 5, 6],
        [5, 5, 3, 4, 5, 6],
        [6, 6, 6, 6, 6, 6]] := by
  decide

def embeddingValue (value : Fin 5) : Fin 6 :=
  if value = 0 then (2 : Fin 6) else
    if value = 1 then (3 : Fin 6) else
      if value = 2 then (0 : Fin 6) else
        if value = 3 then (4 : Fin 6) else
          (5 : Fin 6)

def embedding : Embedding (SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1092.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1092Family.S5_1135.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14604

namespace S6_14607

-- Recovered packet case: 43c94e7a495867fbb3137dd3af6d62be653224b584ec9244f0fcc4413b59dfe3
-- Target table: ec0ded7b2d09e13922277689443f42ab45e2bf368aeaf4d9a05a2688df81e39e
-- Oriented source table: 3017d74accc2e43ed71034e6fde4f1ae2bc6b72ee1f5dac7a84cb08aa13eb779
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 3 4 5 right else
    if left = 1 then row6 0 0 2 3 4 5 right else
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
      [[1, 1, 3, 4, 5, 6],
        [1, 1, 3, 4, 5, 6],
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

def embedding : Embedding (SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup) table.semigroup where
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

def inflation : Inflation (SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup) table.semigroup where
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
    sourceBasis = (SemigroupBasis.CoRoots.S5_1092.basis) := by
  decide

theorem source_basis :
    BasisFor (SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup) sourceBasis := by
  rw [sourceBasis_eq_catalogue]
  exact SemigroupBasis.CoRoots.S5_1092Family.S5_1144.basis_complete

theorem representative_basis : BasisFor table.semigroup targetBasis :=
  Inflation.inheritPowerProductizedBasis
    extra (by decide) retained sourceBasis sourceMembership retainedProducts
    inflation proper source_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_14607

end SemigroupBasis.Generated.Order6GenericInflationV3.Family06

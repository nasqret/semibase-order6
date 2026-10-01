import SemigroupBasis.CoRoots.Order6ContentFirstTailRoots

namespace SemigroupBasis.CoRoots.Order6ContentFirstTailResidualRoots

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6ContentFirstTailRoots

/-! The nine catalogue-oriented roots below are the opposites of the records in
packet `32ed05ce75b588be34d250a13baff6556d2f912c21abc76114c34d3faba58841`.
They share bounded signature
`658c8acc6a6efc842a19290d71f9d1dbbcbf3d7aa2468395caf2956c055ead05`. -/

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem models_of_finite_checks
    (candidate : FiniteTable)
    (roundTrip : basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinThree).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp roundTrip) identity member
  rw [restored] at finiteValid
  exact finiteValid

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-! ## `S6_3364` -/

namespace S6_3364

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],
  [1,1,2,1,1,1],[1,1,1,1,5,5],[1,1,1,1,6,6]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 0 0 0 right else
        if left = 3 then row6 0 0 1 0 0 0 right else
          if left = 4 then row6 0 0 0 0 4 4 right else
            row6 0 0 0 0 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a9eac758d2f5fe28fb970cee1f995d4526f90eeeb2afefd36130933bfbddc46e"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1],
        [1, 1, 1, 1, 1, 1], [1, 1, 2, 1, 1, 1],
        [1, 1, 1, 1, 5, 5], [1, 1, 1, 1, 6, 6]] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide) (by decide)

def leftZeroEmbedding : Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def semilatticeEmbedding :
    Embedding semilatticeTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem direct_basis : BasisFor table.semigroup basis :=
  basisFor_of_contentFirstTailWitnesses table.semigroup models
    leftZeroEmbedding semilatticeEmbedding (1 : Fin 6) (by decide)
    (3 : Fin 6) (2 : Fin 6) (by decide)

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_basis]
  exact direct_basis.oppositeReversed

end S6_3364

/-! ## `S6_3621` -/

namespace S6_3621

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],
  [1,1,2,1,1,1],[1,1,1,1,5,5],[1,1,1,1,6,6]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 1 0 0 right else
        if left = 3 then row6 0 0 1 0 0 0 right else
          if left = 4 then row6 0 0 0 0 4 4 right else
            row6 0 0 0 0 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "34d4d880edb372324aa6eced81ed79c57a071acc8d1bf16e8b80ba66a4d8a346"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1],
        [1, 1, 1, 2, 1, 1], [1, 1, 2, 1, 1, 1],
        [1, 1, 1, 1, 5, 5], [1, 1, 1, 1, 6, 6]] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide) (by decide)

def leftZeroEmbedding : Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def semilatticeEmbedding :
    Embedding semilatticeTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem direct_basis : BasisFor table.semigroup basis :=
  basisFor_of_contentFirstTailWitnesses table.semigroup models
    leftZeroEmbedding semilatticeEmbedding (1 : Fin 6) (by decide)
    (2 : Fin 6) (3 : Fin 6) (by decide)

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_basis]
  exact direct_basis.oppositeReversed

end S6_3621

/-! ## `S6_5894` -/

namespace S6_5894

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],
  [1,1,1,4,4,1],[1,1,2,4,4,1],[6,6,6,6,6,6]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 0 0 0 right else
        if left = 3 then row6 0 0 0 3 3 0 right else
          if left = 4 then row6 0 0 1 3 3 0 right else
            row6 5 5 5 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b8ee5afd141a7a3c4e611a7d8bafc7ed5b1b91ab83ea6d4a1d48bd98f93fbef6"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1],
        [1, 1, 1, 1, 1, 1], [1, 1, 1, 4, 4, 1],
        [1, 1, 2, 4, 4, 1], [6, 6, 6, 6, 6, 6]] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide) (by decide)

def leftZeroEmbedding : Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def semilatticeEmbedding :
    Embedding semilatticeTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (3 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem direct_basis : BasisFor table.semigroup basis :=
  basisFor_of_contentFirstTailWitnesses table.semigroup models
    leftZeroEmbedding semilatticeEmbedding (1 : Fin 6) (by decide)
    (4 : Fin 6) (2 : Fin 6) (by decide)

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_basis]
  exact direct_basis.oppositeReversed

end S6_5894

/-! ## `S6_5912` -/

namespace S6_5912

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],
  [1,1,1,4,4,4],[1,1,2,4,4,4],[1,1,1,6,6,6]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 0 0 0 right else
        if left = 3 then row6 0 0 0 3 3 3 right else
          if left = 4 then row6 0 0 1 3 3 3 right else
            row6 0 0 0 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0a5ac5de2c8d25d9a8d6fbc3bf4df45413193009ab2e76d25566a4aca4bfcd65"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1],
        [1, 1, 1, 1, 1, 1], [1, 1, 1, 4, 4, 4],
        [1, 1, 2, 4, 4, 4], [1, 1, 1, 6, 6, 6]] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide) (by decide)

def leftZeroEmbedding : Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def semilatticeEmbedding :
    Embedding semilatticeTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (3 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem direct_basis : BasisFor table.semigroup basis :=
  basisFor_of_contentFirstTailWitnesses table.semigroup models
    leftZeroEmbedding semilatticeEmbedding (1 : Fin 6) (by decide)
    (4 : Fin 6) (2 : Fin 6) (by decide)

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_basis]
  exact direct_basis.oppositeReversed

end S6_5912

/-! ## `S6_6157` -/

namespace S6_6157

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,2,1],
  [1,1,1,4,4,1],[1,1,2,4,4,1],[6,6,6,6,6,6]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 0 1 0 right else
        if left = 3 then row6 0 0 0 3 3 0 right else
          if left = 4 then row6 0 0 1 3 3 0 right else
            row6 5 5 5 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "935a3b55a2b221b1161969815eec83cb6ae4152503aa72f8c09619870e4a2933"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1],
        [1, 1, 1, 1, 2, 1], [1, 1, 1, 4, 4, 1],
        [1, 1, 2, 4, 4, 1], [6, 6, 6, 6, 6, 6]] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide) (by decide)

def leftZeroEmbedding : Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def semilatticeEmbedding :
    Embedding semilatticeTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (3 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem direct_basis : BasisFor table.semigroup basis :=
  basisFor_of_contentFirstTailWitnesses table.semigroup models
    leftZeroEmbedding semilatticeEmbedding (1 : Fin 6) (by decide)
    (2 : Fin 6) (4 : Fin 6) (by decide)

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_basis]
  exact direct_basis.oppositeReversed

end S6_6157

/-! ## `S6_6160` -/

namespace S6_6160

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,2,1],
  [1,1,1,4,4,4],[1,1,2,4,4,4],[1,1,1,6,6,6]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 0 1 0 right else
        if left = 3 then row6 0 0 0 3 3 3 right else
          if left = 4 then row6 0 0 1 3 3 3 right else
            row6 0 0 0 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4ac6e80aa1e18ec1a1a79de9da2cd7a36eca687874a944460960c6263ae6a1c9"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1],
        [1, 1, 1, 1, 2, 1], [1, 1, 1, 4, 4, 4],
        [1, 1, 2, 4, 4, 4], [1, 1, 1, 6, 6, 6]] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide) (by decide)

def leftZeroEmbedding : Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def semilatticeEmbedding :
    Embedding semilatticeTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (3 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem direct_basis : BasisFor table.semigroup basis :=
  basisFor_of_contentFirstTailWitnesses table.semigroup models
    leftZeroEmbedding semilatticeEmbedding (1 : Fin 6) (by decide)
    (2 : Fin 6) (4 : Fin 6) (by decide)

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_basis]
  exact direct_basis.oppositeReversed

end S6_6160

/-! ## `S6_6181` -/

namespace S6_6181

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,2,1],
  [6,6,6,4,4,6],[6,6,6,4,4,6],[6,6,6,6,6,6]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 0 1 0 right else
        if left = 3 then row6 5 5 5 3 3 5 right else
          if left = 4 then row6 5 5 5 3 3 5 right else
            row6 5 5 5 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "7a783ef21d05ce721bc65a211aa975749894feb315fa74719a44a1f62d9b2ac6"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1],
        [1, 1, 1, 1, 2, 1], [6, 6, 6, 4, 4, 6],
        [6, 6, 6, 4, 4, 6], [6, 6, 6, 6, 6, 6]] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide) (by decide)

def leftZeroEmbedding : Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def semilatticeEmbedding :
    Embedding semilatticeTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (5 : Fin 6) else (3 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem direct_basis : BasisFor table.semigroup basis :=
  basisFor_of_contentFirstTailWitnesses table.semigroup models
    leftZeroEmbedding semilatticeEmbedding (1 : Fin 6) (by decide)
    (2 : Fin 6) (4 : Fin 6) (by decide)

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_basis]
  exact direct_basis.oppositeReversed

end S6_6181

/-! ## `S6_6625` -/

namespace S6_6625

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,6],[1,1,1,1,1,6],[1,1,1,1,2,6],
  [4,4,4,4,4,6],[4,4,4,4,4,6],[6,6,6,6,6,6]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 5 right else
    if left = 1 then row6 0 0 0 0 0 5 right else
      if left = 2 then row6 0 0 0 0 1 5 right else
        if left = 3 then row6 3 3 3 3 3 5 right else
          if left = 4 then row6 3 3 3 3 3 5 right else
            row6 5 5 5 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5753909d858ce1d53138a13b0afcfc539deff3a33c0b0cd984b863ea0f2b942e"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 6], [1, 1, 1, 1, 1, 6],
        [1, 1, 1, 1, 2, 6], [4, 4, 4, 4, 4, 6],
        [4, 4, 4, 4, 4, 6], [6, 6, 6, 6, 6, 6]] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide) (by decide)

def leftZeroEmbedding : Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (3 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def semilatticeEmbedding :
    Embedding semilatticeTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (5 : Fin 6) else (0 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem direct_basis : BasisFor table.semigroup basis :=
  basisFor_of_contentFirstTailWitnesses table.semigroup models
    leftZeroEmbedding semilatticeEmbedding (1 : Fin 6) (by decide)
    (2 : Fin 6) (4 : Fin 6) (by decide)

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_basis]
  exact direct_basis.oppositeReversed

end S6_6625

/-! ## `S6_9817` -/

namespace S6_9817

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,3,3,1,1],
  [1,1,3,3,1,2],[5,5,5,5,5,5],[5,5,5,5,5,5]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 2 2 0 0 right else
        if left = 3 then row6 0 0 2 2 0 1 right else
          if left = 4 then row6 4 4 4 4 4 4 right else
            row6 4 4 4 4 4 4 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5bc3f8e23a3486421de015c95b71274e5aba346d4b53a4766d6d02387a1dc1ac"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1],
        [1, 1, 3, 3, 1, 1], [1, 1, 3, 3, 1, 2],
        [5, 5, 5, 5, 5, 5], [5, 5, 5, 5, 5, 5]] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide) (by decide)

def leftZeroEmbedding : Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def semilatticeEmbedding :
    Embedding semilatticeTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (2 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem direct_basis : BasisFor table.semigroup basis :=
  basisFor_of_contentFirstTailWitnesses table.semigroup models
    leftZeroEmbedding semilatticeEmbedding (1 : Fin 6) (by decide)
    (3 : Fin 6) (5 : Fin 6) (by decide)

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_basis]
  exact direct_basis.oppositeReversed

end S6_9817

end SemigroupBasis.CoRoots.Order6ContentFirstTailResidualRoots

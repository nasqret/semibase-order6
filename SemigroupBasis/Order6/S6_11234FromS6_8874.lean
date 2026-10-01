import SemigroupBasis.CoRoots.S6_8874LeeLiCondition6
import SemigroupBasis.FiniteReflection
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Order6.S6_11234

open SemigroupBasis

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact Smallsemi representative `S6_11234`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 1 1 right else
      if left = 2 then row6 0 1 2 3 1 2 right else
        if left = 3 then row6 0 1 3 2 1 3 right else
          if left = 4 then row6 0 0 0 0 4 4 right else
            row6 0 1 2 3 4 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (table.mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2, 2],
        [1, 2, 3, 4, 2, 3], [1, 2, 4, 3, 2, 4],
        [1, 1, 1, 1, 5, 5], [1, 2, 3, 4, 5, 6]] := by
  decide

def tableSHA256 : String :=
  "e643b191e8bff79936dab2ae1fa5cc10240ed480280c60162522b7a8a6f87819"

/-! ## Exact power embedding of the complete source -/

def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1, 2, 1, 3, 5, 6], [3, 3, 4, 3, 3, 3]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased =
      [[1, 2, 1, 3, 5, 6], [3, 3, 4, 3, 3, 3]] := by
  decide

def coordinateValue (coordinate : Fin 2) (value : Fin 6) : Fin 6 :=
  if coordinate = 0 then
    row6 0 1 0 2 4 5 value
  else
    row6 2 2 3 2 2 2 value

def coordinateHom (coordinate : Fin 2) :
    Hom SemigroupBasis.CoRoots.S6_8874.table.semigroup table.semigroup where
  toFun := coordinateValue coordinate
  map_mul := by
    intro left right
    apply Fin.ext
    revert coordinate left right
    decide

/-- The two recorded homomorphisms separate all six source elements. -/
def sourceEmbedding :
    Embedding SemigroupBasis.CoRoots.S6_8874.table.semigroup
      (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro left right equalCoordinates
    revert left right
    decide)

/-! ## Finite soundness of the reused basis -/

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.S6_8874.basis

def oppositeBasis : List (Identity Nat) := reversedBasis basis

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun identity => identity.map toFinFour

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinFour).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

private theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinFour ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

set_option maxHeartbeats 2000000 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

/-- The complete `S6_8874` basis transfers along the explicit embedding into
`S6_11234^2`. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.S6_8874.representative_basis.inheritAlongPowerEmbedding
    sourceEmbedding models

/-- Reversal gives the corresponding endpoint for the opposite table. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end SemigroupBasis.Order6.S6_11234

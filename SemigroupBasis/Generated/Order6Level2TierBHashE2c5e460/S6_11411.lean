import SemigroupBasis.Generated.Order6Level2TierBHashE2c5e460.S6_10956
import SemigroupBasis.Nonfinite
import SemigroupBasis.SeparatingHoms

namespace SemigroupBasis.Generated.Order6Level2TierBHashE2c5e460.S6_11411

open SemigroupBasis
open SemigroupBasis.Generated.Order6Level2TierBHashE2c5e460.Shared

/-- Authenticated order-six table, SHA-256 `c3662044617a8eacd04b75ed29e4421982f781e64c1cd7a17ab9829acd5b8902`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if a = 1 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (1 : Fin 6)
    else if b = 3 then (1 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if a = 2 then
    if b = 0 then (4 : Fin 6)
    else if b = 1 then (4 : Fin 6)
    else if b = 2 then (2 : Fin 6)
    else if b = 3 then (3 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (4 : Fin 6)
  else if a = 3 then
    if b = 0 then (4 : Fin 6)
    else if b = 1 then (4 : Fin 6)
    else if b = 2 then (3 : Fin 6)
    else if b = 3 then (2 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (4 : Fin 6)
  else if a = 4 then
    if b = 0 then (4 : Fin 6)
    else if b = 1 then (4 : Fin 6)
    else if b = 2 then (4 : Fin 6)
    else if b = 3 then (4 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (4 : Fin 6)
  else
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (1 : Fin 6)
    else if b = 2 then (1 : Fin 6)
    else if b = 3 then (1 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "c3662044617a8eacd04b75ed29e4421982f781e64c1cd7a17ab9829acd5b8902"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0], [4, 4, 2, 3, 4, 4], [4, 4, 3, 2, 4, 4], [4, 4, 4, 4, 4, 4], [0, 1, 1, 1, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def rootToLeafValue (i : Fin 2) (a : Fin 6) : Fin 6 :=
  if i = 0 then
    if a = 0 then (0 : Fin 6)
    else if a = 1 then (1 : Fin 6)
    else if a = 2 then (5 : Fin 6)
    else if a = 3 then (5 : Fin 6)
    else if a = 4 then (4 : Fin 6)
    else (2 : Fin 6)
  else
    if a = 0 then (4 : Fin 6)
    else if a = 1 then (4 : Fin 6)
    else if a = 2 then (2 : Fin 6)
    else if a = 3 then (3 : Fin 6)
    else if a = 4 then (0 : Fin 6)
    else (0 : Fin 6)

def rootToLeafHom (i : Fin 2) :
    Hom SemigroupBasis.Generated.Order6Level2TierBHashE2c5e460.S6_10956.table.semigroup table.semigroup where
  toFun := rootToLeafValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def rootIntoLeafPower :
    Embedding SemigroupBasis.Generated.Order6Level2TierBHashE2c5e460.S6_10956.table.semigroup
      (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms rootToLeafHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def leafToRootValue (i : Fin 2) (a : Fin 6) : Fin 6 :=
  if i = 0 then
    if a = 0 then (0 : Fin 6)
    else if a = 1 then (0 : Fin 6)
    else if a = 2 then (2 : Fin 6)
    else if a = 3 then (3 : Fin 6)
    else if a = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else
    if a = 0 then (0 : Fin 6)
    else if a = 1 then (1 : Fin 6)
    else if a = 2 then (5 : Fin 6)
    else if a = 3 then (5 : Fin 6)
    else if a = 4 then (4 : Fin 6)
    else (2 : Fin 6)

def leafToRootHom (i : Fin 2) :
    Hom table.semigroup SemigroupBasis.Generated.Order6Level2TierBHashE2c5e460.S6_10956.table.semigroup where
  toFun := leafToRootValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def leafIntoRootPower :
    Embedding table.semigroup
      (SemigroupBasis.Generated.Order6Level2TierBHashE2c5e460.S6_10956.table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms leafToRootHom (by
    intro a b equalCoordinates
    revert a b
    decide)

theorem sameIdentityTheoryOver :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Order6Level2TierBHashE2c5e460.S6_10956.table.semigroup table.semigroup Nat := by
  intro identity
  constructor
  case mp =>
    intro rootValid
    exact leafIntoRootPower.pullback_identity identity
      (identity.satisfiedByPi
        SemigroupBasis.Generated.Order6Level2TierBHashE2c5e460.S6_10956.table.semigroup (Fin 2) rootValid)
  case mpr =>
    intro leafValid
    exact rootIntoLeafPower.pullback_identity identity
      (identity.satisfiedByPi table.semigroup (Fin 2) leafValid)

abbrev basis : List (Identity Nat) := Shared.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheoryOver).mp
    SemigroupBasis.Generated.Order6Level2TierBHashE2c5e460.S6_10956.representative_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6Level2TierBHashE2c5e460.S6_11411

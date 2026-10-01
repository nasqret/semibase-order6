import SemigroupBasis.Examples.AffineShiftThreeSyntax
import SemigroupBasis.FiniteReflection

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The exact zero-based multiplication of `S6_15903`. The element `1` is
the identity, `0`, `2`, and `3` form the left-zero ideal, and `4`, `5` are the
two nontrivial shifts. -/
def affineShiftThreeMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then b
  else if a = 2 then 2
  else if a = 3 then 3
  else if a = 4 then
    if b = 0 then 2
    else if b = 1 then 4
    else if b = 2 then 3
    else if b = 3 then 0
    else if b = 4 then 5
    else 1
  else
    if b = 0 then 3
    else if b = 1 then 5
    else if b = 2 then 0
    else if b = 3 then 2
    else if b = 4 then 1
    else 4

/-- The order-six affine-shift monoid, catalogue class `S6_15903`. -/
def affineShiftThree : FiniteTable where
  order := 6
  mul := affineShiftThreeMul
  assoc := by decide

def affineShiftThreeRowsZeroBased : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0],
   [0, 1, 2, 3, 4, 5],
   [2, 2, 2, 2, 2, 2],
   [3, 3, 3, 3, 3, 3],
   [2, 4, 3, 0, 5, 1],
   [3, 5, 0, 2, 1, 4]]

/-- Decide-bound equality with the catalogue Cayley matrix. -/
theorem affineShiftThreeMul_rows :
    ((List.finRange 6).map fun a =>
      (List.finRange 6).map fun b => (affineShiftThreeMul a b).val) =
        affineShiftThreeRowsZeroBased := by
  decide

/-- The cyclic unit subgroup, indexed by its residue modulo three. -/
def affineShiftThreeUnitResidue (residue : Fin 3) : Fin 6 :=
  if residue = 0 then 1 else if residue = 1 then 4 else 5

/-- The left-zero ideal, indexed compatibly with the unit action. -/
def affineShiftThreeIdealResidue (residue : Fin 3) : Fin 6 :=
  if residue = 0 then 0 else if residue = 1 then 2 else 3

/-- Unit multiplication adds the corresponding residues modulo three. -/
theorem affineShiftThreeMul_unitResidues (left right : Fin 3) :
    affineShiftThree.mul
        (affineShiftThreeUnitResidue left)
        (affineShiftThreeUnitResidue right) =
      affineShiftThreeUnitResidue (left + right) := by
  decide +revert

/-- A unit acts on the left-zero ideal by adding its residue. -/
theorem affineShiftThreeMul_unit_ideal (unit ideal : Fin 3) :
    affineShiftThree.mul
        (affineShiftThreeUnitResidue unit)
        (affineShiftThreeIdealResidue ideal) =
      affineShiftThreeIdealResidue (unit + ideal) := by
  decide +revert

/-- Every ideal element is left-zero against every table element. -/
theorem affineShiftThreeMul_ideal_left
    (ideal : Fin 3) (right : Fin 6) :
    affineShiftThree.mul
        (affineShiftThreeIdealResidue ideal) right =
      affineShiftThreeIdealResidue ideal := by
  decide +revert

private def affineShiftThreeToFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def affineShiftThreeFiniteBasis : List (Identity (Fin 3)) :=
  affineShiftThreeBasis.map fun identity =>
    identity.map affineShiftThreeToFinThree

private theorem affineShiftThreeBasis_roundTrip_checked :
    affineShiftThreeBasis.all (fun identity =>
      decide
        ((identity.map affineShiftThreeToFinThree).map Fin.val =
          identity)) = true := by
  decide

private theorem affineShiftThreeBasis_roundTrip
    (identity : Identity Nat) (member : identity ∈ affineShiftThreeBasis) :
    (identity.map affineShiftThreeToFinThree).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp affineShiftThreeBasis_roundTrip_checked)
      identity member

/-- Exhaustive finite checks lift the displayed three-variable laws back to
the standard natural-number variable type. -/
theorem affineShiftThreeModelsOfFiniteChecks
    (candidate : FiniteTable)
    (checked :
      affineShiftThreeFiniteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup affineShiftThreeBasis := by
  intro identity member
  have finiteMember :
      identity.map affineShiftThreeToFinThree ∈
        affineShiftThreeFiniteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound
      (identity.map affineShiftThreeToFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [affineShiftThreeBasis_roundTrip identity member] at finiteValid
  exact finiteValid

set_option maxRecDepth 100000 in
/-- The exact `S6_15903` table satisfies all six displayed laws. -/
theorem affineShiftThreeModels :
    Models affineShiftThree.semigroup affineShiftThreeBasis :=
  affineShiftThreeModelsOfFiniteChecks affineShiftThree (by decide)

end SemigroupBasis.Examples

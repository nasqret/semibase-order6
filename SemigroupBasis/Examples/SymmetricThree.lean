import SemigroupBasis.Examples.SymmetricThreeSyntax
import SemigroupBasis.FiniteReflection

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The exact zero-based multiplication table of the symmetric group `S3`,
catalogue class `S6_4337`. -/
def symmetricThreeMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then b
  else if a = 1 then
    if b = 0 then 1
    else if b = 1 then 0
    else if b = 2 then 4
    else if b = 3 then 5
    else if b = 4 then 2
    else 3
  else if a = 2 then
    if b = 0 then 2
    else if b = 1 then 5
    else if b = 2 then 0
    else if b = 3 then 4
    else if b = 4 then 3
    else 1
  else if a = 3 then
    if b = 0 then 3
    else if b = 1 then 4
    else if b = 2 then 5
    else if b = 3 then 0
    else if b = 4 then 1
    else 2
  else if a = 4 then
    if b = 0 then 4
    else if b = 1 then 3
    else if b = 2 then 1
    else if b = 3 then 2
    else if b = 4 then 5
    else 0
  else
    if b = 0 then 5
    else if b = 1 then 2
    else if b = 2 then 3
    else if b = 3 then 1
    else if b = 4 then 0
    else 4

/-- The six-element symmetric group in the stored catalogue orientation. -/
def symmetricThree : FiniteTable where
  order := 6
  mul := symmetricThreeMul
  assoc := by decide

def symmetricThreeRowsZeroBased : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5],
   [1, 0, 4, 5, 2, 3],
   [2, 5, 0, 4, 3, 1],
   [3, 4, 5, 0, 1, 2],
   [4, 3, 1, 2, 5, 0],
   [5, 2, 3, 1, 0, 4]]

/-- Decide-bound equality with the catalogue Cayley matrix. -/
theorem symmetricThreeMul_rows :
    ((List.finRange 6).map fun a =>
      (List.finRange 6).map fun b => (symmetricThreeMul a b).val) =
        symmetricThreeRowsZeroBased := by
  decide

private def symmetricThreeToFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

def symmetricThreeFiniteBasis : List (Identity (Fin 2)) :=
  symmetricThreeBasis.map fun identity =>
    identity.map symmetricThreeToFinTwo

private theorem symmetricThreeBasis_roundTrip_checked :
    symmetricThreeBasis.all (fun identity =>
      decide
        ((identity.map symmetricThreeToFinTwo).map Fin.val = identity)) =
      true := by
  decide

private theorem symmetricThreeBasis_roundTrip
    (identity : Identity Nat) (member : identity ∈ symmetricThreeBasis) :
    (identity.map symmetricThreeToFinTwo).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp symmetricThreeBasis_roundTrip_checked)
      identity member

/-- Exhaustive two-variable checks lift the displayed laws back to identities
over natural-number variable names. -/
theorem symmetricThreeModelsOfFiniteChecks
    (candidate : FiniteTable)
    (checked :
      symmetricThreeFiniteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup symmetricThreeBasis := by
  intro identity member
  have finiteMember :
      identity.map symmetricThreeToFinTwo ∈ symmetricThreeFiniteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound
      (identity.map symmetricThreeToFinTwo)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [symmetricThreeBasis_roundTrip identity member] at finiteValid
  exact finiteValid

set_option maxRecDepth 100000 in
/-- The exact `S6_4337` table satisfies its three displayed basis laws. -/
theorem symmetricThreeModels :
    Models symmetricThree.semigroup symmetricThreeBasis :=
  symmetricThreeModelsOfFiniteChecks symmetricThree (by decide)

end SemigroupBasis.Examples

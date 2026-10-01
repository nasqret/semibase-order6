import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

/-!
# S6_9776: the unchanged e50c9e eight-law presentation

The actual quotient pair is S2_4-opposite and S5_534-direct. The displayed
eight laws are kept in their frozen order; no HFB or bounded-key premise is
used. The literal square/cube boundary is retained.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776

open SemigroupBasis

def law00 : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0]⟩⟩
def law01 : Identity Nat := ⟨⟨0, [0, 0, 1]⟩, ⟨0, [0, 1]⟩⟩
def law02 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
def law03 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 1]⟩⟩
def law04 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def law05 : Identity Nat := ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 2]⟩⟩
def law06 : Identity Nat := ⟨⟨0, [1, 0, 2]⟩, ⟨0, [1, 2]⟩⟩
def law07 : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1, 2]⟩⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07]

def displayedBasisSHA256 : String :=
  "e50c9e573ade4bfa8de0726c082b9ffb628a414c3d2cd1f3904ffbd8321ee531"

theorem basis_length : basis.length = 8 := rfl

def mul (a b : Fin 6) : Fin 6 :=
  if b = 4 then 4 else if b = 5 then 5
  else if a = 2 ∧ b = 2 then 1
  else if a = 3 then 3 else if a = 4 ∨ a = 5 then 4 else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem table_rows_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul a b).val)) =
      [[0,0,0,0,4,5], [0,0,0,0,4,5], [0,0,1,0,4,5],
       [3,3,3,3,4,5], [4,4,4,4,4,5], [4,4,4,4,4,5]] := by decide

private def toFin : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem raw_roundtrips :
    basis.all (fun identity => decide ((identity.map toFin).map Fin.val = identity)) = true := by decide

private theorem raw_checks :
    basis.all (fun identity => table.checkIdentityFused (identity.map toFin)) = true := by decide

theorem models_raw : Models table.semigroup basis := by
  intro identity member
  have roundtrip : (identity.map toFin).map Fin.val = identity :=
    of_decide_eq_true ((List.all_eq_true.mp raw_roundtrips) identity member)
  have valid := table.checkIdentityFusedNat_sound (identity.map toFin)
    ((List.all_eq_true.mp raw_checks) identity member)
  rw [roundtrip] at valid
  exact valid

theorem models_opposite_raw : Models table.semigroup.opposite (reversedBasis basis) :=
  models_raw.oppositeReversed

def squareCube : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def bandLaw : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, []⟩⟩

theorem square_cube_invalid : ¬ squareCube.SatisfiedBy table.semigroup := by
  intro valid
  have equal := valid (fun _ => (2 : Fin 6))
  change (1 : Fin 6) = 0 at equal
  exact (by decide : (1 : Fin 6) ≠ 0) equal

theorem band_invalid : ¬ bandLaw.SatisfiedBy table.semigroup := by
  intro valid
  have equal := valid (fun _ => (2 : Fin 6))
  change (1 : Fin 6) = 2 at equal
  exact (by decide : (1 : Fin 6) ≠ 2) equal

#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.basis_length
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.table
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.table_rows_exact
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.models_raw
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.models_opposite_raw
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.square_cube_invalid
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.band_invalid

end SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776

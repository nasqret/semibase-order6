import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

/-!
# Literal S6_5441 and its unchanged eleven-law presentation

O6F_0005/direct:17 belongs to the authenticated direct16/17 contract.
Condition17 and the target's dual HFB5 membership are not completeness
premises. The square/cube boundary remains visible: xx is not xxx here.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5441

open SemigroupBasis

/-- xxx = xxxx. -/
def law00 : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0]⟩⟩
/-- xxxy = xxy. -/
def law01 : Identity Nat := ⟨⟨0, [0, 0, 1]⟩, ⟨0, [0, 1]⟩⟩
/-- xxyx = xyx. -/
def law02 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
/-- xxyy = xyy. -/
def law03 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1]⟩⟩
/-- xxyz = xyz. -/
def law04 : Identity Nat := ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 2]⟩⟩
/-- xyxx = xyxy. -/
def law05 : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0, 1]⟩⟩
/-- xyxx = xyyx. -/
def law06 : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 1, 0]⟩⟩
/-- xyxx = xyyy. -/
def law07 : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 1, 1]⟩⟩
/-- xyxx = yxxx. -/
def law08 : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 0, 0]⟩⟩
/-- xyzx = yxzx. -/
def law09 : Identity Nat := ⟨⟨0, [1, 2, 0]⟩, ⟨1, [0, 2, 0]⟩⟩
/-- xyzz = yxzz. -/
def law10 : Identity Nat := ⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 2, 2]⟩⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10]

def displayedBasisSHA256 : String :=
  "a26d8537fbe83a104964558f0d87c004f8283bd2667804a9dff45b38c6c63c0c"

theorem basis_length : basis.length = 11 := rfl

def mul (left right : Fin 6) : Fin 6 :=
  if left = 2 ∨ left = 3 then
    if right = 3 ∨ right = 5 then 1 else 0
  else if left = 4 ∨ left = 5 then
    if right = 1 then 1 else if right = 2 ∨ right = 3 then 2
    else if right = 4 ∨ right = 5 then 4 else 0
  else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem table_rows_exact :
    (List.finRange 6).map (fun left => (List.finRange 6).map (fun right => (mul left right).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,0,0], [0,0,0,1,0,1],
       [0,0,0,1,0,1], [0,1,2,2,4,4], [0,1,2,2,4,4]] := by decide

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

def oldPower : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem oldPower_invalid : ¬ oldPower.SatisfiedBy table.semigroup := by
  intro valid
  have equal := valid (fun _ => (3 : Fin 6))
  change (1 : Fin 6) = 0 at equal
  exact (by decide : (1 : Fin 6) ≠ 0) equal

def bandPower : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, []⟩⟩

theorem bandPower_invalid : ¬ bandPower.SatisfiedBy table.semigroup := by
  intro valid
  have equal := valid (fun _ => (1 : Fin 6))
  change (0 : Fin 6) = 1 at equal
  exact (by decide : (0 : Fin 6) ≠ 1) equal

def abaControl : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 0, 0, 1, 0]⟩⟩

private def abaControlFin : Identity (Fin 2) := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 0, 0, 1, 0]⟩⟩

theorem abaControl_valid : abaControl.SatisfiedBy table.semigroup := by
  change (abaControlFin.map Fin.val).SatisfiedBy table.semigroup
  exact table.checkIdentityFusedNat_sound abaControlFin (by decide)

def xyzControl : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [1, 1, 1, 1, 2]⟩⟩

theorem xyzControl_invalid : ¬ xyzControl.SatisfiedBy table.semigroup := by
  intro valid
  let valuation : Nat → Fin 6 := fun letter => if letter = 0 then 4 else if letter = 1 then 2 else 3
  exact (by decide : table.semigroup.eval valuation xyzControl.lhs ≠
    table.semigroup.eval valuation xyzControl.rhs) (valid valuation)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5441

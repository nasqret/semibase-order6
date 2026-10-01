import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

/-! Literal S6_5595 and its unchanged O6F_0004/dual:4 eight-law contract.
Neither Condition4, HFB membership nor a bounded key is a completeness premise. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595

open SemigroupBasis

def law00 : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0]⟩⟩
def law01 : Identity Nat := ⟨⟨0, [0, 0, 1]⟩, ⟨0, [0, 1]⟩⟩
def law02 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def law03 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 0, 0]⟩⟩
def law04 : Identity Nat := ⟨⟨0, [0, 1, 1, 0]⟩, ⟨0, [0, 1, 1, 1]⟩⟩
def law05 : Identity Nat := ⟨⟨0, [0, 1, 1, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩
def law06 : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩
def law07 : Identity Nat := ⟨⟨0, [1, 0, 2]⟩, ⟨1, [0, 0, 2]⟩⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06, law07]

def displayedBasisSHA256 : String :=
  "676e182dc7f7dd5998fc845738114fdb6f6288a689324ce3fdbbca9ca6a932d8"

theorem basis_length : basis.length = 8 := rfl

def mul (left right : Fin 6) : Fin 6 :=
  if left = 5 then right
  else if left = 4 then
    if right = 1 then 1 else if right = 2 ∨ right = 3 then 2
    else if right = 4 ∨ right = 5 then 4 else 0
  else if left = 2 ∨ left = 3 then
    if right = 3 then 1 else if right = 5 then 2 else 0
  else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem table_rows_exact :
    (List.finRange 6).map (fun left => (List.finRange 6).map (fun right => (mul left right).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,0,0], [0,0,0,1,0,2],
       [0,0,0,1,0,2], [0,1,2,2,4,4], [0,1,2,3,4,5]] := by decide

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

theorem abaControl_invalid : ¬ abaControl.SatisfiedBy table.semigroup := by
  intro valid
  let valuation : Nat → Fin 6 := fun letter => if letter = 0 then 3 else 5
  exact (by decide : table.semigroup.eval valuation abaControl.lhs ≠
    table.semigroup.eval valuation abaControl.rhs) (valid valuation)

def xyzControl : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [1, 1, 1, 1, 2]⟩⟩

theorem xyzControl_invalid : ¬ xyzControl.SatisfiedBy table.semigroup := by
  intro valid
  let valuation : Nat → Fin 6 := fun letter => if letter = 0 then 4 else if letter = 1 then 2 else 3
  exact (by decide : table.semigroup.eval valuation xyzControl.lhs ≠
    table.semigroup.eval valuation xyzControl.rhs) (valid valuation)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595

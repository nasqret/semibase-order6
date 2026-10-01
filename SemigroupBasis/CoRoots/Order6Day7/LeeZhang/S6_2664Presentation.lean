import SemigroupBasis.FiniteReflection

/-!
# The exact displayed S6_2664 raw12 presentation

Family O6F_0002 in the authenticated direct16/direct17 packet is distinct
from the similarly named dual-C4 family. The ordered twelve-law digest is
`4970266ae59a81cebc226c09f9ee08f13dbbda1c01199596ff04b0c570a745df`.
The actual catalogue table is used, without relabelling or substituting
S6_1075. In particular, `xx = xxx` is false here.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2664

open SemigroupBasis

/-- `xxx = xxxx`. -/
def law00 : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0]⟩⟩
/-- `xxxy = xxy`. -/
def law01 : Identity Nat := ⟨⟨0, [0, 0, 1]⟩, ⟨0, [0, 1]⟩⟩
/-- `xxyx = xxyy`. -/
def law02 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩
/-- `xxyx = xyxx`. -/
def law03 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
/-- `xxyx = yxyx`. -/
def law04 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 1, 0]⟩⟩
/-- `xxyz = yxyz`. -/
def law05 : Identity Nat := ⟨⟨0, [0, 1, 2]⟩, ⟨1, [0, 1, 2]⟩⟩
/-- `xxyzx = xxyzy`. -/
def law06 : Identity Nat := ⟨⟨0, [0, 1, 2, 0]⟩, ⟨0, [0, 1, 2, 1]⟩⟩
/-- `xxyzx = xxyzz`. -/
def law07 : Identity Nat := ⟨⟨0, [0, 1, 2, 0]⟩, ⟨0, [0, 1, 2, 2]⟩⟩
/-- `xyx = xyyx`. -/
def law08 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩
/-- `xyy = xyyy`. -/
def law09 : Identity Nat := ⟨⟨0, [1, 1]⟩, ⟨0, [1, 1, 1]⟩⟩
/-- `xyyz = xyz`; the right side is square-free. -/
def law10 : Identity Nat := ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩
/-- `xyzx = xzyx`. -/
def law11 : Identity Nat := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10, law11]

def displayedBasisSHA256 : String :=
  "4970266ae59a81cebc226c09f9ee08f13dbbda1c01199596ff04b0c570a745df"

theorem basis_length : basis.length = 12 := rfl

def mul (left right : Fin 6) : Fin 6 :=
  if left = 5 then
    if right = 5 then 5 else if right = 2 ∨ right = 4 then 2 else 0
  else if left = 3 ∨ left = 4 then
    if right = 5 then 3 else if right = 2 ∨ right = 4 then 1 else 0
  else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- Exact unrelabelled zero-based catalogue rows. -/
theorem table_literal_exact :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map (fun right => (mul left right).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,0,0], [0,0,0,0,0,0],
       [0,0,1,0,1,3], [0,0,1,0,1,3], [0,0,2,0,2,5]] := by
  decide

private def toFin : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem raw_roundtrips :
    basis.all (fun identity =>
      decide ((identity.map toFin).map Fin.val = identity)) = true := by
  decide

private theorem raw_checks :
    basis.all (fun identity =>
      table.checkIdentityFused (identity.map toFin)) = true := by
  decide

/-- Soundness of exactly the displayed raw12, not a completeness field. -/
theorem models : Models table.semigroup basis := by
  intro identity member
  have roundtrip : (identity.map toFin).map Fin.val = identity :=
    of_decide_eq_true ((List.all_eq_true.mp raw_roundtrips) identity member)
  have valid := table.checkIdentityFusedNat_sound (identity.map toFin)
    ((List.all_eq_true.mp raw_checks) identity member)
  rw [roundtrip] at valid
  exact valid

def oldSquareLaw : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩

/-- The old S6_1075 doubleton preparation is not sound on this table. -/
theorem oldSquareLaw_invalid : ¬ oldSquareLaw.SatisfiedBy table.semigroup := by
  intro valid
  exact (by decide :
    table.semigroup.eval (fun _ => (4 : Fin 6)) oldSquareLaw.lhs ≠
      table.semigroup.eval (fun _ => (4 : Fin 6)) oldSquareLaw.rhs)
    (valid (fun _ => (4 : Fin 6)))

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2664

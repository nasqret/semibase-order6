import SemigroupBasis.FiniteReflection

/-!
# The exact displayed S6_1075 presentation

This is family O6F_0004 from the authenticated direct-16/direct-17 packet.
The ordered ten-law digest is
`94707ab34bdc7c489f069a386aadf4e5eb86aa77eb0f37fc79d7e470d0a84369`.
The table is the literal catalogue representative, with each entry decreased
by one. Condition membership is not used as a completeness premise.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_1075

open SemigroupBasis

/-- `xx = xxx`. -/
def law00 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
/-- `xxyx = xxyy`. -/
def law01 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩
/-- `xxyx = xyxx`. -/
def law02 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
/-- `xxyx = yxyx`. -/
def law03 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 1, 0]⟩⟩
/-- `xxyz = yxyz`. -/
def law04 : Identity Nat := ⟨⟨0, [0, 1, 2]⟩, ⟨1, [0, 1, 2]⟩⟩
/-- `xxyzx = xxyzy`. -/
def law05 : Identity Nat := ⟨⟨0, [0, 1, 2, 0]⟩, ⟨0, [0, 1, 2, 1]⟩⟩
/-- `xxyzx = xxyzz`. -/
def law06 : Identity Nat := ⟨⟨0, [0, 1, 2, 0]⟩, ⟨0, [0, 1, 2, 2]⟩⟩
/-- `xyx = xyyx`. -/
def law07 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩
/-- `xyyz = xyz`; its right side is square-free. -/
def law08 : Identity Nat := ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩
/-- `xyzx = xzyx`. -/
def law09 : Identity Nat := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09]

def displayedBasisSHA256 : String :=
  "94707ab34bdc7c489f069a386aadf4e5eb86aa77eb0f37fc79d7e470d0a84369"

def mul (left right : Fin 6) : Fin 6 :=
  if left = 5 then
    if right = 5 then 5 else if right = 2 ∨ right = 3 then 2 else 0
  else if left = 4 then
    if right = 5 then 4 else if right = 2 ∨ right = 3 then 1 else 0
  else if left = 3 then
    if right = 5 then 4 else if right = 2 then 1 else 0
  else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- Exact, unrelabelled zero-based catalogue table. -/
theorem table_literal_exact :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map (fun right => (mul left right).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,0,0], [0,0,0,0,0,0],
       [0,0,1,0,0,4], [0,0,1,1,0,4], [0,0,2,2,0,5]] := by
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

/-- Soundness of exactly the ten displayed laws, not a completeness claim. -/
theorem models : Models table.semigroup basis := by
  intro identity member
  have roundtrip : (identity.map toFin).map Fin.val = identity :=
    of_decide_eq_true ((List.all_eq_true.mp raw_roundtrips) identity member)
  have valid := table.checkIdentityFusedNat_sound (identity.map toFin)
    ((List.all_eq_true.mp raw_checks) identity member)
  rw [roundtrip] at valid
  exact valid

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_1075

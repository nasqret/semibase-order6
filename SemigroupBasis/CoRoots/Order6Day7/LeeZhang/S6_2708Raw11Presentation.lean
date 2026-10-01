import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2636Raw6Tables

/-!
# Exact S6_2708 raw11 and the separately proposed sigma12

The literal route4 packet has raw digest46ba0131, distinct from the
three-root raw6 presentation. Msg0410 stops its positive completeness
obligation. This module proves only exact-table facts and soundness of
the witness-augmented candidate; no candidate completeness is asserted.
The already kernel-green factorial-abcd model is reused unchanged.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708

open SemigroupBasis

/-- `xxx = xxxx`. -/
def law00 : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0]⟩⟩
/-- `xxxy = xxy`. -/
def law01 : Identity Nat := ⟨⟨0, [0, 0, 1]⟩, ⟨0, [0, 1]⟩⟩
/-- `xxyx = xyxx`. -/
def law02 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
/-- `xxyx = yxxx`. -/
def law03 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 0, 0]⟩⟩
/-- `xxyyx = xxyyy`. -/
def law04 : Identity Nat := ⟨⟨0, [0, 1, 1, 0]⟩, ⟨0, [0, 1, 1, 1]⟩⟩
/-- `xxyyz = xyyxz`. -/
def law05 : Identity Nat := ⟨⟨0, [0, 1, 1, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩
/-- `xyxy = yxxy`. -/
def law06 : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩
/-- `xyxz = yxxz`. -/
def law07 : Identity Nat := ⟨⟨0, [1, 0, 2]⟩, ⟨1, [0, 0, 2]⟩⟩
/-- `xyzx = xzyx`. -/
def law08 : Identity Nat := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩
/-- `xyzx = yxzx`. -/
def law09 : Identity Nat := ⟨⟨0, [1, 2, 0]⟩, ⟨1, [0, 2, 0]⟩⟩
/-- `xyzz = yxzz`. -/
def law10 : Identity Nat := ⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 2, 2]⟩⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10]

def displayedBasisSHA256 : String :=
  "46ba01314e80c5e3033fa80893d19969e701fa676dfbdd5929ff3d6a9c85a34a"

theorem basis_length : basis.length = 11 := rfl

/-- Exact shared prefix swap: alphabetical t,x,y,z ->0,1,2,3. -/
abbrev missingPrefixSwap : Identity Nat := DualC4Raw6.missingPrefixSwap

private def missingPrefixSwapFin : Identity (Fin 4) :=
  ⟨⟨1, [2, 3, 0]⟩, ⟨2, [1, 3, 0]⟩⟩

theorem missingPrefixSwapFin_map : missingPrefixSwapFin.map Fin.val = missingPrefixSwap := rfl

def sigma12 : List (Identity Nat) := basis ++ [missingPrefixSwap]

def proposedSigma12SHA256 : String :=
  "c9df3c465c4836654ba8448a97ecc169c19ff43788969aea8425369016ecf966"

theorem sigma12_length : sigma12.length = 12 := rfl

def mul (left right : Fin 6) : Fin 6 :=
  if left = 2 ∨ left = 4 then
    if right = 4 then 1 else if right = 5 then 3 else 0
  else if left = 3 then
    if right = 2 ∨ right = 4 then 1 else if right = 5 then 3 else 0
  else if left = 5 then
    if right = 1 then 1 else if right = 2 ∨ right = 4 then 4
    else if right = 3 then 3 else if right = 5 then 5 else 0
  else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem table_rows_exact :
    (List.finRange 6).map (fun left => (List.finRange 6).map (fun right => (mul left right).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,0,0], [0,0,0,0,1,3],
       [0,0,1,0,1,3], [0,0,0,0,1,3], [0,1,4,3,4,5]] := by decide

private def toFin : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem raw_roundtrips :
    basis.all (fun identity => decide ((identity.map toFin).map Fin.val = identity)) = true := by
  decide

private theorem models_of_checked (T : FiniteTable)
    (checked : basis.all (fun identity => T.checkIdentityFused (identity.map toFin)) = true) :
    Models T.semigroup basis := by
  intro identity member
  have roundtrip : (identity.map toFin).map Fin.val = identity :=
    of_decide_eq_true ((List.all_eq_true.mp raw_roundtrips) identity member)
  have valid := T.checkIdentityFusedNat_sound (identity.map toFin)
    ((List.all_eq_true.mp checked) identity member)
  rw [roundtrip] at valid
  exact valid

theorem models_raw : Models table.semigroup basis := models_of_checked table (by decide)

theorem models_opposite_raw : Models table.semigroup.opposite (reversedBasis basis) :=
  models_raw.oppositeReversed

theorem missingPrefixSwap_valid : missingPrefixSwap.SatisfiedBy table.semigroup := by
  rw [← missingPrefixSwapFin_map]
  exact table.checkIdentityFusedNat_sound missingPrefixSwapFin (by decide)

/-- Soundness only; this is not an unrestricted completeness field. -/
theorem models_sigma12 : Models table.semigroup sigma12 := by
  intro identity member
  simp only [sigma12, List.mem_append, List.mem_singleton] at member
  rcases member with old | rfl
  · exact models_raw identity old
  · exact missingPrefixSwap_valid

theorem models_opposite_sigma12 :
    Models table.semigroup.opposite (reversedBasis sigma12) := models_sigma12.oppositeReversed

-- Separate closed reflection lemmas keep peak kernel memory bounded.
private theorem countermodel_checked00 :
    DualC4Raw6.Countermodel.table.checkIdentityFused (law00.map toFin) = true := by decide
private theorem countermodel_checked01 :
    DualC4Raw6.Countermodel.table.checkIdentityFused (law01.map toFin) = true := by decide
private theorem countermodel_checked02 :
    DualC4Raw6.Countermodel.table.checkIdentityFused (law02.map toFin) = true := by decide
private theorem countermodel_checked03 :
    DualC4Raw6.Countermodel.table.checkIdentityFused (law03.map toFin) = true := by decide
private theorem countermodel_checked04 :
    DualC4Raw6.Countermodel.table.checkIdentityFused (law04.map toFin) = true := by decide
private theorem countermodel_checked05 :
    DualC4Raw6.Countermodel.table.checkIdentityFused (law05.map toFin) = true := by decide
private theorem countermodel_checked06 :
    DualC4Raw6.Countermodel.table.checkIdentityFused (law06.map toFin) = true := by decide
private theorem countermodel_checked07 :
    DualC4Raw6.Countermodel.table.checkIdentityFused (law07.map toFin) = true := by decide
private theorem countermodel_checked08 :
    DualC4Raw6.Countermodel.table.checkIdentityFused (law08.map toFin) = true := by decide
private theorem countermodel_checked09 :
    DualC4Raw6.Countermodel.table.checkIdentityFused (law09.map toFin) = true := by decide
private theorem countermodel_checked10 :
    DualC4Raw6.Countermodel.table.checkIdentityFused (law10.map toFin) = true := by decide

/-- The existing explicit model satisfies this DIFFERENT eleven-law presentation. -/
theorem countermodel_models_raw : Models DualC4Raw6.Countermodel.table.semigroup basis :=
  models_of_checked DualC4Raw6.Countermodel.table (by
    simp only [basis, List.all_cons, List.all_nil, countermodel_checked00, countermodel_checked01,
      countermodel_checked02, countermodel_checked03, countermodel_checked04, countermodel_checked05,
      countermodel_checked06, countermodel_checked07, countermodel_checked08, countermodel_checked09,
      countermodel_checked10, Bool.true_and])

/-- The old three-root raw6 law is false here; do not transport that family by name. -/
theorem foreignRaw6Law_invalid : ¬ DualC4Raw6.law04.SatisfiedBy table.semigroup := by
  intro valid
  let valuation : Nat → Fin 6 := fun letter => if letter = 0 then 2 else 5
  exact (by decide : table.semigroup.eval valuation DualC4Raw6.law04.lhs ≠
    table.semigroup.eval valuation DualC4Raw6.law04.rhs) (valid valuation)

theorem oldAmbientPower_invalid : ¬ DualC4Raw6.oldAmbientPower.SatisfiedBy table.semigroup := by
  intro valid
  exact (by decide :
    table.semigroup.eval (fun _ => (4 : Fin 6)) DualC4Raw6.oldAmbientPower.lhs ≠
      table.semigroup.eval (fun _ => (4 : Fin 6)) DualC4Raw6.oldAmbientPower.rhs)
    (valid (fun _ => (4 : Fin 6)))

def abaControl : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [0, 0, 0, 1, 0]⟩

theorem abaControl_invalid : ¬ abaControl.SatisfiedBy table.semigroup := by
  intro valid
  let valuation : Nat → Fin 6 := fun letter => if letter = 0 then 2 else 5
  exact (by decide : table.semigroup.eval valuation abaControl.lhs ≠
    table.semigroup.eval valuation abaControl.rhs) (valid valuation)

def xyzControl : Identity Nat := ⟨Word.mk 0 [1, 2], Word.mk 0 [1, 1, 1, 1, 2]⟩

theorem xyzControl_invalid : ¬ xyzControl.SatisfiedBy table.semigroup := by
  intro valid
  let valuation : Nat → Fin 6 := fun letter => if letter = 0 then 5 else if letter = 1 then 2 else 4
  exact (by decide : table.semigroup.eval valuation xyzControl.lhs ≠
    table.semigroup.eval valuation xyzControl.rhs) (valid valuation)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708

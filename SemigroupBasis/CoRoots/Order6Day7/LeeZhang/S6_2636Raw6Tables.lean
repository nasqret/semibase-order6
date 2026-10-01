import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

/-!
# Exact tables and raw6 soundness for the dual-Condition-4 family

The unchanged O6F_0002 presentation belongs to the authenticated
`order6-lz-c4-o6f0002-i3` packet. Its ordered digest is
`0c9433e7ee05da85af181444ff977bda81e8602bbbc49c430bbeb808904af80f`.
All three literal catalogue representatives validate the raw laws and the
missing linear prefix swap. A concrete eleven-element semigroup validates
the raw laws but fails that swap. No completeness premise is introduced.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.DualC4Raw6

open SemigroupBasis

/-- `xxx = xxxx`; x -> 0. -/
def law00 : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0]⟩⟩
/-- `xxxy = xxy`; x -> 0, y -> 1. -/
def law01 : Identity Nat := ⟨⟨0, [0, 0, 1]⟩, ⟨0, [0, 1]⟩⟩
/-- `xxyyx = xxyyy`; x -> 0, y -> 1. -/
def law02 : Identity Nat := ⟨⟨0, [0, 1, 1, 0]⟩, ⟨0, [0, 1, 1, 1]⟩⟩
/-- `xxyyz = xyyxz`; x -> 0, y -> 1, z -> 2. -/
def law03 : Identity Nat := ⟨⟨0, [0, 1, 1, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩
/-- `xyx = yxx`; x -> 0, y -> 1. -/
def law04 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩
/-- `xyzx = xzyx`; x -> 0, y -> 1, z -> 2. -/
def law05 : Identity Nat := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05]

def displayedBasisSHA256 : String :=
  "0c9433e7ee05da85af181444ff977bda81e8602bbbc49c430bbeb808904af80f"

theorem displayedBasis_length : basis.length = 6 := rfl

/-- `xyzt = yxzt`; independent alphabetical normalization: t -> 0,
x -> 1, y -> 2, z -> 3, matching the exact screen's variable order. -/
def missingPrefixSwap : Identity Nat := ⟨⟨1, [2, 3, 0]⟩, ⟨2, [1, 3, 0]⟩⟩

private def missingPrefixSwapFin : Identity (Fin 4) :=
  ⟨⟨1, [2, 3, 0]⟩, ⟨2, [1, 3, 0]⟩⟩

theorem missingPrefixSwapFin_map : missingPrefixSwapFin.map Fin.val = missingPrefixSwap := rfl

/-- The existing three-law ambient kernel's power law is not valid here. -/
def oldAmbientPower : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

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

namespace S6_2636

def mul (left right : Fin 6) : Fin 6 :=
  if left = 3 then
    if right = 4 then 1 else if right = 5 then 3 else 0
  else if left = 4 then
    if right = 2 ∨ right = 4 then 1 else if right = 5 then 3 else 0
  else if left = 5 then
    if right = 1 then 1 else if right = 3 then 3 else if right = 4 then 4 else if right = 5 then 5 else 0
  else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem table_rows_exact :
    (List.finRange 6).map (fun left => (List.finRange 6).map (fun right => (mul left right).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,0,0], [0,0,0,0,0,0],
       [0,0,0,0,1,3], [0,0,1,0,1,3], [0,1,0,3,4,5]] := by decide

theorem models_raw : Models table.semigroup basis := models_of_checked table (by decide)

theorem models_opposite_raw : Models table.semigroup.opposite (reversedBasis basis) :=
  models_raw.oppositeReversed

theorem missingPrefixSwap_valid : missingPrefixSwap.SatisfiedBy table.semigroup := by
  rw [← missingPrefixSwapFin_map]
  exact table.checkIdentityFusedNat_sound missingPrefixSwapFin (by decide)

theorem oldAmbientPower_invalid : ¬ oldAmbientPower.SatisfiedBy table.semigroup := by
  intro valid
  have unequal := valid (fun _ => (4 : Fin 6))
  change (1 : Fin 6) = 0 at unequal
  exact (by decide : (1 : Fin 6) ≠ 0) unequal

end S6_2636

namespace S6_2637

def mul (left right : Fin 6) : Fin 6 :=
  if left = 3 then
    if right = 4 then 1 else if right = 5 then 3 else 0
  else if left = 4 then
    if right = 2 ∨ right = 4 then 1 else if right = 5 then 3 else 0
  else if left = 5 then
    if right = 1 ∨ right = 2 then 1 else if right = 3 then 3 else if right = 4 then 4 else if right = 5 then 5 else 0
  else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem table_rows_exact :
    (List.finRange 6).map (fun left => (List.finRange 6).map (fun right => (mul left right).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,0,0], [0,0,0,0,0,0],
       [0,0,0,0,1,3], [0,0,1,0,1,3], [0,1,1,3,4,5]] := by decide

theorem models_raw : Models table.semigroup basis := models_of_checked table (by decide)

theorem models_opposite_raw : Models table.semigroup.opposite (reversedBasis basis) :=
  models_raw.oppositeReversed

theorem missingPrefixSwap_valid : missingPrefixSwap.SatisfiedBy table.semigroup := by
  rw [← missingPrefixSwapFin_map]
  exact table.checkIdentityFusedNat_sound missingPrefixSwapFin (by decide)

theorem oldAmbientPower_invalid : ¬ oldAmbientPower.SatisfiedBy table.semigroup := by
  intro valid
  have unequal := valid (fun _ => (4 : Fin 6))
  change (1 : Fin 6) = 0 at unequal
  exact (by decide : (1 : Fin 6) ≠ 0) unequal

end S6_2637

namespace S6_2705

def mul (left right : Fin 6) : Fin 6 :=
  if left = 2 ∨ left = 3 then
    if right = 4 then 1 else if right = 5 then 2 else 0
  else if left = 4 then
    if right = 3 ∨ right = 4 then 1 else if right = 5 then 2 else 0
  else if left = 5 then
    if right = 1 then 1 else if right = 2 ∨ right = 3 then 2 else if right = 4 then 4 else if right = 5 then 5 else 0
  else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem table_rows_exact :
    (List.finRange 6).map (fun left => (List.finRange 6).map (fun right => (mul left right).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,0,0], [0,0,0,0,1,2],
       [0,0,0,0,1,2], [0,0,0,1,1,2], [0,1,2,2,4,5]] := by decide

theorem models_raw : Models table.semigroup basis := models_of_checked table (by decide)

theorem models_opposite_raw : Models table.semigroup.opposite (reversedBasis basis) :=
  models_raw.oppositeReversed

theorem missingPrefixSwap_valid : missingPrefixSwap.SatisfiedBy table.semigroup := by
  rw [← missingPrefixSwapFin_map]
  exact table.checkIdentityFusedNat_sound missingPrefixSwapFin (by decide)

theorem oldAmbientPower_invalid : ¬ oldAmbientPower.SatisfiedBy table.semigroup := by
  intro valid
  have unequal := valid (fun _ => (4 : Fin 6))
  change (1 : Fin 6) = 0 at unequal
  exact (by decide : (1 : Fin 6) ≠ 0) unequal

end S6_2705

namespace Countermodel

/-- The zero plus the ten nonempty factors of the square-free word abcd. -/
def mul (left right : Fin 11) : Fin 11 :=
  if left = 1 then
    if right = 2 then 5 else if right = 6 then 8 else if right = 9 then 10 else 0
  else if left = 2 then
    if right = 3 then 6 else if right = 7 then 9 else 0
  else if left = 3 then
    if right = 4 then 7 else 0
  else if left = 5 then
    if right = 3 then 8 else if right = 7 then 10 else 0
  else if left = 6 then
    if right = 4 then 9 else 0
  else if left = 8 then
    if right = 4 then 10 else 0
  else 0

def table : FiniteTable where
  order := 11
  mul := mul
  assoc := by decide

theorem table_rows_exact :
    (List.finRange 11).map (fun left => (List.finRange 11).map (fun right => (mul left right).val)) =
      [[0,0,0,0,0,0,0,0,0,0,0], [0,0,5,0,0,0,8,0,0,10,0],
       [0,0,0,6,0,0,0,9,0,0,0], [0,0,0,0,7,0,0,0,0,0,0],
       [0,0,0,0,0,0,0,0,0,0,0], [0,0,0,8,0,0,0,10,0,0,0],
       [0,0,0,0,9,0,0,0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0],
       [0,0,0,0,10,0,0,0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0],
       [0,0,0,0,0,0,0,0,0,0,0]] := by decide

theorem models_raw : Models table.semigroup basis := models_of_checked table (by decide)

/-- Alphabetical (t,x,y,z) -> (4,1,2,3), hence x=a,y=b,z=c,t=d. -/
def valuation : Nat → Fin 11
  | 0 => 4
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0

theorem missingPrefixSwap_fails : missingPrefixSwap.FailsAt table.semigroup valuation := by
  change (10 : Fin 11) ≠ 0
  decide

theorem missingPrefixSwap_invalid : ¬ missingPrefixSwap.SatisfiedBy table.semigroup :=
  Identity.not_satisfiedBy_of_failsAt missingPrefixSwap_fails

end Countermodel

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.DualC4Raw6

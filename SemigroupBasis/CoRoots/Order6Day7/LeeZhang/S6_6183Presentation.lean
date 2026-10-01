import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

/-! The authenticated literal S6_6183 table and unchanged O6F_0007 raw7.
Its dual Condition4/HFB labels are not exact-basis completeness premises.
The original MAX7/MAX8 screen is an under-approximation: its first displayed
gaps are word-substitution instances of law01, proved in the next module. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183

open SemigroupBasis

def law00 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def law01 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def law02 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
def law03 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
def law04 : Identity Nat := ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 0, 2, 1]⟩⟩
def law05 : Identity Nat := ⟨⟨0, [1, 0, 2]⟩, ⟨1, [0, 0, 2]⟩⟩
def law06 : Identity Nat := ⟨⟨0, [1, 1]⟩, ⟨1, [0, 1, 1]⟩⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06]
def displayedBasisSHA256 : String :=
  "9002fa5d85afe84657a11adde76a33526f5a7799d89d973b83452370b47b176a"
def literalTableSHA256 : String :=
  "816a6adfc81ee9a247c0590143c0d3f2e6b5e6dcd48efd3e3ea1eb82ed18e5af"

theorem basis_length : basis.length = 7 := rfl

def mul (left right : Fin 6) : Fin 6 :=
  if left = 5 then right
  else if left = 3 ∨ left = 4 then
    if right = 4 ∨ right = 5 then 3 else right
  else if left = 2 then
    if right = 4 then 1 else if right = 5 then 2 else 0
  else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem table_rows_exact :
    (List.finRange 6).map (fun left => (List.finRange 6).map (fun right => (mul left right).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,0,0], [0,0,0,0,1,2],
       [0,1,2,3,3,3], [0,1,2,3,3,3], [0,1,2,3,4,5]] := by decide

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

def bandPower : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, []⟩⟩
theorem bandPower_invalid : ¬bandPower.SatisfiedBy table.semigroup := by
  intro valid
  have equal := valid (fun _ => (1 : Fin 6))
  change (0 : Fin 6) = 1 at equal
  exact (by decide : (0 : Fin 6) ≠ 1) equal

def commutation : Identity Nat := ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩
theorem commutation_invalid : ¬commutation.SatisfiedBy table.semigroup := by
  intro valid
  let valuation : Nat → Fin 6 := fun letter => if letter = 0 then 1 else 3
  exact (by decide : table.semigroup.eval valuation commutation.lhs ≠
    table.semigroup.eval valuation commutation.rhs) (valid valuation)

def terminalAbsorption : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
theorem terminalAbsorption_invalid : ¬terminalAbsorption.SatisfiedBy table.semigroup := by
  intro valid
  let valuation : Nat → Fin 6 := fun letter => if letter = 0 then 4 else 2
  exact (by decide : table.semigroup.eval valuation terminalAbsorption.lhs ≠
    table.semigroup.eval valuation terminalAbsorption.rhs) (valid valuation)

def Raw7Completeness : Prop :=
  ∀ identity : Identity Nat, identity.SatisfiedBy table.semigroup →
    Derives basis identity.lhs identity.rhs

def Raw7BothOrientations : Prop :=
  Raw7Completeness ∧ ∀ identity : Identity Nat, identity.SatisfiedBy table.semigroup.opposite →
    Derives (reversedBasis basis) identity.lhs identity.rhs

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183

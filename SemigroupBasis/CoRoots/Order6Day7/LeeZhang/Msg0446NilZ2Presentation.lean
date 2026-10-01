import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.Examples.CommutativeExponentFour
import SemigroupBasis.Subdirect

/-! Exact msg0446 presentations and literal-table maps. These are soundness,
factor, and countermodel results; no unrestricted basis endpoint is asserted.
Variables retain x=0, y=1, z=2. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0446NilZ2

open SemigroupBasis

def law00 : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0, 0]⟩⟩
def law01 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨1, [0, 0]⟩⟩
def law02 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
def law03 : Identity Nat := ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 0, 2, 1]⟩⟩
def law04 : Identity Nat := ⟨⟨0, [0, 1, 2, 1]⟩, ⟨1, [2, 0, 1, 0]⟩⟩
def law05 : Identity Nat := ⟨⟨0, [1, 2, 0, 1]⟩, ⟨0, [1, 2, 1, 0]⟩⟩
def law06 : Identity Nat := ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩
def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06]
def basisSHA256 : String := "f3f249b48ab1fef2e1c987492fccd99341b5c146b16c24b3c8220483c85949ea"
theorem basis_length : basis.length = 7 := rfl

def mul9386 (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then if b = 4 ∨ b = 5 then 1 else 0
  else if a = 2 then if b = 2 ∨ b = 3 then 1 else if b = 4 ∨ b = 5 then 2 else 0
  else if a = 3 then if b = 2 ∨ b = 3 then 1 else if b = 4 ∨ b = 5 then 3 else 0
  else if a = 4 then b
  else if b = 2 then 3 else if b = 3 then 2 else if b = 4 then 5 else if b = 5 then 4 else b

def table9386 : FiniteTable := ⟨6, mul9386, by decide⟩

theorem table9386_rows_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul9386 a b).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,1,1], [0,0,1,1,2,2],
       [0,0,1,1,3,3], [0,1,2,3,4,5], [0,1,3,2,5,4]] := by decide

def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem models9386 : Models table9386.semigroup basis :=
  FiniteCertificate.checkModels_sound table9386 basis toFinThree (by decide)

theorem oppositeModels9386 : Models table9386.semigroup.opposite (reversedBasis basis) :=
  models9386.oppositeReversed

abbrev m18Table := Generated.Catalogue.S5_254.table
abbrev exponentTable := Examples.commutativeExponentFour

/-- Collapse the degree-two element to zero, retaining the two nilpotents and units. -/
def m18Map9386 (a : Fin 6) : Fin 5 :=
  if a = 0 ∨ a = 1 then 0 else if a = 2 then 1 else if a = 3 then 2 else if a = 4 then 3 else 4

def m18Section9386 (a : Fin 5) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 2 else if a = 2 then 3 else if a = 3 then 4 else 5

/-- The existing S4_40 convention is reverse degree: 3 is the identity. -/
def exponentMap9386 (a : Fin 6) : Fin 4 :=
  if a = 4 ∨ a = 5 then 3 else if a = 2 ∨ a = 3 then 2 else if a = 1 then 1 else 0

def exponentSection9386 (a : Fin 4) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else 4

def m18Projection9386 : SplitSurjection table9386.semigroup m18Table.semigroup where
  toFun := m18Map9386
  map_mul := by decide
  preimage := m18Section9386
  right_inverse := by decide

def exponentProjection9386 : SplitSurjection table9386.semigroup exponentTable.semigroup where
  toFun := exponentMap9386
  map_mul := by decide
  preimage := exponentSection9386
  right_inverse := by decide

def subdirect9386 : SubdirectPair table9386.semigroup m18Table.semigroup exponentTable.semigroup where
  left := m18Projection9386
  right := exponentProjection9386
  jointlyInjective := by unfold Function.Injective; decide

/-- An unrestricted semantic equivalence, not a seven-law derivational converse. -/
theorem valid9386_iff_factors {α : Type} (identity : Identity α) :
    identity.SatisfiedBy table9386.semigroup ↔
      identity.SatisfiedBy m18Table.semigroup ∧ identity.SatisfiedBy exponentTable.semigroup :=
  subdirect9386.satisfiedBy_iff identity

theorem m18Models : Models m18Table.semigroup basis := by
  intro identity member
  exact m18Projection9386.pushforwardIdentity identity (models9386 identity member)

theorem exponentModels : Models exponentTable.semigroup basis := by
  intro identity member
  exact exponentProjection9386.pushforwardIdentity identity (models9386 identity member)

/-- M18's stronger power law cannot be imported into the new basis. -/
theorem m18_power_not_valid9386 :
    ¬ (⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩ : Identity Nat).SatisfiedBy table9386.semigroup := by
  intro valid
  have evaluated := valid (fun _ => (2 : Fin 6))
  change (1 : Fin 6) = 0 at evaluated
  exact (by decide : (1 : Fin 6) ≠ 0) evaluated

theorem m18_power_not_derivable9386 :
    ¬ Derives basis (⟨0, [0]⟩ : Word Nat) (⟨0, [0, 0, 0]⟩ : Word Nat) := by
  intro derivation
  exact m18_power_not_valid9386 (derivation.sound models9386)

namespace Ford

def law00 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩
def law01 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [0, 1, 0, 0]⟩⟩
def law02 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 0, 1, 0]⟩⟩
def law03 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩
def law04 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
def law05 : Identity Nat := ⟨⟨0, [0, 0, 1, 1]⟩, ⟨0, [0, 1, 1, 0]⟩⟩
def law06 : Identity Nat := ⟨⟨0, [0, 0, 1, 1]⟩, ⟨0, [1, 0, 0, 1]⟩⟩
def law07 : Identity Nat := ⟨⟨0, [0, 0, 1, 2]⟩, ⟨0, [1, 0, 0, 2]⟩⟩
def law08 : Identity Nat := ⟨⟨0, [0, 0, 1, 2]⟩, ⟨0, [1, 2, 0, 0]⟩⟩
def law09 : Identity Nat := ⟨⟨0, [0, 1, 1, 1]⟩, ⟨0, [1, 1, 0, 1]⟩⟩
def law10 : Identity Nat := ⟨⟨0, [0, 1, 1, 1]⟩, ⟨0, [1, 1, 1, 0]⟩⟩
def law11 : Identity Nat := ⟨⟨0, [0, 1, 1, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩
def law12 : Identity Nat := ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 0, 2, 1]⟩⟩
def law13 : Identity Nat := ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 0, 2]⟩⟩
def law14 : Identity Nat := ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩
def law15 : Identity Nat := ⟨⟨0, [1, 1, 1, 2]⟩, ⟨0, [1, 2, 1, 1]⟩⟩
def law16 : Identity Nat := ⟨⟨0, [1, 1, 2, 2]⟩, ⟨0, [1, 2, 2, 1]⟩⟩
def law17 : Identity Nat := ⟨⟨0, [1, 2, 0, 1]⟩, ⟨0, [1, 2, 1, 0]⟩⟩
def law18 : Identity Nat := ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1, 0, 0]⟩⟩
def law19 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09,
   law10, law11, law12, law13, law14, law15, law16, law17, law18, law19]
def basisSHA256 : String := "f6624a6d431d4df70e423a40ec9a0ddb39f4b9dc2225db0eb0d71f324024d4fe"
theorem basis_length : basis.length = 20 := rfl

def mul6543 (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then if b = 3 ∨ b = 4 then 1 else 0
  else if a = 2 then if b = 3 ∨ b = 4 then 2 else 0
  else if a = 3 then b
  else if a = 4 then
    if b = 1 then 2 else if b = 2 then 1 else if b = 3 then 4 else if b = 4 then 3 else b
  else 5

def mul6605 (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then if b = 3 then 1 else if b = 4 then 2 else 0
  else if a = 2 then if b = 3 then 2 else if b = 4 then 1 else 0
  else if a = 3 then b
  else if a = 4 then if b = 3 then 4 else if b = 4 then 3 else b
  else 5

def table6543 : FiniteTable := ⟨6, mul6543, by decide⟩
def table6605 : FiniteTable := ⟨6, mul6605, by decide⟩

theorem table6543_rows_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul6543 a b).val)) =
      [[0,0,0,0,0,0], [0,0,0,1,1,0], [0,0,0,2,2,0],
       [0,1,2,3,4,5], [0,2,1,4,3,5], [5,5,5,5,5,5]] := by decide
theorem table6605_rows_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul6605 a b).val)) =
      [[0,0,0,0,0,0], [0,0,0,1,2,0], [0,0,0,2,1,0],
       [0,1,2,3,4,5], [0,1,2,4,3,5], [5,5,5,5,5,5]] := by decide

theorem models6543 : Models table6543.semigroup basis :=
  FiniteCertificate.checkModels_sound table6543 basis toFinThree (by decide)
theorem models6605 : Models table6605.semigroup basis :=
  FiniteCertificate.checkModels_sound table6605 basis toFinThree (by decide)
theorem oppositeModels6543 : Models table6543.semigroup.opposite (reversedBasis basis) :=
  models6543.oppositeReversed
theorem oppositeModels6605 : Models table6605.semigroup.opposite (reversedBasis basis) :=
  models6605.oppositeReversed

def firstCopyInput : Word Nat := ⟨0, [0, 1]⟩
def firstCopyRender : Word Nat := ⟨0, [1, 0]⟩
def firstCopyValuation (letter : Nat) : Fin 6 := if letter = 0 then 4 else 1

theorem firstCopy_values6543 :
    table6543.semigroup.eval firstCopyValuation firstCopyInput = (1 : Fin 6) ∧
      table6543.semigroup.eval firstCopyValuation firstCopyRender = (2 : Fin 6) := by decide
theorem firstCopy_values6605 :
    table6605.semigroup.eval firstCopyValuation firstCopyInput = (1 : Fin 6) ∧
      table6605.semigroup.eval firstCopyValuation firstCopyRender = (2 : Fin 6) := by decide

theorem firstCopy_not_valid6543 :
    ¬ (⟨firstCopyInput, firstCopyRender⟩ : Identity Nat).SatisfiedBy table6543.semigroup := by
  intro valid
  have evaluated := valid firstCopyValuation
  rw [firstCopy_values6543.1, firstCopy_values6543.2] at evaluated
  exact (by decide : (1 : Fin 6) ≠ 2) evaluated
theorem firstCopy_not_valid6605 :
    ¬ (⟨firstCopyInput, firstCopyRender⟩ : Identity Nat).SatisfiedBy table6605.semigroup := by
  intro valid
  have evaluated := valid firstCopyValuation
  rw [firstCopy_values6605.1, firstCopy_values6605.2] at evaluated
  exact (by decide : (1 : Fin 6) ≠ 2) evaluated

theorem firstCopy_not_derivable : ¬ Derives basis firstCopyInput firstCopyRender := by
  intro derivation
  exact firstCopy_not_valid6543 (derivation.sound models6543)

end Ford
end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0446NilZ2

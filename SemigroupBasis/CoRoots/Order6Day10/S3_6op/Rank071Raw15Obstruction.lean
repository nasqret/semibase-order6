import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.Subdirect

/-!
# Rank071: the frozen fifteen-law S6_2979 candidate is incomplete

The eleven states are zero and all nonempty contiguous factors of abcd.
Every displayed-law endpoint repeats a variable, so every instance is zero
in this model. In contrast, xyzt is nonzero under x=a,y=b,z=c,t=d, while
xyyzt is zero. Both actual factors and the target validate that identity.
No extension law is added and no positive completeness attempt is made.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071Raw15Obstruction

open SemigroupBasis

def law00 : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 1, 0], Word.mk 0 [1, 0]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [0, 1, 1], Word.mk 0 [1, 0, 0]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [0, 1, 1], Word.mk 0 [1, 0, 1]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [0, 1, 1], Word.mk 1 [0, 0, 1]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [0, 1, 2, 2], Word.mk 0 [1, 0, 2, 2]⟩
def law06 : Identity Nat := ⟨Word.mk 0 [0, 1, 2, 2], Word.mk 0 [1, 2, 0, 1]⟩
def law07 : Identity Nat := ⟨Word.mk 0 [0, 1, 2, 2], Word.mk 0 [1, 2, 0, 2]⟩
def law08 : Identity Nat := ⟨Word.mk 0 [0, 1, 2, 2], Word.mk 0 [1, 2, 1, 0]⟩
def law09 : Identity Nat := ⟨Word.mk 0 [0, 1, 2, 2], Word.mk 0 [1, 2, 2, 0]⟩
def law10 : Identity Nat := ⟨Word.mk 0 [1, 0, 2], Word.mk 1 [0, 1, 2]⟩
def law11 : Identity Nat := ⟨Word.mk 0 [1, 0, 2, 0], Word.mk 0 [1, 2, 0]⟩
def law12 : Identity Nat := ⟨Word.mk 0 [1, 1, 2, 0], Word.mk 0 [1, 2, 0]⟩
def law13 : Identity Nat := ⟨Word.mk 0 [1, 2, 0], Word.mk 1 [1, 0, 2, 0]⟩
def law14 : Identity Nat := ⟨Word.mk 0 [1, 2, 2], Word.mk 0 [2, 1, 1]⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07,
    law08, law09, law10, law11, law12, law13, law14]

abbrev displayedBasisSHA256 : String :=
  "29d759e788c14fec27f7baa7499d40eb96e615d8acc04713496912420461f87b"

def leftTable : FiniteTable where
  order := 3
  mul first second := Generated.S3_6.table.mul second first
  assoc := by decide

theorem leftTable_is_actual_opposite :
    leftTable.semigroup = Generated.S3_6.table.semigroup.opposite := rfl

abbrev rightTable : FiniteTable := Generated.Catalogue.S5_240.table

/-- Exact zero-based S6_2979 table from the source-pinned contract. -/
def targetMul (first second : Fin 6) : Fin 6 :=
  if first = 2 then
    if second = 5 then 1 else 0
  else if first = 3 then
    if second = 4 ∨ second = 5 then 3 else 0
  else if first = 4 ∨ first = 5 then
    if second = 1 then 1 else if second = 2 then 2
    else if second = 4 ∨ second = 5 then 4 else 0
  else 0

def targetTable : FiniteTable where
  order := 6
  mul := targetMul
  assoc := by decide

theorem targetTable_exact :
    List.ofFn (fun first : Fin 6 => List.ofFn (fun second : Fin 6 =>
      (targetTable.mul first second).val)) =
    [[0,0,0,0,0,0], [0,0,0,0,0,0], [0,0,0,0,0,1],
      [0,0,0,0,3,3], [0,1,2,0,4,4], [0,1,2,0,4,4]] := by decide

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem basis_length : basis.length = 15 := by decide
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)
theorem modelsTarget : Models targetTable.semigroup basis :=
  FiniteCertificate.checkModels_sound targetTable basis toFinThree (by decide)

/-- States [zero,a,b,c,d,ab,bc,cd,abc,bcd,abcd]. -/
def counterMul (first second : Fin 11) : Fin 11 :=
  if first = 1 then
    if second = 2 then 5 else if second = 6 then 8 else if second = 9 then 10 else 0
  else if first = 2 then
    if second = 3 then 6 else if second = 7 then 9 else 0
  else if first = 3 then
    if second = 4 then 7 else 0
  else if first = 5 then
    if second = 3 then 8 else if second = 7 then 10 else 0
  else if first = 6 then
    if second = 4 then 9 else 0
  else if first = 8 then
    if second = 4 then 10 else 0
  else 0

def counterTable : FiniteTable where
  order := 11
  mul := counterMul
  assoc := by decide

theorem counterZeroLeft (value : Fin 11) : counterTable.semigroup.mul (0 : Fin 11) value = (0 : Fin 11) := by
  revert value
  decide

theorem counterZeroRight (value : Fin 11) : counterTable.semigroup.mul value (0 : Fin 11) = (0 : Fin 11) := by
  revert value
  decide

theorem counterSquareZero (value : Fin 11) : counterTable.semigroup.mul value value = (0 : Fin 11) := by
  revert value
  decide

theorem counterSandwichZero (first middle : Fin 11) :
    counterTable.semigroup.mul (counterTable.semigroup.mul first middle) first = (0 : Fin 11) := by
  revert first middle
  decide

theorem counterPrependZero {value : Fin 11} (zero : value = (0 : Fin 11)) (stem : Fin 11) :
    counterTable.semigroup.mul stem value = (0 : Fin 11) := by
  rw [zero]
  exact counterZeroRight stem

theorem counterAppendZero {value : Fin 11} (zero : value = (0 : Fin 11)) (tail : Fin 11) :
    counterTable.semigroup.mul value tail = (0 : Fin 11) := by
  rw [zero]
  exact counterZeroLeft tail

-- Each law below is discharged by the repeated-variable zero lemmas.
theorem counterTable_models_raw15 : Models counterTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro valuation
    have leftZero : counterTable.semigroup.eval valuation law00.lhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (valuation 0) (valuation 0)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterSquareZero (valuation 0)
    have rightZero : counterTable.semigroup.eval valuation law00.rhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 0)) (valuation 0)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSquareZero (valuation 0)) (valuation 0)
    exact leftZero.trans rightZero.symm
  · intro valuation
    have leftZero : counterTable.semigroup.eval valuation law01.lhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 0)) (valuation 1)) (valuation 0)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSquareZero (valuation 0)) (counterTable.semigroup.mul (valuation 1) (valuation 0))
    have rightZero : counterTable.semigroup.eval valuation law01.rhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 1)) (valuation 0)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterSandwichZero (valuation 0) (valuation 1)
    exact leftZero.trans rightZero.symm
  · intro valuation
    have leftZero : counterTable.semigroup.eval valuation law02.lhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 0)) (valuation 1)) (valuation 1)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSquareZero (valuation 0)) (counterTable.semigroup.mul (valuation 1) (valuation 1))
    have rightZero : counterTable.semigroup.eval valuation law02.rhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 1)) (valuation 0)) (valuation 0)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSandwichZero (valuation 0) (valuation 1)) (valuation 0)
    exact leftZero.trans rightZero.symm
  · intro valuation
    have leftZero : counterTable.semigroup.eval valuation law03.lhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 0)) (valuation 1)) (valuation 1)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSquareZero (valuation 0)) (counterTable.semigroup.mul (valuation 1) (valuation 1))
    have rightZero : counterTable.semigroup.eval valuation law03.rhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 1)) (valuation 0)) (valuation 1)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSandwichZero (valuation 0) (valuation 1)) (valuation 1)
    exact leftZero.trans rightZero.symm
  · intro valuation
    have leftZero : counterTable.semigroup.eval valuation law04.lhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 0)) (valuation 1)) (valuation 1)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSquareZero (valuation 0)) (counterTable.semigroup.mul (valuation 1) (valuation 1))
    have rightZero : counterTable.semigroup.eval valuation law04.rhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 1) (valuation 0)) (valuation 0)) (valuation 1)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterPrependZero (counterSquareZero (valuation 0)) (valuation 1)) (valuation 1)
    exact leftZero.trans rightZero.symm
  · intro valuation
    have leftZero : counterTable.semigroup.eval valuation law05.lhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 0)) (valuation 1)) (valuation 2)) (valuation 2)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSquareZero (valuation 0)) (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 1) (valuation 2)) (valuation 2))
    have rightZero : counterTable.semigroup.eval valuation law05.rhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 1)) (valuation 0)) (valuation 2)) (valuation 2)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSandwichZero (valuation 0) (valuation 1)) (counterTable.semigroup.mul (valuation 2) (valuation 2))
    exact leftZero.trans rightZero.symm
  · intro valuation
    have leftZero : counterTable.semigroup.eval valuation law06.lhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 0)) (valuation 1)) (valuation 2)) (valuation 2)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSquareZero (valuation 0)) (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 1) (valuation 2)) (valuation 2))
    have rightZero : counterTable.semigroup.eval valuation law06.rhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 1)) (valuation 2)) (valuation 0)) (valuation 1)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSandwichZero (valuation 0) (counterTable.semigroup.mul (valuation 1) (valuation 2))) (valuation 1)
    exact leftZero.trans rightZero.symm
  · intro valuation
    have leftZero : counterTable.semigroup.eval valuation law07.lhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 0)) (valuation 1)) (valuation 2)) (valuation 2)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSquareZero (valuation 0)) (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 1) (valuation 2)) (valuation 2))
    have rightZero : counterTable.semigroup.eval valuation law07.rhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 1)) (valuation 2)) (valuation 0)) (valuation 2)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSandwichZero (valuation 0) (counterTable.semigroup.mul (valuation 1) (valuation 2))) (valuation 2)
    exact leftZero.trans rightZero.symm
  · intro valuation
    have leftZero : counterTable.semigroup.eval valuation law08.lhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 0)) (valuation 1)) (valuation 2)) (valuation 2)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSquareZero (valuation 0)) (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 1) (valuation 2)) (valuation 2))
    have rightZero : counterTable.semigroup.eval valuation law08.rhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 1)) (valuation 2)) (valuation 1)) (valuation 0)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterPrependZero (counterSandwichZero (valuation 1) (valuation 2)) (valuation 0)) (valuation 0)
    exact leftZero.trans rightZero.symm
  · intro valuation
    have leftZero : counterTable.semigroup.eval valuation law09.lhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 0)) (valuation 1)) (valuation 2)) (valuation 2)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSquareZero (valuation 0)) (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 1) (valuation 2)) (valuation 2))
    have rightZero : counterTable.semigroup.eval valuation law09.rhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 1)) (valuation 2)) (valuation 2)) (valuation 0)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterPrependZero (counterSquareZero (valuation 2)) (counterTable.semigroup.mul (valuation 0) (valuation 1))) (valuation 0)
    exact leftZero.trans rightZero.symm
  · intro valuation
    have leftZero : counterTable.semigroup.eval valuation law10.lhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 1)) (valuation 0)) (valuation 2)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSandwichZero (valuation 0) (valuation 1)) (valuation 2)
    have rightZero : counterTable.semigroup.eval valuation law10.rhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 1) (valuation 0)) (valuation 1)) (valuation 2)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSandwichZero (valuation 1) (valuation 0)) (valuation 2)
    exact leftZero.trans rightZero.symm
  · intro valuation
    have leftZero : counterTable.semigroup.eval valuation law11.lhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 1)) (valuation 0)) (valuation 2)) (valuation 0)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSandwichZero (valuation 0) (valuation 1)) (counterTable.semigroup.mul (valuation 2) (valuation 0))
    have rightZero : counterTable.semigroup.eval valuation law11.rhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 1)) (valuation 2)) (valuation 0)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterSandwichZero (valuation 0) (counterTable.semigroup.mul (valuation 1) (valuation 2))
    exact leftZero.trans rightZero.symm
  · intro valuation
    have leftZero : counterTable.semigroup.eval valuation law12.lhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 1)) (valuation 1)) (valuation 2)) (valuation 0)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterPrependZero (counterSquareZero (valuation 1)) (valuation 0)) (counterTable.semigroup.mul (valuation 2) (valuation 0))
    have rightZero : counterTable.semigroup.eval valuation law12.rhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 1)) (valuation 2)) (valuation 0)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterSandwichZero (valuation 0) (counterTable.semigroup.mul (valuation 1) (valuation 2))
    exact leftZero.trans rightZero.symm
  · intro valuation
    have leftZero : counterTable.semigroup.eval valuation law13.lhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 1)) (valuation 2)) (valuation 0)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterSandwichZero (valuation 0) (counterTable.semigroup.mul (valuation 1) (valuation 2))
    have rightZero : counterTable.semigroup.eval valuation law13.rhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 1) (valuation 1)) (valuation 0)) (valuation 2)) (valuation 0)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterAppendZero (counterSquareZero (valuation 1)) (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 2)) (valuation 0))
    exact leftZero.trans rightZero.symm
  · intro valuation
    have leftZero : counterTable.semigroup.eval valuation law14.lhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 1)) (valuation 2)) (valuation 2)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterPrependZero (counterSquareZero (valuation 2)) (counterTable.semigroup.mul (valuation 0) (valuation 1))
    have rightZero : counterTable.semigroup.eval valuation law14.rhs = (0 : Fin 11) := by
      change (counterTable.semigroup.mul (counterTable.semigroup.mul (counterTable.semigroup.mul (valuation 0) (valuation 2)) (valuation 1)) (valuation 1)) = (0 : Fin 11)
      simpa only [counterTable.semigroup.assoc] using counterPrependZero (counterSquareZero (valuation 1)) (counterTable.semigroup.mul (valuation 0) (valuation 2))
    exact leftZero.trans rightZero.symm

def missingLaw : Identity Nat := ⟨Word.mk 0 [1, 2, 3], Word.mk 0 [1, 1, 2, 3]⟩

theorem missingLaw_leftValid : missingLaw.SatisfiedBy leftTable.semigroup := by
  have checked : Models leftTable.semigroup [missingLaw] :=
    FiniteCertificate.checkModels_sound leftTable [missingLaw] toFinFour (by decide)
  exact checked missingLaw (by decide)

theorem missingLaw_rightValid : missingLaw.SatisfiedBy rightTable.semigroup := by
  have checked : Models rightTable.semigroup [missingLaw] :=
    FiniteCertificate.checkModels_sound rightTable [missingLaw] toFinFour (by decide)
  exact checked missingLaw (by decide)

theorem missingLaw_targetValid : missingLaw.SatisfiedBy targetTable.semigroup := by
  have checked : Models targetTable.semigroup [missingLaw] :=
    FiniteCertificate.checkModels_sound targetTable [missingLaw] toFinFour (by decide)
  exact checked missingLaw (by decide)

def counterValuation : Nat → Fin 11
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | _ => 4

theorem counterEval_left :
    counterTable.semigroup.eval counterValuation missingLaw.lhs = (10 : Fin 11) := by decide
theorem counterEval_right :
    counterTable.semigroup.eval counterValuation missingLaw.rhs = (0 : Fin 11) := by decide

theorem missingLaw_counterInvalid : ¬ missingLaw.SatisfiedBy counterTable.semigroup := by
  intro valid
  have impossible : (10 : Fin 11) = (0 : Fin 11) := by
    simpa only [counterEval_left, counterEval_right] using valid counterValuation
  exact (by decide : (10 : Fin 11) ≠ 0) impossible

/-- The nonderivability is unrestricted, not a bounded search failure. -/
theorem missingLaw_not_derives : ¬ Derives basis missingLaw.lhs missingLaw.rhs := by
  intro derivation
  exact missingLaw_counterInvalid (derivation.sound counterTable_models_raw15)

def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup →
    identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem raw15_not_complete : ¬ Complete := by
  intro complete
  exact missingLaw_not_derives (complete missingLaw missingLaw_leftValid missingLaw_rightValid)

theorem raw15_no_intersectionBasis :
    ¬ IntersectionBasis leftTable.semigroup rightTable.semigroup basis := by
  intro intersection
  exact raw15_not_complete intersection.complete

theorem raw15_not_class_basis : ¬ BasisFor targetTable.semigroup basis := by
  intro complete
  exact missingLaw_not_derives (complete.2 missingLaw missingLaw_targetValid)

end SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071Raw15Obstruction

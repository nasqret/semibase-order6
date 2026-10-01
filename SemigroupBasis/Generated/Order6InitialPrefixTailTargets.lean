import SemigroupBasis.FiniteCertificate

namespace SemigroupBasis.Generated.Order6InitialPrefixTailTargets

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xyzu : Word Nat := w 0 [1, 2, 3]
def yxzu : Word Nat := w 1 [0, 2, 3]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def squareSwitchLaw : Identity Nat := ⟨xxyy, xyyx⟩
def gatherLaw : Identity Nat := ⟨xyx, yxx⟩
def squarefreeTailLaw : Identity Nat := ⟨xyzu, yxzu⟩
def anchoredTailLaw : Identity Nat := ⟨xyzx, xzyx⟩

/-- The exact displayed f9a3a2d6 basis on the nine representative tables. -/
def basis : List (Identity Nat) :=
  [powerLaw, squareSwitchLaw, gatherLaw, squarefreeTailLaw,
    anchoredTailLaw]

private def toFinOne : Nat → Fin 1 := fun _ => 0

private def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

namespace S6_1041

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,4],[1,1,2,1,1,1],[1,2,1,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 0
  | 1, 5 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 0
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 3
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 1
  | 4, 3 => 0
  | 4, 4 => 0
  | 4, 5 => 0
  | 5, 0 => 0
  | 5, 1 => 1
  | 5, 2 => 0
  | 5, 3 => 3
  | 5, 4 => 4
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e49d457c1bca0d576a8cd9fcce987ed520886d92a412c86c0aa809d4659bfd28"

abbrev semigroup : Semigroup (Fin 6) := table.semigroup

private def SwapProductPair (left right : Fin 6) : Prop :=
  left = right ∨
    (left = 0 ∧ right = 1) ∨
    (left = 0 ∧ right = 4) ∨
    (left = 1 ∧ right = 0) ∨
    (left = 4 ∧ right = 0)

private theorem swapProductPair_complete (left right : Fin 6) :
    SwapProductPair (mul left right) (mul right left) := by
  unfold SwapProductPair
  revert left right
  decide

private theorem swapProductPair_tail
    {left right : Fin 6} (pair : SwapProductPair left right)
    (suffixLeft suffixRight : Fin 6) :
    mul (mul left suffixLeft) suffixRight =
      mul (mul right suffixLeft) suffixRight := by
  rcases pair with equal | pair | pair | pair | pair
  · exact congrArg (fun value =>
      mul (mul value suffixLeft) suffixRight) equal
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide

private theorem squarefreeTailValid :
    squarefreeTailLaw.SatisfiedBy semigroup := by
  intro valuation
  change
    mul (mul (mul (valuation 0) (valuation 1))
      (valuation 2)) (valuation 3) =
    mul (mul (mul (valuation 1) (valuation 0))
      (valuation 2)) (valuation 3)
  exact swapProductPair_tail
    (swapProductPair_complete (valuation 0) (valuation 1))
    (valuation 2) (valuation 3)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsPower : Models semigroup [powerLaw] :=
  FiniteCertificate.checkModels_sound
    table [powerLaw] toFinOne (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsSquareSwitch :
    Models semigroup [squareSwitchLaw] :=
  FiniteCertificate.checkModels_sound
    table [squareSwitchLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsGather : Models semigroup [gatherLaw] :=
  FiniteCertificate.checkModels_sound
    table [gatherLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsAnchoredTail :
    Models semigroup [anchoredTailLaw] :=
  FiniteCertificate.checkModels_sound
    table [anchoredTailLaw] toFinThree (by decide)

theorem models : Models semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact modelsPower powerLaw (by simp)
  · exact modelsSquareSwitch squareSwitchLaw (by simp)
  · exact modelsGather gatherLaw (by simp)
  · exact squarefreeTailValid
  · exact modelsAnchoredTail anchoredTailLaw (by simp)

def capSelected : Fin 6 := 3
def secondHead : Fin 6 := 2
def secondSelected : Fin 6 := 4
def secondFiller : Fin 6 := 5
def secondAfterImmediate : Fin 6 := 1
def secondAfterLate : Fin 6 := 0
def secondAfterFiller : Fin 6 := 0

end S6_1041
namespace S6_1043

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,4],[1,1,2,1,1,1],[1,2,2,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 0
  | 1, 5 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 0
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 3
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 1
  | 4, 3 => 0
  | 4, 4 => 0
  | 4, 5 => 0
  | 5, 0 => 0
  | 5, 1 => 1
  | 5, 2 => 1
  | 5, 3 => 3
  | 5, 4 => 4
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "23214112a8828cb71a23e0f64c040ce68d69b10b611be1e7507d4b962cdf4945"

abbrev semigroup : Semigroup (Fin 6) := table.semigroup

private def SwapProductPair (left right : Fin 6) : Prop :=
  left = right ∨
    (left = 0 ∧ right = 1) ∨
    (left = 0 ∧ right = 4) ∨
    (left = 1 ∧ right = 0) ∨
    (left = 4 ∧ right = 0)

private theorem swapProductPair_complete (left right : Fin 6) :
    SwapProductPair (mul left right) (mul right left) := by
  unfold SwapProductPair
  revert left right
  decide

private theorem swapProductPair_tail
    {left right : Fin 6} (pair : SwapProductPair left right)
    (suffixLeft suffixRight : Fin 6) :
    mul (mul left suffixLeft) suffixRight =
      mul (mul right suffixLeft) suffixRight := by
  rcases pair with equal | pair | pair | pair | pair
  · exact congrArg (fun value =>
      mul (mul value suffixLeft) suffixRight) equal
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide

private theorem squarefreeTailValid :
    squarefreeTailLaw.SatisfiedBy semigroup := by
  intro valuation
  change
    mul (mul (mul (valuation 0) (valuation 1))
      (valuation 2)) (valuation 3) =
    mul (mul (mul (valuation 1) (valuation 0))
      (valuation 2)) (valuation 3)
  exact swapProductPair_tail
    (swapProductPair_complete (valuation 0) (valuation 1))
    (valuation 2) (valuation 3)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsPower : Models semigroup [powerLaw] :=
  FiniteCertificate.checkModels_sound
    table [powerLaw] toFinOne (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsSquareSwitch :
    Models semigroup [squareSwitchLaw] :=
  FiniteCertificate.checkModels_sound
    table [squareSwitchLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsGather : Models semigroup [gatherLaw] :=
  FiniteCertificate.checkModels_sound
    table [gatherLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsAnchoredTail :
    Models semigroup [anchoredTailLaw] :=
  FiniteCertificate.checkModels_sound
    table [anchoredTailLaw] toFinThree (by decide)

theorem models : Models semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact modelsPower powerLaw (by simp)
  · exact modelsSquareSwitch squareSwitchLaw (by simp)
  · exact modelsGather gatherLaw (by simp)
  · exact squarefreeTailValid
  · exact modelsAnchoredTail anchoredTailLaw (by simp)

def capSelected : Fin 6 := 3
def secondHead : Fin 6 := 2
def secondSelected : Fin 6 := 4
def secondFiller : Fin 6 := 5
def secondAfterImmediate : Fin 6 := 1
def secondAfterLate : Fin 6 := 0
def secondAfterFiller : Fin 6 := 1

end S6_1043
namespace S6_1045

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,4],[1,1,2,1,1,4],[1,2,1,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 0
  | 1, 5 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 0
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 3
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 1
  | 4, 3 => 0
  | 4, 4 => 0
  | 4, 5 => 3
  | 5, 0 => 0
  | 5, 1 => 1
  | 5, 2 => 0
  | 5, 3 => 3
  | 5, 4 => 4
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2607c39a78f2464af65ec4a1e4b5e3d5d8db678da81f3bbf5a9e19c8d9c55bd4"

abbrev semigroup : Semigroup (Fin 6) := table.semigroup

private def SwapProductPair (left right : Fin 6) : Prop :=
  left = right ∨
    (left = 0 ∧ right = 1) ∨
    (left = 1 ∧ right = 0) ∨
    (left = 3 ∧ right = 4) ∨
    (left = 4 ∧ right = 3)

private theorem swapProductPair_complete (left right : Fin 6) :
    SwapProductPair (mul left right) (mul right left) := by
  unfold SwapProductPair
  revert left right
  decide

private theorem swapProductPair_tail
    {left right : Fin 6} (pair : SwapProductPair left right)
    (suffixLeft suffixRight : Fin 6) :
    mul (mul left suffixLeft) suffixRight =
      mul (mul right suffixLeft) suffixRight := by
  rcases pair with equal | pair | pair | pair | pair
  · exact congrArg (fun value =>
      mul (mul value suffixLeft) suffixRight) equal
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide

private theorem squarefreeTailValid :
    squarefreeTailLaw.SatisfiedBy semigroup := by
  intro valuation
  change
    mul (mul (mul (valuation 0) (valuation 1))
      (valuation 2)) (valuation 3) =
    mul (mul (mul (valuation 1) (valuation 0))
      (valuation 2)) (valuation 3)
  exact swapProductPair_tail
    (swapProductPair_complete (valuation 0) (valuation 1))
    (valuation 2) (valuation 3)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsPower : Models semigroup [powerLaw] :=
  FiniteCertificate.checkModels_sound
    table [powerLaw] toFinOne (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsSquareSwitch :
    Models semigroup [squareSwitchLaw] :=
  FiniteCertificate.checkModels_sound
    table [squareSwitchLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsGather : Models semigroup [gatherLaw] :=
  FiniteCertificate.checkModels_sound
    table [gatherLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsAnchoredTail :
    Models semigroup [anchoredTailLaw] :=
  FiniteCertificate.checkModels_sound
    table [anchoredTailLaw] toFinThree (by decide)

theorem models : Models semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact modelsPower powerLaw (by simp)
  · exact modelsSquareSwitch squareSwitchLaw (by simp)
  · exact modelsGather gatherLaw (by simp)
  · exact squarefreeTailValid
  · exact modelsAnchoredTail anchoredTailLaw (by simp)

def capSelected : Fin 6 := 3
def secondHead : Fin 6 := 2
def secondSelected : Fin 6 := 4
def secondFiller : Fin 6 := 5
def secondAfterImmediate : Fin 6 := 1
def secondAfterLate : Fin 6 := 0
def secondAfterFiller : Fin 6 := 0

end S6_1045
namespace S6_1046

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,4],[1,1,2,1,1,4],[1,2,2,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 0
  | 1, 5 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 0
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 3
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 1
  | 4, 3 => 0
  | 4, 4 => 0
  | 4, 5 => 3
  | 5, 0 => 0
  | 5, 1 => 1
  | 5, 2 => 1
  | 5, 3 => 3
  | 5, 4 => 4
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "39cff1670959d4e54fa4e6c5585265ccec8f19d392a7acf3d72fa28953a79a20"

abbrev semigroup : Semigroup (Fin 6) := table.semigroup

private def SwapProductPair (left right : Fin 6) : Prop :=
  left = right ∨
    (left = 0 ∧ right = 1) ∨
    (left = 1 ∧ right = 0) ∨
    (left = 3 ∧ right = 4) ∨
    (left = 4 ∧ right = 3)

private theorem swapProductPair_complete (left right : Fin 6) :
    SwapProductPair (mul left right) (mul right left) := by
  unfold SwapProductPair
  revert left right
  decide

private theorem swapProductPair_tail
    {left right : Fin 6} (pair : SwapProductPair left right)
    (suffixLeft suffixRight : Fin 6) :
    mul (mul left suffixLeft) suffixRight =
      mul (mul right suffixLeft) suffixRight := by
  rcases pair with equal | pair | pair | pair | pair
  · exact congrArg (fun value =>
      mul (mul value suffixLeft) suffixRight) equal
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide

private theorem squarefreeTailValid :
    squarefreeTailLaw.SatisfiedBy semigroup := by
  intro valuation
  change
    mul (mul (mul (valuation 0) (valuation 1))
      (valuation 2)) (valuation 3) =
    mul (mul (mul (valuation 1) (valuation 0))
      (valuation 2)) (valuation 3)
  exact swapProductPair_tail
    (swapProductPair_complete (valuation 0) (valuation 1))
    (valuation 2) (valuation 3)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsPower : Models semigroup [powerLaw] :=
  FiniteCertificate.checkModels_sound
    table [powerLaw] toFinOne (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsSquareSwitch :
    Models semigroup [squareSwitchLaw] :=
  FiniteCertificate.checkModels_sound
    table [squareSwitchLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsGather : Models semigroup [gatherLaw] :=
  FiniteCertificate.checkModels_sound
    table [gatherLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsAnchoredTail :
    Models semigroup [anchoredTailLaw] :=
  FiniteCertificate.checkModels_sound
    table [anchoredTailLaw] toFinThree (by decide)

theorem models : Models semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact modelsPower powerLaw (by simp)
  · exact modelsSquareSwitch squareSwitchLaw (by simp)
  · exact modelsGather gatherLaw (by simp)
  · exact squarefreeTailValid
  · exact modelsAnchoredTail anchoredTailLaw (by simp)

def capSelected : Fin 6 := 3
def secondHead : Fin 6 := 2
def secondSelected : Fin 6 := 4
def secondFiller : Fin 6 := 5
def secondAfterImmediate : Fin 6 := 1
def secondAfterLate : Fin 6 := 0
def secondAfterFiller : Fin 6 := 1

end S6_1046
namespace S6_1062

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,2,4],[1,1,2,1,1,1],[1,2,1,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 0
  | 1, 5 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 0
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 1
  | 3, 5 => 3
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 1
  | 4, 3 => 0
  | 4, 4 => 0
  | 4, 5 => 0
  | 5, 0 => 0
  | 5, 1 => 1
  | 5, 2 => 0
  | 5, 3 => 3
  | 5, 4 => 4
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "488ee4adea94554b9c8f3c268e4922d2ba8fcb380d129ed21efdd1d988e38266"

abbrev semigroup : Semigroup (Fin 6) := table.semigroup

private def SwapProductPair (left right : Fin 6) : Prop :=
  left = right ∨
    (left = 0 ∧ right = 1) ∨
    (left = 0 ∧ right = 4) ∨
    (left = 1 ∧ right = 0) ∨
    (left = 4 ∧ right = 0)

private theorem swapProductPair_complete (left right : Fin 6) :
    SwapProductPair (mul left right) (mul right left) := by
  unfold SwapProductPair
  revert left right
  decide

private theorem swapProductPair_tail
    {left right : Fin 6} (pair : SwapProductPair left right)
    (suffixLeft suffixRight : Fin 6) :
    mul (mul left suffixLeft) suffixRight =
      mul (mul right suffixLeft) suffixRight := by
  rcases pair with equal | pair | pair | pair | pair
  · exact congrArg (fun value =>
      mul (mul value suffixLeft) suffixRight) equal
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide

private theorem squarefreeTailValid :
    squarefreeTailLaw.SatisfiedBy semigroup := by
  intro valuation
  change
    mul (mul (mul (valuation 0) (valuation 1))
      (valuation 2)) (valuation 3) =
    mul (mul (mul (valuation 1) (valuation 0))
      (valuation 2)) (valuation 3)
  exact swapProductPair_tail
    (swapProductPair_complete (valuation 0) (valuation 1))
    (valuation 2) (valuation 3)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsPower : Models semigroup [powerLaw] :=
  FiniteCertificate.checkModels_sound
    table [powerLaw] toFinOne (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsSquareSwitch :
    Models semigroup [squareSwitchLaw] :=
  FiniteCertificate.checkModels_sound
    table [squareSwitchLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsGather : Models semigroup [gatherLaw] :=
  FiniteCertificate.checkModels_sound
    table [gatherLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsAnchoredTail :
    Models semigroup [anchoredTailLaw] :=
  FiniteCertificate.checkModels_sound
    table [anchoredTailLaw] toFinThree (by decide)

theorem models : Models semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact modelsPower powerLaw (by simp)
  · exact modelsSquareSwitch squareSwitchLaw (by simp)
  · exact modelsGather gatherLaw (by simp)
  · exact squarefreeTailValid
  · exact modelsAnchoredTail anchoredTailLaw (by simp)

def capSelected : Fin 6 := 3
def secondHead : Fin 6 := 2
def secondSelected : Fin 6 := 4
def secondFiller : Fin 6 := 5
def secondAfterImmediate : Fin 6 := 1
def secondAfterLate : Fin 6 := 0
def secondAfterFiller : Fin 6 := 0

end S6_1062
namespace S6_1063

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,2,4],[1,1,2,1,1,1],[1,2,2,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 0
  | 1, 5 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 0
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 1
  | 3, 5 => 3
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 1
  | 4, 3 => 0
  | 4, 4 => 0
  | 4, 5 => 0
  | 5, 0 => 0
  | 5, 1 => 1
  | 5, 2 => 1
  | 5, 3 => 3
  | 5, 4 => 4
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5f69494f8d09d82d1c89d09d019d1a3e182236017f7ea4ee25a9f5ecb5f0fb29"

abbrev semigroup : Semigroup (Fin 6) := table.semigroup

private def SwapProductPair (left right : Fin 6) : Prop :=
  left = right ∨
    (left = 0 ∧ right = 1) ∨
    (left = 0 ∧ right = 4) ∨
    (left = 1 ∧ right = 0) ∨
    (left = 4 ∧ right = 0)

private theorem swapProductPair_complete (left right : Fin 6) :
    SwapProductPair (mul left right) (mul right left) := by
  unfold SwapProductPair
  revert left right
  decide

private theorem swapProductPair_tail
    {left right : Fin 6} (pair : SwapProductPair left right)
    (suffixLeft suffixRight : Fin 6) :
    mul (mul left suffixLeft) suffixRight =
      mul (mul right suffixLeft) suffixRight := by
  rcases pair with equal | pair | pair | pair | pair
  · exact congrArg (fun value =>
      mul (mul value suffixLeft) suffixRight) equal
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide

private theorem squarefreeTailValid :
    squarefreeTailLaw.SatisfiedBy semigroup := by
  intro valuation
  change
    mul (mul (mul (valuation 0) (valuation 1))
      (valuation 2)) (valuation 3) =
    mul (mul (mul (valuation 1) (valuation 0))
      (valuation 2)) (valuation 3)
  exact swapProductPair_tail
    (swapProductPair_complete (valuation 0) (valuation 1))
    (valuation 2) (valuation 3)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsPower : Models semigroup [powerLaw] :=
  FiniteCertificate.checkModels_sound
    table [powerLaw] toFinOne (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsSquareSwitch :
    Models semigroup [squareSwitchLaw] :=
  FiniteCertificate.checkModels_sound
    table [squareSwitchLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsGather : Models semigroup [gatherLaw] :=
  FiniteCertificate.checkModels_sound
    table [gatherLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsAnchoredTail :
    Models semigroup [anchoredTailLaw] :=
  FiniteCertificate.checkModels_sound
    table [anchoredTailLaw] toFinThree (by decide)

theorem models : Models semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact modelsPower powerLaw (by simp)
  · exact modelsSquareSwitch squareSwitchLaw (by simp)
  · exact modelsGather gatherLaw (by simp)
  · exact squarefreeTailValid
  · exact modelsAnchoredTail anchoredTailLaw (by simp)

def capSelected : Fin 6 := 3
def secondHead : Fin 6 := 2
def secondSelected : Fin 6 := 4
def secondFiller : Fin 6 := 5
def secondAfterImmediate : Fin 6 := 1
def secondAfterLate : Fin 6 := 0
def secondAfterFiller : Fin 6 := 1

end S6_1063
namespace S6_1100

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,1,1,1,1,3],[1,1,1,2,1,1],[1,2,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 0
  | 1, 5 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 2
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 2
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 1
  | 4, 4 => 0
  | 4, 5 => 0
  | 5, 0 => 0
  | 5, 1 => 1
  | 5, 2 => 2
  | 5, 3 => 2
  | 5, 4 => 4
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5aab94f099f4fa80668cdf43a81dbde0c8e0c4f39ce85bc6a5ac86e2a0906c7b"

abbrev semigroup : Semigroup (Fin 6) := table.semigroup

private def SwapProductPair (left right : Fin 6) : Prop :=
  left = right ∨
    (left = 0 ∧ right = 1) ∨
    (left = 0 ∧ right = 4) ∨
    (left = 1 ∧ right = 0) ∨
    (left = 4 ∧ right = 0)

private theorem swapProductPair_complete (left right : Fin 6) :
    SwapProductPair (mul left right) (mul right left) := by
  unfold SwapProductPair
  revert left right
  decide

private theorem swapProductPair_tail
    {left right : Fin 6} (pair : SwapProductPair left right)
    (suffixLeft suffixRight : Fin 6) :
    mul (mul left suffixLeft) suffixRight =
      mul (mul right suffixLeft) suffixRight := by
  rcases pair with equal | pair | pair | pair | pair
  · exact congrArg (fun value =>
      mul (mul value suffixLeft) suffixRight) equal
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide

private theorem squarefreeTailValid :
    squarefreeTailLaw.SatisfiedBy semigroup := by
  intro valuation
  change
    mul (mul (mul (valuation 0) (valuation 1))
      (valuation 2)) (valuation 3) =
    mul (mul (mul (valuation 1) (valuation 0))
      (valuation 2)) (valuation 3)
  exact swapProductPair_tail
    (swapProductPair_complete (valuation 0) (valuation 1))
    (valuation 2) (valuation 3)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsPower : Models semigroup [powerLaw] :=
  FiniteCertificate.checkModels_sound
    table [powerLaw] toFinOne (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsSquareSwitch :
    Models semigroup [squareSwitchLaw] :=
  FiniteCertificate.checkModels_sound
    table [squareSwitchLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsGather : Models semigroup [gatherLaw] :=
  FiniteCertificate.checkModels_sound
    table [gatherLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsAnchoredTail :
    Models semigroup [anchoredTailLaw] :=
  FiniteCertificate.checkModels_sound
    table [anchoredTailLaw] toFinThree (by decide)

theorem models : Models semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact modelsPower powerLaw (by simp)
  · exact modelsSquareSwitch squareSwitchLaw (by simp)
  · exact modelsGather gatherLaw (by simp)
  · exact squarefreeTailValid
  · exact modelsAnchoredTail anchoredTailLaw (by simp)

def capSelected : Fin 6 := 2
def secondHead : Fin 6 := 3
def secondSelected : Fin 6 := 4
def secondFiller : Fin 6 := 5
def secondAfterImmediate : Fin 6 := 1
def secondAfterLate : Fin 6 := 0
def secondAfterFiller : Fin 6 := 2

end S6_1100
namespace S6_1102

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,1,1,1,1,3],[1,1,1,2,1,3],[1,2,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 0
  | 1, 5 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 2
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 2
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 1
  | 4, 4 => 0
  | 4, 5 => 2
  | 5, 0 => 0
  | 5, 1 => 1
  | 5, 2 => 2
  | 5, 3 => 2
  | 5, 4 => 4
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "97620e1c18bcb71e0d8692ef9ccd11977c025c6262a61ab5bea59fec08d469e5"

abbrev semigroup : Semigroup (Fin 6) := table.semigroup

private def SwapProductPair (left right : Fin 6) : Prop :=
  left = right ∨
    (left = 0 ∧ right = 1) ∨
    (left = 1 ∧ right = 0) ∨
    (left = 2 ∧ right = 4) ∨
    (left = 4 ∧ right = 2)

private theorem swapProductPair_complete (left right : Fin 6) :
    SwapProductPair (mul left right) (mul right left) := by
  unfold SwapProductPair
  revert left right
  decide

private theorem swapProductPair_tail
    {left right : Fin 6} (pair : SwapProductPair left right)
    (suffixLeft suffixRight : Fin 6) :
    mul (mul left suffixLeft) suffixRight =
      mul (mul right suffixLeft) suffixRight := by
  rcases pair with equal | pair | pair | pair | pair
  · exact congrArg (fun value =>
      mul (mul value suffixLeft) suffixRight) equal
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide

private theorem squarefreeTailValid :
    squarefreeTailLaw.SatisfiedBy semigroup := by
  intro valuation
  change
    mul (mul (mul (valuation 0) (valuation 1))
      (valuation 2)) (valuation 3) =
    mul (mul (mul (valuation 1) (valuation 0))
      (valuation 2)) (valuation 3)
  exact swapProductPair_tail
    (swapProductPair_complete (valuation 0) (valuation 1))
    (valuation 2) (valuation 3)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsPower : Models semigroup [powerLaw] :=
  FiniteCertificate.checkModels_sound
    table [powerLaw] toFinOne (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsSquareSwitch :
    Models semigroup [squareSwitchLaw] :=
  FiniteCertificate.checkModels_sound
    table [squareSwitchLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsGather : Models semigroup [gatherLaw] :=
  FiniteCertificate.checkModels_sound
    table [gatherLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsAnchoredTail :
    Models semigroup [anchoredTailLaw] :=
  FiniteCertificate.checkModels_sound
    table [anchoredTailLaw] toFinThree (by decide)

theorem models : Models semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact modelsPower powerLaw (by simp)
  · exact modelsSquareSwitch squareSwitchLaw (by simp)
  · exact modelsGather gatherLaw (by simp)
  · exact squarefreeTailValid
  · exact modelsAnchoredTail anchoredTailLaw (by simp)

def capSelected : Fin 6 := 2
def secondHead : Fin 6 := 3
def secondSelected : Fin 6 := 4
def secondFiller : Fin 6 := 5
def secondAfterImmediate : Fin 6 := 1
def secondAfterLate : Fin 6 := 0
def secondAfterFiller : Fin 6 := 2

end S6_1102
namespace S6_1134

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,2,1],[1,1,2,1,1,4],[1,1,2,1,1,4],[1,2,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 0
  | 1, 5 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 1
  | 2, 5 => 0
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 2 => 1
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 3
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 1
  | 4, 3 => 0
  | 4, 4 => 0
  | 4, 5 => 3
  | 5, 0 => 0
  | 5, 1 => 1
  | 5, 2 => 2
  | 5, 3 => 3
  | 5, 4 => 3
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "43f05428ba3143d54dac1d73547b97febe9c73406cea293ea3e45da918164036"

abbrev semigroup : Semigroup (Fin 6) := table.semigroup

private def SwapProductPair (left right : Fin 6) : Prop :=
  left = right ∨
    (left = 0 ∧ right = 1) ∨
    (left = 0 ∧ right = 2) ∨
    (left = 1 ∧ right = 0) ∨
    (left = 2 ∧ right = 0)

private theorem swapProductPair_complete (left right : Fin 6) :
    SwapProductPair (mul left right) (mul right left) := by
  unfold SwapProductPair
  revert left right
  decide

private theorem swapProductPair_tail
    {left right : Fin 6} (pair : SwapProductPair left right)
    (suffixLeft suffixRight : Fin 6) :
    mul (mul left suffixLeft) suffixRight =
      mul (mul right suffixLeft) suffixRight := by
  rcases pair with equal | pair | pair | pair | pair
  · exact congrArg (fun value =>
      mul (mul value suffixLeft) suffixRight) equal
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide
  · rcases pair with ⟨rfl, rfl⟩
    revert suffixLeft suffixRight
    decide

private theorem squarefreeTailValid :
    squarefreeTailLaw.SatisfiedBy semigroup := by
  intro valuation
  change
    mul (mul (mul (valuation 0) (valuation 1))
      (valuation 2)) (valuation 3) =
    mul (mul (mul (valuation 1) (valuation 0))
      (valuation 2)) (valuation 3)
  exact swapProductPair_tail
    (swapProductPair_complete (valuation 0) (valuation 1))
    (valuation 2) (valuation 3)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsPower : Models semigroup [powerLaw] :=
  FiniteCertificate.checkModels_sound
    table [powerLaw] toFinOne (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsSquareSwitch :
    Models semigroup [squareSwitchLaw] :=
  FiniteCertificate.checkModels_sound
    table [squareSwitchLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsGather : Models semigroup [gatherLaw] :=
  FiniteCertificate.checkModels_sound
    table [gatherLaw] toFinTwo (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem modelsAnchoredTail :
    Models semigroup [anchoredTailLaw] :=
  FiniteCertificate.checkModels_sound
    table [anchoredTailLaw] toFinThree (by decide)

theorem models : Models semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact modelsPower powerLaw (by simp)
  · exact modelsSquareSwitch squareSwitchLaw (by simp)
  · exact modelsGather gatherLaw (by simp)
  · exact squarefreeTailValid
  · exact modelsAnchoredTail anchoredTailLaw (by simp)

def capSelected : Fin 6 := 3
def secondHead : Fin 6 := 4
def secondSelected : Fin 6 := 2
def secondFiller : Fin 6 := 5
def secondAfterImmediate : Fin 6 := 1
def secondAfterLate : Fin 6 := 0
def secondAfterFiller : Fin 6 := 3

end S6_1134
end SemigroupBasis.Generated.Order6InitialPrefixTailTargets

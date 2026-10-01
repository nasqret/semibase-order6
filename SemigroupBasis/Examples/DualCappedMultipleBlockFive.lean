import SemigroupBasis.Examples.DualCappedMultipleBlockFiveSyntax
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The zero-based multiplication table opposite to the stored `S5_209`
representative. This orientation has right identity `4` and is the natural
orientation for the block normal form. -/
def dualCappedMultipleBlockFiveMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then
    0
  else if a = 1 then
    if b = 0 then 0 else if b = 1 then 0 else
      if b = 2 then 0 else if b = 3 then 0 else 1
  else if a = 2 then
    if b = 0 then 0 else if b = 1 then 0 else
      if b = 2 then 0 else if b = 3 then 0 else 2
  else if a = 3 then
    if b = 0 then 0 else if b = 1 then 0 else
      if b = 2 then 0 else if b = 3 then 1 else 3
  else
    if b = 0 then 0 else if b = 1 then 1 else
      if b = 2 then 0 else if b = 3 then 3 else 4

def dualCappedMultipleBlockFive : FiniteTable where
  order := 5
  mul := dualCappedMultipleBlockFiveMul
  assoc := by decide

/-- The stored Smallsemi orientation of `S5_209`. -/
def dualCappedMultipleBlockFiveStoredMul (a b : Fin 5) : Fin 5 :=
  dualCappedMultipleBlockFiveMul b a

def dualCappedMultipleBlockFiveStored : FiniteTable where
  order := 5
  mul := dualCappedMultipleBlockFiveStoredMul
  assoc := by decide

private theorem dualCappedMultipleBlockFiveMul_power (a : Fin 5) :
    dualCappedMultipleBlockFiveMul
        (dualCappedMultipleBlockFiveMul a a) a =
      dualCappedMultipleBlockFiveMul
        (dualCappedMultipleBlockFiveMul
          (dualCappedMultipleBlockFiveMul a a) a) a := by
  decide +revert

private theorem dualCappedMultipleBlockFiveMul_gather (a b : Fin 5) :
    dualCappedMultipleBlockFiveMul
        (dualCappedMultipleBlockFiveMul a b) a =
      dualCappedMultipleBlockFiveMul
        (dualCappedMultipleBlockFiveMul a a) b := by
  decide +revert

private theorem dualCappedMultipleBlockFiveMul_suffixSwap
    (a b c : Fin 5) :
    dualCappedMultipleBlockFiveMul
        (dualCappedMultipleBlockFiveMul a b) c =
      dualCappedMultipleBlockFiveMul
        (dualCappedMultipleBlockFiveMul a c) b := by
  decide +revert

private theorem dualCappedMultipleBlockFiveMul_squareRotation
    (a b : Fin 5) :
    dualCappedMultipleBlockFiveMul
        (dualCappedMultipleBlockFiveMul
          (dualCappedMultipleBlockFiveMul b b) a) a =
      dualCappedMultipleBlockFiveMul
        (dualCappedMultipleBlockFiveMul
          (dualCappedMultipleBlockFiveMul a b) b) a := by
  decide +revert

theorem dualCappedMultipleBlockFiveBasis_models :
    Models dualCappedMultipleBlockFive.semigroup
      dualCappedMultipleBlockFiveBasis := by
  intro e he
  simp only [dualCappedMultipleBlockFiveBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · intro valuation
    change
      dualCappedMultipleBlockFiveMul
          (dualCappedMultipleBlockFiveMul
            (valuation 0) (valuation 0))
          (valuation 0) =
        dualCappedMultipleBlockFiveMul
          (dualCappedMultipleBlockFiveMul
            (dualCappedMultipleBlockFiveMul
              (valuation 0) (valuation 0))
            (valuation 0))
          (valuation 0)
    exact dualCappedMultipleBlockFiveMul_power (valuation 0)
  · intro valuation
    change
      dualCappedMultipleBlockFiveMul
          (dualCappedMultipleBlockFiveMul (valuation 0) (valuation 1))
          (valuation 0) =
        dualCappedMultipleBlockFiveMul
          (dualCappedMultipleBlockFiveMul (valuation 0) (valuation 0))
          (valuation 1)
    exact dualCappedMultipleBlockFiveMul_gather
      (valuation 0) (valuation 1)
  · intro valuation
    change
      dualCappedMultipleBlockFiveMul
          (dualCappedMultipleBlockFiveMul (valuation 0) (valuation 1))
          (valuation 2) =
        dualCappedMultipleBlockFiveMul
          (dualCappedMultipleBlockFiveMul (valuation 0) (valuation 2))
          (valuation 1)
    exact dualCappedMultipleBlockFiveMul_suffixSwap
      (valuation 0) (valuation 1) (valuation 2)
  · intro valuation
    change
      dualCappedMultipleBlockFiveMul
          (dualCappedMultipleBlockFiveMul
            (dualCappedMultipleBlockFiveMul
              (valuation 1) (valuation 1))
            (valuation 0))
          (valuation 0) =
        dualCappedMultipleBlockFiveMul
          (dualCappedMultipleBlockFiveMul
            (dualCappedMultipleBlockFiveMul
              (valuation 0) (valuation 1))
            (valuation 1))
          (valuation 0)
    exact dualCappedMultipleBlockFiveMul_squareRotation
      (valuation 0) (valuation 1)

private def dualCappedMultipleBlockFiveValuation
    (z : Nat) (witness : Fin 5) : Nat → Fin 5 :=
  fun x => if x = z then witness else 4

private theorem dualCappedMultipleBlockFiveMul_rightIdentity (a : Fin 5) :
    dualCappedMultipleBlockFiveMul a 4 = a := by
  decide +revert

private def dualCappedMultipleBlockFiveHeadHeadState
    (extra : Nat) : Fin 5 :=
  if extra = 0 then 2 else 0

private def dualCappedMultipleBlockFiveHeadOtherState
    (count : Nat) : Fin 5 :=
  if count = 0 then 4 else 0

private theorem dualCappedMultipleBlockFiveHeadHead_target (n : Nat) :
    dualCappedMultipleBlockFiveMul
        (dualCappedMultipleBlockFiveHeadHeadState n) 2 =
      dualCappedMultipleBlockFiveHeadHeadState (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [dualCappedMultipleBlockFiveHeadHeadState, hn,
      dualCappedMultipleBlockFiveMul]

private theorem dualCappedMultipleBlockFiveHeadOther_target (n : Nat) :
    dualCappedMultipleBlockFiveMul
        (dualCappedMultipleBlockFiveHeadOtherState n) 2 =
      dualCappedMultipleBlockFiveHeadOtherState (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [dualCappedMultipleBlockFiveHeadOtherState, hn,
      dualCappedMultipleBlockFiveMul]

private theorem dualCappedMultipleBlockFiveHeadHead_other (n : Nat) :
    dualCappedMultipleBlockFiveMul
        (dualCappedMultipleBlockFiveHeadHeadState n) 4 =
      dualCappedMultipleBlockFiveHeadHeadState n :=
  dualCappedMultipleBlockFiveMul_rightIdentity _

private theorem dualCappedMultipleBlockFiveHeadOther_other (n : Nat) :
    dualCappedMultipleBlockFiveMul
        (dualCappedMultipleBlockFiveHeadOtherState n) 4 =
      dualCappedMultipleBlockFiveHeadOtherState n :=
  dualCappedMultipleBlockFiveMul_rightIdentity _

private theorem dualCappedMultipleBlockFiveHeadHeadFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            dualCappedMultipleBlockFiveMul current
              (dualCappedMultipleBlockFiveValuation z 2 x))
          (dualCappedMultipleBlockFiveHeadHeadState n) =
        dualCappedMultipleBlockFiveHeadHeadState (n + xs.count z)
  | [], _ => by simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show dualCappedMultipleBlockFiveValuation z 2 z =
            (2 : Fin 5) by
          simp [dualCappedMultipleBlockFiveValuation]]
        rw [dualCappedMultipleBlockFiveHeadHead_target,
          dualCappedMultipleBlockFiveHeadHeadFold]
        rw [List.count_cons_self]
        congr 1
        omega
      · rw [show dualCappedMultipleBlockFiveValuation z 2 x =
            (4 : Fin 5) by
          simp [dualCappedMultipleBlockFiveValuation, hx]]
        rw [dualCappedMultipleBlockFiveHeadHead_other,
          dualCappedMultipleBlockFiveHeadHeadFold,
          List.count_cons_of_ne hx]

private theorem dualCappedMultipleBlockFiveHeadOtherFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            dualCappedMultipleBlockFiveMul current
              (dualCappedMultipleBlockFiveValuation z 2 x))
          (dualCappedMultipleBlockFiveHeadOtherState n) =
        dualCappedMultipleBlockFiveHeadOtherState (n + xs.count z)
  | [], _ => by simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show dualCappedMultipleBlockFiveValuation z 2 z =
            (2 : Fin 5) by
          simp [dualCappedMultipleBlockFiveValuation]]
        rw [dualCappedMultipleBlockFiveHeadOther_target,
          dualCappedMultipleBlockFiveHeadOtherFold]
        rw [List.count_cons_self]
        congr 1
        omega
      · rw [show dualCappedMultipleBlockFiveValuation z 2 x =
            (4 : Fin 5) by
          simp [dualCappedMultipleBlockFiveValuation, hx]]
        rw [dualCappedMultipleBlockFiveHeadOther_other,
          dualCappedMultipleBlockFiveHeadOtherFold,
          List.count_cons_of_ne hx]

private def dualCappedMultipleBlockFivePowerState (count : Nat) : Fin 5 :=
  if count = 0 then 4 else
    if count = 1 then 3 else
      if count = 2 then 1 else 0

private theorem dualCappedMultipleBlockFivePower_target (n : Nat) :
    dualCappedMultipleBlockFiveMul
        (dualCappedMultipleBlockFivePowerState n) 3 =
      dualCappedMultipleBlockFivePowerState (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · by_cases hn2 : n = 2
      · subst n
        rfl
      · have hnext2 : n + 1 ≠ 2 := by omega
        simp [dualCappedMultipleBlockFivePowerState, hn0, hn1, hn2,
          hnext2, dualCappedMultipleBlockFiveMul]

private theorem dualCappedMultipleBlockFivePower_other (n : Nat) :
    dualCappedMultipleBlockFiveMul
        (dualCappedMultipleBlockFivePowerState n) 4 =
      dualCappedMultipleBlockFivePowerState n :=
  dualCappedMultipleBlockFiveMul_rightIdentity _

private theorem dualCappedMultipleBlockFivePowerFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            dualCappedMultipleBlockFiveMul current
              (dualCappedMultipleBlockFiveValuation z 3 x))
          (dualCappedMultipleBlockFivePowerState n) =
        dualCappedMultipleBlockFivePowerState (n + xs.count z)
  | [], _ => by simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show dualCappedMultipleBlockFiveValuation z 3 z =
            (3 : Fin 5) by
          simp [dualCappedMultipleBlockFiveValuation]]
        rw [dualCappedMultipleBlockFivePower_target,
          dualCappedMultipleBlockFivePowerFold]
        rw [List.count_cons_self]
        congr 1
        omega
      · rw [show dualCappedMultipleBlockFiveValuation z 3 x =
            (4 : Fin 5) by
          simp [dualCappedMultipleBlockFiveValuation, hx]]
        rw [dualCappedMultipleBlockFivePower_other,
          dualCappedMultipleBlockFivePowerFold,
          List.count_cons_of_ne hx]

/-- The five states visible to the exact `S5_209` table for one variable. -/
inductive DualCappedMultipleBlockFiveState where
  | absent
  | singletonHead
  | singletonTail
  | exactlyTwo
  | atLeastThree
deriving DecidableEq, Repr

def dualCappedMultipleBlockFiveVariableState
    (w : Word Nat) (z : Nat) : DualCappedMultipleBlockFiveState :=
  let count := w.toList.count z
  if count = 0 then
    .absent
  else if count = 1 then
    if w.head = z then .singletonHead else .singletonTail
  else if count = 2 then
    .exactlyTwo
  else
    .atLeastThree

private def DualCappedMultipleBlockFiveState.headValue :
    DualCappedMultipleBlockFiveState → Fin 5
  | .absent => 4
  | .singletonHead => 2
  | .singletonTail => 0
  | .exactlyTwo => 0
  | .atLeastThree => 0

private def DualCappedMultipleBlockFiveState.powerValue :
    DualCappedMultipleBlockFiveState → Fin 5
  | .absent => 4
  | .singletonHead => 3
  | .singletonTail => 3
  | .exactlyTwo => 1
  | .atLeastThree => 0

private theorem dualCappedMultipleBlockFiveEvalHead
    (z : Nat) (w : Word Nat) :
    dualCappedMultipleBlockFive.semigroup.eval
        (dualCappedMultipleBlockFiveValuation z 2) w =
      (dualCappedMultipleBlockFiveVariableState w z).headValue := by
  cases w with
  | mk head tail =>
      by_cases hhead : head = z
      · subst head
        change
          tail.foldl
              (fun current x =>
                dualCappedMultipleBlockFiveMul current
                  (dualCappedMultipleBlockFiveValuation z 2 x))
              (dualCappedMultipleBlockFiveValuation z 2 z) =
            (dualCappedMultipleBlockFiveVariableState
              ⟨z, tail⟩ z).headValue
        rw [show dualCappedMultipleBlockFiveValuation z 2 z =
            dualCappedMultipleBlockFiveHeadHeadState 0 by
          simp [dualCappedMultipleBlockFiveValuation,
            dualCappedMultipleBlockFiveHeadHeadState]]
        rw [dualCappedMultipleBlockFiveHeadHeadFold]
        by_cases hzero : tail.count z = 0
        · simp [dualCappedMultipleBlockFiveVariableState,
            dualCappedMultipleBlockFiveHeadHeadState,
            DualCappedMultipleBlockFiveState.headValue,
            Word.toList, hzero]
        · by_cases hone : tail.count z = 1
          · simp [dualCappedMultipleBlockFiveVariableState,
              dualCappedMultipleBlockFiveHeadHeadState,
              DualCappedMultipleBlockFiveState.headValue,
              Word.toList, hone]
          · simp [dualCappedMultipleBlockFiveVariableState,
              dualCappedMultipleBlockFiveHeadHeadState,
              DualCappedMultipleBlockFiveState.headValue,
              Word.toList, hzero, hone]
      · change
          tail.foldl
              (fun current x =>
                dualCappedMultipleBlockFiveMul current
                  (dualCappedMultipleBlockFiveValuation z 2 x))
              (dualCappedMultipleBlockFiveValuation z 2 head) =
            (dualCappedMultipleBlockFiveVariableState
              ⟨head, tail⟩ z).headValue
        rw [show dualCappedMultipleBlockFiveValuation z 2 head =
            dualCappedMultipleBlockFiveHeadOtherState 0 by
          simp [dualCappedMultipleBlockFiveValuation,
            dualCappedMultipleBlockFiveHeadOtherState, hhead]]
        rw [dualCappedMultipleBlockFiveHeadOtherFold]
        by_cases hzero : tail.count z = 0
        · simp [dualCappedMultipleBlockFiveVariableState,
            dualCappedMultipleBlockFiveHeadOtherState,
            DualCappedMultipleBlockFiveState.headValue,
            Word.toList, hhead, hzero]
        · by_cases hone : tail.count z = 1
          · simp [dualCappedMultipleBlockFiveVariableState,
              dualCappedMultipleBlockFiveHeadOtherState,
              DualCappedMultipleBlockFiveState.headValue,
              Word.toList, hhead, hone]
          · by_cases htwo : tail.count z = 2 <;>
              simp [dualCappedMultipleBlockFiveVariableState,
                dualCappedMultipleBlockFiveHeadOtherState,
                DualCappedMultipleBlockFiveState.headValue,
                Word.toList, hhead, hzero, hone, htwo]

private theorem dualCappedMultipleBlockFiveEvalPower
    (z : Nat) (w : Word Nat) :
    dualCappedMultipleBlockFive.semigroup.eval
        (dualCappedMultipleBlockFiveValuation z 3) w =
      (dualCappedMultipleBlockFiveVariableState w z).powerValue := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              dualCappedMultipleBlockFiveMul current
                (dualCappedMultipleBlockFiveValuation z 3 x))
            (dualCappedMultipleBlockFiveValuation z 3 head) =
          (dualCappedMultipleBlockFiveVariableState
            ⟨head, tail⟩ z).powerValue
      by_cases hhead : head = z
      · subst head
        rw [show dualCappedMultipleBlockFiveValuation z 3 z =
            dualCappedMultipleBlockFivePowerState 1 by
          simp [dualCappedMultipleBlockFiveValuation,
            dualCappedMultipleBlockFivePowerState]]
        rw [dualCappedMultipleBlockFivePowerFold]
        by_cases hzero : tail.count z = 0
        · simp [dualCappedMultipleBlockFiveVariableState,
            dualCappedMultipleBlockFivePowerState,
            DualCappedMultipleBlockFiveState.powerValue,
            Word.toList, hzero]
        · by_cases hone : tail.count z = 1
          · simp [dualCappedMultipleBlockFiveVariableState,
              dualCappedMultipleBlockFivePowerState,
              DualCappedMultipleBlockFiveState.powerValue,
              Word.toList, hone]
          · have hlarge : 1 + tail.count z ≠ 2 := by omega
            simp [dualCappedMultipleBlockFiveVariableState,
              dualCappedMultipleBlockFivePowerState,
              DualCappedMultipleBlockFiveState.powerValue,
              Word.toList, hzero, hone, hlarge]
      · rw [show dualCappedMultipleBlockFiveValuation z 3 head =
            dualCappedMultipleBlockFivePowerState 0 by
          simp [dualCappedMultipleBlockFiveValuation,
            dualCappedMultipleBlockFivePowerState, hhead]]
        rw [dualCappedMultipleBlockFivePowerFold]
        by_cases hzero : tail.count z = 0
        · simp [dualCappedMultipleBlockFiveVariableState,
            dualCappedMultipleBlockFivePowerState,
            DualCappedMultipleBlockFiveState.powerValue,
            Word.toList, hhead, hzero]
        · by_cases hone : tail.count z = 1
          · simp [dualCappedMultipleBlockFiveVariableState,
              dualCappedMultipleBlockFivePowerState,
              DualCappedMultipleBlockFiveState.powerValue,
              Word.toList, hhead, hone]
          · by_cases htwo : tail.count z = 2
            · simp [dualCappedMultipleBlockFiveVariableState,
                dualCappedMultipleBlockFivePowerState,
                DualCappedMultipleBlockFiveState.powerValue,
                Word.toList, hhead, htwo]
            · simp [dualCappedMultipleBlockFiveVariableState,
                dualCappedMultipleBlockFivePowerState,
                DualCappedMultipleBlockFiveState.powerValue,
                Word.toList, hhead, hzero, hone, htwo]

private theorem DualCappedMultipleBlockFiveState.eq_of_values_eq
    {left right : DualCappedMultipleBlockFiveState}
    (head : left.headValue = right.headValue)
    (power : left.powerValue = right.powerValue) :
    left = right := by
  cases left <;> cases right <;>
    simp_all [DualCappedMultipleBlockFiveState.headValue,
      DualCappedMultipleBlockFiveState.powerValue]

theorem dualCappedMultipleBlockFiveValid_state_eq
    (e : Identity Nat)
    (valid : e.SatisfiedBy dualCappedMultipleBlockFive.semigroup)
    (z : Nat) :
    dualCappedMultipleBlockFiveVariableState e.lhs z =
      dualCappedMultipleBlockFiveVariableState e.rhs z := by
  apply DualCappedMultipleBlockFiveState.eq_of_values_eq
  · have h := valid (dualCappedMultipleBlockFiveValuation z 2)
    simpa [dualCappedMultipleBlockFiveEvalHead] using h
  · have h := valid (dualCappedMultipleBlockFiveValuation z 3)
    simpa [dualCappedMultipleBlockFiveEvalPower] using h

private def DualCappedMultipleBlockFiveState.exponent :
    DualCappedMultipleBlockFiveState → Nat
  | .absent => 0
  | .singletonHead => 1
  | .singletonTail => 1
  | .exactlyTwo => 2
  | .atLeastThree => 3

private theorem dualCappedMultipleBlockFiveVariableState_exponent
    (w : Word Nat) (z : Nat) :
    (dualCappedMultipleBlockFiveVariableState w z).exponent =
      dualCappedMultipleBlockFiveExponent (w.toList.count z) := by
  by_cases hzero : w.toList.count z = 0
  · simp [dualCappedMultipleBlockFiveVariableState,
      DualCappedMultipleBlockFiveState.exponent,
      dualCappedMultipleBlockFiveExponent, hzero]
  · by_cases hone : w.toList.count z = 1
    · by_cases hhead : w.head = z <;>
        simp [dualCappedMultipleBlockFiveVariableState,
          DualCappedMultipleBlockFiveState.exponent,
          dualCappedMultipleBlockFiveExponent, hone, hhead]
    · by_cases htwo : w.toList.count z = 2
      · simp [dualCappedMultipleBlockFiveVariableState,
          DualCappedMultipleBlockFiveState.exponent,
          dualCappedMultipleBlockFiveExponent, htwo]
      · have hlarge : ¬w.toList.count z < 3 := by omega
        simp [dualCappedMultipleBlockFiveVariableState,
          DualCappedMultipleBlockFiveState.exponent,
          dualCappedMultipleBlockFiveExponent, hzero, hone, htwo, hlarge]

private theorem dualCappedMultipleBlockFiveState_singletonHead_iff
    (w : Word Nat) (z : Nat) :
    dualCappedMultipleBlockFiveVariableState w z =
        .singletonHead ↔
      w.toList.count z = 1 ∧ w.head = z := by
  by_cases hzero : w.toList.count z = 0
  · simp [dualCappedMultipleBlockFiveVariableState, hzero]
  · by_cases hone : w.toList.count z = 1
    · by_cases hhead : w.head = z <;>
        simp [dualCappedMultipleBlockFiveVariableState, hone, hhead]
    · by_cases htwo : w.toList.count z = 2 <;>
        simp [dualCappedMultipleBlockFiveVariableState, hzero, hone, htwo]

theorem dualCappedMultipleBlockFiveSingletonHead_eq_some_iff
    (w : Word Nat) (z : Nat) :
    dualCappedMultipleBlockFiveSingletonHead w = some z ↔
      dualCappedMultipleBlockFiveVariableState w z =
        .singletonHead := by
  rw [dualCappedMultipleBlockFiveState_singletonHead_iff]
  unfold dualCappedMultipleBlockFiveSingletonHead
  by_cases hcount : w.toList.count w.head = 1
  · rw [if_pos hcount]
    constructor
    · intro h
      have hhead : w.head = z := Option.some.inj h
      subst z
      exact ⟨hcount, rfl⟩
    · rintro ⟨hz, hhead⟩
      subst z
      rfl
  · rw [if_neg hcount]
    constructor
    · intro h
      contradiction
    · rintro ⟨hz, hhead⟩
      subst z
      exact False.elim (hcount hz)

theorem dualCappedMultipleBlockFiveBasis_complete :
    BasisFor dualCappedMultipleBlockFive.semigroup
      dualCappedMultipleBlockFiveBasis := by
  refine ⟨dualCappedMultipleBlockFiveBasis_models, ?_⟩
  intro e valid
  apply dualCappedMultipleBlockFiveDerivesOfInvariantEq
  · intro z
    rw [← dualCappedMultipleBlockFiveVariableState_exponent e.lhs z,
      dualCappedMultipleBlockFiveValid_state_eq e valid z,
      dualCappedMultipleBlockFiveVariableState_exponent]
  · apply Option.ext
    intro z
    rw [dualCappedMultipleBlockFiveSingletonHead_eq_some_iff,
      dualCappedMultipleBlockFiveSingletonHead_eq_some_iff,
      dualCappedMultipleBlockFiveValid_state_eq e valid z]

def dualCappedMultipleBlockFiveStoredX : Word Nat := Word.singleton 0
def dualCappedMultipleBlockFiveStoredXXX : Word Nat := ⟨0, [0, 0]⟩
def dualCappedMultipleBlockFiveStoredXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def dualCappedMultipleBlockFiveStoredXYX : Word Nat := ⟨0, [1, 0]⟩
def dualCappedMultipleBlockFiveStoredYXX : Word Nat := ⟨1, [0, 0]⟩
def dualCappedMultipleBlockFiveStoredXYZ : Word Nat := ⟨0, [1, 2]⟩
def dualCappedMultipleBlockFiveStoredYXZ : Word Nat := ⟨1, [0, 2]⟩
def dualCappedMultipleBlockFiveStoredXXYY : Word Nat := ⟨0, [0, 1, 1]⟩
def dualCappedMultipleBlockFiveStoredXYYX : Word Nat := ⟨0, [1, 1, 0]⟩

def dualCappedMultipleBlockFiveStoredPowerLaw : Identity Nat :=
  ⟨dualCappedMultipleBlockFiveStoredXXX,
    dualCappedMultipleBlockFiveStoredXXXX⟩

def dualCappedMultipleBlockFiveStoredGatherLaw : Identity Nat :=
  ⟨dualCappedMultipleBlockFiveStoredXYX,
    dualCappedMultipleBlockFiveStoredYXX⟩

def dualCappedMultipleBlockFiveStoredPrefixSwapLaw : Identity Nat :=
  ⟨dualCappedMultipleBlockFiveStoredXYZ,
    dualCappedMultipleBlockFiveStoredYXZ⟩

def dualCappedMultipleBlockFiveStoredSquareRotationLaw : Identity Nat :=
  ⟨dualCappedMultipleBlockFiveStoredXXYY,
    dualCappedMultipleBlockFiveStoredXYYX⟩

/-- The exact stored `S5_209` basis
`xxx = xxxx`, `xyx = yxx`, `xyz = yxz`, `xxyy = xyyx`. -/
def dualCappedMultipleBlockFiveStoredBasis : List (Identity Nat) :=
  [dualCappedMultipleBlockFiveStoredPowerLaw,
    dualCappedMultipleBlockFiveStoredGatherLaw,
    dualCappedMultipleBlockFiveStoredPrefixSwapLaw,
    dualCappedMultipleBlockFiveStoredSquareRotationLaw]

private def dualCappedMultipleBlockFiveExactOppositeBasis :
    List (Identity Nat) :=
  reversedBasis dualCappedMultipleBlockFiveStoredBasis

private def dualCappedMultipleBlockFiveRenameReverseSwap
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => w
  | 1 => v
  | 2 => u
  | n + 3 => Word.singleton (n + 3)

private theorem dualCappedMultipleBlockFiveNormalizedAxiomsDeriveExact :
    ∀ e : Identity Nat, e ∈ dualCappedMultipleBlockFiveBasis →
      Derives dualCappedMultipleBlockFiveExactOppositeBasis e.lhs e.rhs := by
  intro e he
  simp only [dualCappedMultipleBlockFiveBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Derives.fromBasis <| by
      exact List.Mem.head _
  · exact Derives.fromBasis <| by
      exact List.Mem.tail _ (List.Mem.head _)
  · have exactLaw :
        Derives dualCappedMultipleBlockFiveExactOppositeBasis
          (dualCappedMultipleBlockFiveStoredPrefixSwapLaw.reversed.lhs)
          (dualCappedMultipleBlockFiveStoredPrefixSwapLaw.reversed.rhs) :=
      Derives.fromBasis <| by
        exact List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)
    have renamed :=
      Derives.subst exactLaw
        (dualCappedMultipleBlockFiveRenameReverseSwap
          (Word.singleton 0) (Word.singleton 1)
          (Word.singleton 2))
    simpa [dualCappedMultipleBlockFiveStoredPrefixSwapLaw,
      dualCappedMultipleBlockFiveStoredXYZ,
      dualCappedMultipleBlockFiveStoredYXZ,
      Identity.reversed, Word.reverse, Word.bind,
      dualCappedMultipleBlockFiveXYZ, dualCappedMultipleBlockFiveXZY,
      dualCappedMultipleBlockFiveRenameReverseSwap,
      Word.singleton, Word.append, Word.append_assoc] using renamed
  · exact Derives.fromBasis <| by
      exact List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)

private theorem dualCappedMultipleBlockFiveExactAxiomsDeriveNormalized :
    ∀ e : Identity Nat,
      e ∈ dualCappedMultipleBlockFiveExactOppositeBasis →
      Derives dualCappedMultipleBlockFiveBasis e.lhs e.rhs := by
  intro e he
  simp only [dualCappedMultipleBlockFiveExactOppositeBasis,
    dualCappedMultipleBlockFiveStoredBasis, reversedBasis,
    List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Derives.fromBasis <| by
      exact List.Mem.head _
  · exact Derives.fromBasis <| by
      exact List.Mem.tail _ (List.Mem.head _)
  · have normalizedLaw :
        Derives dualCappedMultipleBlockFiveBasis
          dualCappedMultipleBlockFiveXYZ
          dualCappedMultipleBlockFiveXZY :=
      Derives.fromBasis
          (e := dualCappedMultipleBlockFiveSuffixSwapLaw) <| by
        exact List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)
    have renamed :=
      Derives.subst normalizedLaw
        (dualCappedMultipleBlockFiveRenameReverseSwap
          (Word.singleton 0) (Word.singleton 1)
          (Word.singleton 2))
    simpa [dualCappedMultipleBlockFiveStoredPrefixSwapLaw,
      dualCappedMultipleBlockFiveStoredXYZ,
      dualCappedMultipleBlockFiveStoredYXZ,
      Identity.reversed, Word.reverse, Word.bind,
      dualCappedMultipleBlockFiveXYZ, dualCappedMultipleBlockFiveXZY,
      dualCappedMultipleBlockFiveRenameReverseSwap,
      Word.singleton, Word.append, Word.append_assoc] using renamed
  · exact Derives.fromBasis <| by
      exact List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)

private theorem dualCappedMultipleBlockFiveExactOpposite_models :
    Models dualCappedMultipleBlockFive.semigroup
      dualCappedMultipleBlockFiveExactOppositeBasis := by
  intro e he valuation
  exact
    (dualCappedMultipleBlockFiveExactAxiomsDeriveNormalized e he).sound
      dualCappedMultipleBlockFiveBasis_models valuation

private theorem dualCappedMultipleBlockFiveExactOppositeBasis_complete :
    BasisFor dualCappedMultipleBlockFive.semigroup
      dualCappedMultipleBlockFiveExactOppositeBasis :=
  dualCappedMultipleBlockFiveBasis_complete.replace
    dualCappedMultipleBlockFiveExactOpposite_models
    dualCappedMultipleBlockFiveNormalizedAxiomsDeriveExact

private theorem dualCappedMultipleBlockFiveReverseExactBasis :
    reversedBasis dualCappedMultipleBlockFiveExactOppositeBasis =
      dualCappedMultipleBlockFiveStoredBasis := by
  decide

/-- Completeness of the exact basis in the stored `S5_209` orientation. -/
theorem dualCappedMultipleBlockFiveStoredBasis_complete :
    BasisFor dualCappedMultipleBlockFiveStored.semigroup
      dualCappedMultipleBlockFiveStoredBasis := by
  have reversed :=
    dualCappedMultipleBlockFiveExactOppositeBasis_complete.oppositeReversed
  rw [dualCappedMultipleBlockFiveReverseExactBasis] at reversed
  simpa [dualCappedMultipleBlockFiveStored,
    dualCappedMultipleBlockFiveStoredMul,
    dualCappedMultipleBlockFive, FiniteTable.semigroup,
    Semigroup.opposite] using reversed

end SemigroupBasis.Examples

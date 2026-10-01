import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo
import SemigroupBasis.Examples.DualMultipleBlockFiveSyntax
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The zero-based multiplication table opposite to the stored `S5_121`
representative. This orientation has right identity `4` and is the natural
orientation for the block normal form. -/
def dualMultipleBlockFiveMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 0 else
      if b = 2 then 0 else if b = 3 then 3 else 0
  else if a = 1 then
    if b = 0 then 0 else if b = 1 then 0 else
      if b = 2 then 0 else if b = 3 then 3 else 1
  else if a = 2 then
    if b = 0 then 0 else if b = 1 then 0 else
      if b = 2 then 0 else if b = 3 then 3 else 2
  else if a = 3 then
    if b = 0 then 3 else if b = 1 then 3 else
      if b = 2 then 3 else if b = 3 then 0 else 3
  else
    if b = 0 then 0 else if b = 1 then 0 else
      if b = 2 then 2 else if b = 3 then 3 else 4

def dualMultipleBlockFive : FiniteTable where
  order := 5
  mul := dualMultipleBlockFiveMul
  assoc := by decide

/-- The stored Smallsemi orientation of `S5_121`. -/
def dualMultipleBlockFiveStoredMul (a b : Fin 5) : Fin 5 :=
  dualMultipleBlockFiveMul b a

def dualMultipleBlockFiveStored : FiniteTable where
  order := 5
  mul := dualMultipleBlockFiveStoredMul
  assoc := by decide

private theorem dualMultipleBlockFiveMul_power (a : Fin 5) :
    dualMultipleBlockFiveMul a a =
      dualMultipleBlockFiveMul
        (dualMultipleBlockFiveMul
          (dualMultipleBlockFiveMul a a) a) a := by
  decide +revert

private theorem dualMultipleBlockFiveMul_gather (a b : Fin 5) :
    dualMultipleBlockFiveMul
        (dualMultipleBlockFiveMul a b) a =
      dualMultipleBlockFiveMul
        (dualMultipleBlockFiveMul a a) b := by
  decide +revert

private theorem dualMultipleBlockFiveMul_suffixSwap
    (a b c : Fin 5) :
    dualMultipleBlockFiveMul
        (dualMultipleBlockFiveMul a b) c =
      dualMultipleBlockFiveMul
        (dualMultipleBlockFiveMul a c) b := by
  decide +revert

private theorem dualMultipleBlockFiveMul_squareRotation
    (a b : Fin 5) :
    dualMultipleBlockFiveMul
        (dualMultipleBlockFiveMul
          (dualMultipleBlockFiveMul b b) a) a =
      dualMultipleBlockFiveMul
        (dualMultipleBlockFiveMul
          (dualMultipleBlockFiveMul a b) b) a := by
  decide +revert

theorem dualMultipleBlockFiveBasis_models :
    Models dualMultipleBlockFive.semigroup
      dualMultipleBlockFiveBasis := by
  intro e he
  simp only [dualMultipleBlockFiveBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · intro valuation
    change
      dualMultipleBlockFiveMul (valuation 0) (valuation 0) =
        dualMultipleBlockFiveMul
          (dualMultipleBlockFiveMul
            (dualMultipleBlockFiveMul
              (valuation 0) (valuation 0))
            (valuation 0))
          (valuation 0)
    exact dualMultipleBlockFiveMul_power (valuation 0)
  · intro valuation
    change
      dualMultipleBlockFiveMul
          (dualMultipleBlockFiveMul (valuation 0) (valuation 1))
          (valuation 0) =
        dualMultipleBlockFiveMul
          (dualMultipleBlockFiveMul (valuation 0) (valuation 0))
          (valuation 1)
    exact dualMultipleBlockFiveMul_gather
      (valuation 0) (valuation 1)
  · intro valuation
    change
      dualMultipleBlockFiveMul
          (dualMultipleBlockFiveMul (valuation 0) (valuation 1))
          (valuation 2) =
        dualMultipleBlockFiveMul
          (dualMultipleBlockFiveMul (valuation 0) (valuation 2))
          (valuation 1)
    exact dualMultipleBlockFiveMul_suffixSwap
      (valuation 0) (valuation 1) (valuation 2)
  · intro valuation
    change
      dualMultipleBlockFiveMul
          (dualMultipleBlockFiveMul
            (dualMultipleBlockFiveMul
              (valuation 1) (valuation 1))
            (valuation 0))
          (valuation 0) =
        dualMultipleBlockFiveMul
          (dualMultipleBlockFiveMul
            (dualMultipleBlockFiveMul
              (valuation 0) (valuation 1))
            (valuation 1))
          (valuation 0)
    exact dualMultipleBlockFiveMul_squareRotation
      (valuation 0) (valuation 1)

private def dualMultipleBlockFiveValuation
    (z : Nat) (witness : Fin 5) : Nat → Fin 5 :=
  fun x => if x = z then witness else 4

private theorem dualMultipleBlockFiveMul_rightIdentity (a : Fin 5) :
    dualMultipleBlockFiveMul a 4 = a := by
  decide +revert

private def dualMultipleBlockFiveTwoHeadState (n : Nat) : Fin 5 :=
  if n = 0 then 1 else 0

private def dualMultipleBlockFiveTwoOtherState (n : Nat) : Fin 5 :=
  if n = 0 then 4 else 0

private theorem dualMultipleBlockFiveTwoHead_target (n : Nat) :
    dualMultipleBlockFiveMul
        (dualMultipleBlockFiveTwoHeadState n) 1 =
      dualMultipleBlockFiveTwoHeadState (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [dualMultipleBlockFiveTwoHeadState, hn,
      dualMultipleBlockFiveMul]

private theorem dualMultipleBlockFiveTwoOther_target (n : Nat) :
    dualMultipleBlockFiveMul
        (dualMultipleBlockFiveTwoOtherState n) 1 =
      dualMultipleBlockFiveTwoOtherState (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [dualMultipleBlockFiveTwoOtherState, hn,
      dualMultipleBlockFiveMul]

private theorem dualMultipleBlockFiveTwoHead_other (n : Nat) :
    dualMultipleBlockFiveMul
        (dualMultipleBlockFiveTwoHeadState n) 4 =
      dualMultipleBlockFiveTwoHeadState n :=
  dualMultipleBlockFiveMul_rightIdentity _

private theorem dualMultipleBlockFiveTwoOther_other (n : Nat) :
    dualMultipleBlockFiveMul
        (dualMultipleBlockFiveTwoOtherState n) 4 =
      dualMultipleBlockFiveTwoOtherState n :=
  dualMultipleBlockFiveMul_rightIdentity _

private theorem dualMultipleBlockFiveTwoHeadFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            dualMultipleBlockFiveMul current
              (dualMultipleBlockFiveValuation z 1 x))
          (dualMultipleBlockFiveTwoHeadState n) =
        dualMultipleBlockFiveTwoHeadState (n + xs.count z)
  | [], _ => by simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show dualMultipleBlockFiveValuation z 1 z =
            (1 : Fin 5) by
          simp [dualMultipleBlockFiveValuation]]
        rw [dualMultipleBlockFiveTwoHead_target,
          dualMultipleBlockFiveTwoHeadFold]
        rw [List.count_cons_self]
        congr 1
        omega
      · rw [show dualMultipleBlockFiveValuation z 1 x =
            (4 : Fin 5) by
          simp [dualMultipleBlockFiveValuation, hx]]
        rw [dualMultipleBlockFiveTwoHead_other,
          dualMultipleBlockFiveTwoHeadFold,
          List.count_cons_of_ne hx]

private theorem dualMultipleBlockFiveTwoOtherFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            dualMultipleBlockFiveMul current
              (dualMultipleBlockFiveValuation z 1 x))
          (dualMultipleBlockFiveTwoOtherState n) =
        dualMultipleBlockFiveTwoOtherState (n + xs.count z)
  | [], _ => by simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show dualMultipleBlockFiveValuation z 1 z =
            (1 : Fin 5) by
          simp [dualMultipleBlockFiveValuation]]
        rw [dualMultipleBlockFiveTwoOther_target,
          dualMultipleBlockFiveTwoOtherFold]
        rw [List.count_cons_self]
        congr 1
        omega
      · rw [show dualMultipleBlockFiveValuation z 1 x =
            (4 : Fin 5) by
          simp [dualMultipleBlockFiveValuation, hx]]
        rw [dualMultipleBlockFiveTwoOther_other,
          dualMultipleBlockFiveTwoOtherFold,
          List.count_cons_of_ne hx]

private def dualMultipleBlockFiveThreeState (n : Nat) : Fin 5 :=
  if n = 0 then 4 else if n = 1 then 2 else 0

private theorem dualMultipleBlockFiveThree_target (n : Nat) :
    dualMultipleBlockFiveMul
        (dualMultipleBlockFiveThreeState n) 2 =
      dualMultipleBlockFiveThreeState (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · simp [dualMultipleBlockFiveThreeState, hn0, hn1,
        dualMultipleBlockFiveMul]

private theorem dualMultipleBlockFiveThree_other (n : Nat) :
    dualMultipleBlockFiveMul
        (dualMultipleBlockFiveThreeState n) 4 =
      dualMultipleBlockFiveThreeState n :=
  dualMultipleBlockFiveMul_rightIdentity _

private theorem dualMultipleBlockFiveThreeFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            dualMultipleBlockFiveMul current
              (dualMultipleBlockFiveValuation z 2 x))
          (dualMultipleBlockFiveThreeState n) =
        dualMultipleBlockFiveThreeState (n + xs.count z)
  | [], _ => by simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show dualMultipleBlockFiveValuation z 2 z =
            (2 : Fin 5) by
          simp [dualMultipleBlockFiveValuation]]
        rw [dualMultipleBlockFiveThree_target,
          dualMultipleBlockFiveThreeFold]
        rw [List.count_cons_self]
        congr 1
        omega
      · rw [show dualMultipleBlockFiveValuation z 2 x =
            (4 : Fin 5) by
          simp [dualMultipleBlockFiveValuation, hx]]
        rw [dualMultipleBlockFiveThree_other,
          dualMultipleBlockFiveThreeFold,
          List.count_cons_of_ne hx]

private def dualMultipleBlockFiveFourState (n : Nat) : Fin 5 :=
  if n = 0 then 4 else if n % 2 = 0 then 0 else 3

private theorem dualMultipleBlockFiveFour_target (n : Nat) :
    dualMultipleBlockFiveMul
        (dualMultipleBlockFiveFourState n) 3 =
      dualMultipleBlockFiveFourState (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hp : n % 2 = 0
    · have hnext : (n + 1) % 2 = 1 := by omega
      simp [dualMultipleBlockFiveFourState, hn0, hp, hnext,
        dualMultipleBlockFiveMul]
    · have hmod : n % 2 = 1 := by omega
      have hnext : (n + 1) % 2 = 0 := by omega
      simp [dualMultipleBlockFiveFourState, hn0, hmod, hnext,
        dualMultipleBlockFiveMul]

private theorem dualMultipleBlockFiveFour_other (n : Nat) :
    dualMultipleBlockFiveMul
        (dualMultipleBlockFiveFourState n) 4 =
      dualMultipleBlockFiveFourState n :=
  dualMultipleBlockFiveMul_rightIdentity _

private theorem dualMultipleBlockFiveFourFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            dualMultipleBlockFiveMul current
              (dualMultipleBlockFiveValuation z 3 x))
          (dualMultipleBlockFiveFourState n) =
        dualMultipleBlockFiveFourState (n + xs.count z)
  | [], _ => by simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show dualMultipleBlockFiveValuation z 3 z =
            (3 : Fin 5) by
          simp [dualMultipleBlockFiveValuation]]
        rw [dualMultipleBlockFiveFour_target,
          dualMultipleBlockFiveFourFold]
        rw [List.count_cons_self]
        congr 1
        omega
      · rw [show dualMultipleBlockFiveValuation z 3 x =
            (4 : Fin 5) by
          simp [dualMultipleBlockFiveValuation, hx]]
        rw [dualMultipleBlockFiveFour_other,
          dualMultipleBlockFiveFourFold,
          List.count_cons_of_ne hx]

/-- The five states visible to the exact table for one variable. -/
inductive DualMultipleBlockFiveState where
  | absent
  | singletonHead
  | singletonTail
  | positiveEven
  | oddAtLeastThree
deriving DecidableEq, Repr

def dualMultipleBlockFiveVariableState
    (w : Word Nat) (z : Nat) : DualMultipleBlockFiveState :=
  let count := w.toList.count z
  if count = 0 then
    .absent
  else if count = 1 then
    if w.head = z then .singletonHead else .singletonTail
  else if count % 2 = 0 then
    .positiveEven
  else
    .oddAtLeastThree

private def DualMultipleBlockFiveState.twoValue :
    DualMultipleBlockFiveState → Fin 5
  | .absent => 4
  | .singletonHead => 1
  | .singletonTail => 0
  | .positiveEven => 0
  | .oddAtLeastThree => 0

private def DualMultipleBlockFiveState.threeValue :
    DualMultipleBlockFiveState → Fin 5
  | .absent => 4
  | .singletonHead => 2
  | .singletonTail => 2
  | .positiveEven => 0
  | .oddAtLeastThree => 0

private def DualMultipleBlockFiveState.fourValue :
    DualMultipleBlockFiveState → Fin 5
  | .absent => 4
  | .singletonHead => 3
  | .singletonTail => 3
  | .positiveEven => 0
  | .oddAtLeastThree => 3

private theorem dualMultipleBlockFiveEvalTwo
    (z : Nat) (w : Word Nat) :
    dualMultipleBlockFive.semigroup.eval
        (dualMultipleBlockFiveValuation z 1) w =
      (dualMultipleBlockFiveVariableState w z).twoValue := by
  cases w with
  | mk head tail =>
      by_cases hhead : head = z
      · subst head
        change
          tail.foldl
              (fun current x =>
                dualMultipleBlockFiveMul current
                  (dualMultipleBlockFiveValuation z 1 x))
              (dualMultipleBlockFiveValuation z 1 z) =
            (dualMultipleBlockFiveVariableState
              ⟨z, tail⟩ z).twoValue
        rw [show dualMultipleBlockFiveValuation z 1 z =
            (1 : Fin 5) by
          simp [dualMultipleBlockFiveValuation]]
        change
          tail.foldl
              (fun current x =>
                dualMultipleBlockFiveMul current
                  (dualMultipleBlockFiveValuation z 1 x))
              (dualMultipleBlockFiveTwoHeadState 0) =
            (dualMultipleBlockFiveVariableState
              ⟨z, tail⟩ z).twoValue
        rw [dualMultipleBlockFiveTwoHeadFold]
        by_cases htail : tail.count z = 0
        · simp [dualMultipleBlockFiveVariableState,
            dualMultipleBlockFiveTwoHeadState,
            DualMultipleBlockFiveState.twoValue, Word.toList, htail]
        · by_cases hparity : (tail.count z + 1) % 2 = 0 <;>
            simp [dualMultipleBlockFiveVariableState,
              dualMultipleBlockFiveTwoHeadState,
              DualMultipleBlockFiveState.twoValue, Word.toList,
              htail, hparity]
      · change
          tail.foldl
              (fun current x =>
                dualMultipleBlockFiveMul current
                  (dualMultipleBlockFiveValuation z 1 x))
              (dualMultipleBlockFiveValuation z 1 head) =
            (dualMultipleBlockFiveVariableState
              ⟨head, tail⟩ z).twoValue
        rw [show dualMultipleBlockFiveValuation z 1 head =
            (4 : Fin 5) by
          simp [dualMultipleBlockFiveValuation, hhead],
          show (4 : Fin 5) =
            dualMultipleBlockFiveTwoOtherState 0 by rfl,
          dualMultipleBlockFiveTwoOtherFold]
        by_cases hzero : tail.count z = 0
        · simp [dualMultipleBlockFiveVariableState,
            dualMultipleBlockFiveTwoOtherState,
            DualMultipleBlockFiveState.twoValue, Word.toList, hhead, hzero]
        · by_cases hone : tail.count z = 1
          · simp [dualMultipleBlockFiveVariableState,
              dualMultipleBlockFiveTwoOtherState,
              DualMultipleBlockFiveState.twoValue, Word.toList,
              hhead, hone]
          · by_cases hparity : tail.count z % 2 = 0 <;>
              simp [dualMultipleBlockFiveVariableState,
                dualMultipleBlockFiveTwoOtherState,
                DualMultipleBlockFiveState.twoValue, Word.toList,
                hhead, hzero, hone, hparity]

private theorem dualMultipleBlockFiveEvalThree
    (z : Nat) (w : Word Nat) :
    dualMultipleBlockFive.semigroup.eval
        (dualMultipleBlockFiveValuation z 2) w =
      (dualMultipleBlockFiveVariableState w z).threeValue := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              dualMultipleBlockFiveMul current
                (dualMultipleBlockFiveValuation z 2 x))
            (dualMultipleBlockFiveValuation z 2 head) =
          (dualMultipleBlockFiveVariableState
            ⟨head, tail⟩ z).threeValue
      by_cases hhead : head = z
      · subst head
        rw [show dualMultipleBlockFiveValuation z 2 z =
            dualMultipleBlockFiveThreeState 1 by
          simp [dualMultipleBlockFiveValuation,
            dualMultipleBlockFiveThreeState]]
        rw [dualMultipleBlockFiveThreeFold]
        by_cases htail0 : tail.count z = 0
        · simp [dualMultipleBlockFiveVariableState,
            dualMultipleBlockFiveThreeState,
            DualMultipleBlockFiveState.threeValue, Word.toList, htail0]
        · by_cases htail1 : tail.count z = 1
          · simp [dualMultipleBlockFiveVariableState,
              dualMultipleBlockFiveThreeState,
              DualMultipleBlockFiveState.threeValue, Word.toList,
              htail1]
          · by_cases hparity : (tail.count z + 1) % 2 = 0 <;>
              simp [dualMultipleBlockFiveVariableState,
                dualMultipleBlockFiveThreeState,
                DualMultipleBlockFiveState.threeValue, Word.toList,
                htail0, hparity]
      · rw [show dualMultipleBlockFiveValuation z 2 head =
            dualMultipleBlockFiveThreeState 0 by
          simp [dualMultipleBlockFiveValuation,
            dualMultipleBlockFiveThreeState, hhead]]
        rw [dualMultipleBlockFiveThreeFold]
        by_cases hzero : tail.count z = 0
        · simp [dualMultipleBlockFiveVariableState,
            dualMultipleBlockFiveThreeState,
            DualMultipleBlockFiveState.threeValue, Word.toList,
            hhead, hzero]
        · by_cases hone : tail.count z = 1
          · simp [dualMultipleBlockFiveVariableState,
              dualMultipleBlockFiveThreeState,
              DualMultipleBlockFiveState.threeValue, Word.toList,
              hhead, hone]
          · by_cases hparity : tail.count z % 2 = 0 <;>
              simp [dualMultipleBlockFiveVariableState,
                dualMultipleBlockFiveThreeState,
                DualMultipleBlockFiveState.threeValue, Word.toList,
                hhead, hzero, hone, hparity]

private theorem dualMultipleBlockFiveEvalFour
    (z : Nat) (w : Word Nat) :
    dualMultipleBlockFive.semigroup.eval
        (dualMultipleBlockFiveValuation z 3) w =
      (dualMultipleBlockFiveVariableState w z).fourValue := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              dualMultipleBlockFiveMul current
                (dualMultipleBlockFiveValuation z 3 x))
            (dualMultipleBlockFiveValuation z 3 head) =
          (dualMultipleBlockFiveVariableState
            ⟨head, tail⟩ z).fourValue
      by_cases hhead : head = z
      · subst head
        rw [show dualMultipleBlockFiveValuation z 3 z =
            dualMultipleBlockFiveFourState 1 by
          simp [dualMultipleBlockFiveValuation,
            dualMultipleBlockFiveFourState]]
        rw [dualMultipleBlockFiveFourFold]
        by_cases htail0 : tail.count z = 0
        · simp [dualMultipleBlockFiveVariableState,
            dualMultipleBlockFiveFourState,
            DualMultipleBlockFiveState.fourValue, Word.toList, htail0]
        · by_cases hparity : (tail.count z + 1) % 2 = 0
          · simp [dualMultipleBlockFiveVariableState,
              dualMultipleBlockFiveFourState,
              DualMultipleBlockFiveState.fourValue, Word.toList,
              htail0, hparity, Nat.add_comm]
          · have hmod : (tail.count z + 1) % 2 = 1 := by omega
            simp [dualMultipleBlockFiveVariableState,
              dualMultipleBlockFiveFourState,
              DualMultipleBlockFiveState.fourValue, Word.toList,
              htail0, hmod, Nat.add_comm]
      · rw [show dualMultipleBlockFiveValuation z 3 head =
            dualMultipleBlockFiveFourState 0 by
          simp [dualMultipleBlockFiveValuation,
            dualMultipleBlockFiveFourState, hhead]]
        rw [dualMultipleBlockFiveFourFold]
        by_cases hzero : tail.count z = 0
        · simp [dualMultipleBlockFiveVariableState,
            dualMultipleBlockFiveFourState,
            DualMultipleBlockFiveState.fourValue, Word.toList,
            hhead, hzero]
        · by_cases hone : tail.count z = 1
          · simp [dualMultipleBlockFiveVariableState,
              dualMultipleBlockFiveFourState,
              DualMultipleBlockFiveState.fourValue, Word.toList,
              hhead, hone]
          · by_cases hparity : tail.count z % 2 = 0
            · simp [dualMultipleBlockFiveVariableState,
                dualMultipleBlockFiveFourState,
                DualMultipleBlockFiveState.fourValue, Word.toList,
                hhead, hzero, hone, hparity]
            · have hmod : tail.count z % 2 = 1 := by omega
              simp [dualMultipleBlockFiveVariableState,
                dualMultipleBlockFiveFourState,
                DualMultipleBlockFiveState.fourValue, Word.toList,
                hhead, hzero, hone, hmod]

private theorem DualMultipleBlockFiveState.eq_of_values_eq
    {left right : DualMultipleBlockFiveState}
    (two : left.twoValue = right.twoValue)
    (three : left.threeValue = right.threeValue)
    (four : left.fourValue = right.fourValue) :
    left = right := by
  cases left <;> cases right <;>
    simp_all [DualMultipleBlockFiveState.twoValue,
      DualMultipleBlockFiveState.threeValue,
      DualMultipleBlockFiveState.fourValue]

theorem dualMultipleBlockFiveValid_state_eq
    (e : Identity Nat)
    (valid : e.SatisfiedBy dualMultipleBlockFive.semigroup)
    (z : Nat) :
    dualMultipleBlockFiveVariableState e.lhs z =
      dualMultipleBlockFiveVariableState e.rhs z := by
  apply DualMultipleBlockFiveState.eq_of_values_eq
  · have h := valid (dualMultipleBlockFiveValuation z 1)
    simpa [dualMultipleBlockFiveEvalTwo] using h
  · have h := valid (dualMultipleBlockFiveValuation z 2)
    simpa [dualMultipleBlockFiveEvalThree] using h
  · have h := valid (dualMultipleBlockFiveValuation z 3)
    simpa [dualMultipleBlockFiveEvalFour] using h

private def DualMultipleBlockFiveState.exponent :
    DualMultipleBlockFiveState → Nat
  | .absent => 0
  | .singletonHead => 1
  | .singletonTail => 1
  | .positiveEven => 2
  | .oddAtLeastThree => 3

private theorem dualMultipleBlockFiveVariableState_exponent
    (w : Word Nat) (z : Nat) :
    (dualMultipleBlockFiveVariableState w z).exponent =
      periodTwoFromTwoExponent (w.toList.count z) := by
  by_cases hzero : w.toList.count z = 0
  · simp [dualMultipleBlockFiveVariableState,
      DualMultipleBlockFiveState.exponent,
      periodTwoFromTwoExponent, hzero]
  · by_cases hone : w.toList.count z = 1
    · by_cases hhead : w.head = z <;>
        simp [dualMultipleBlockFiveVariableState,
          DualMultipleBlockFiveState.exponent,
          periodTwoFromTwoExponent, hone, hhead]
    · have hlarge : ¬w.toList.count z < 2 := by omega
      by_cases hparity : w.toList.count z % 2 = 0
      · simp [dualMultipleBlockFiveVariableState,
          DualMultipleBlockFiveState.exponent,
          periodTwoFromTwoExponent, hzero, hone, hlarge, hparity]
      · have hmod : w.toList.count z % 2 = 1 := by omega
        simp [dualMultipleBlockFiveVariableState,
          DualMultipleBlockFiveState.exponent,
          periodTwoFromTwoExponent, hzero, hone, hlarge, hmod]

private theorem dualMultipleBlockFiveState_singletonHead_iff
    (w : Word Nat) (z : Nat) :
    dualMultipleBlockFiveVariableState w z =
        .singletonHead ↔
      w.toList.count z = 1 ∧ w.head = z := by
  by_cases hzero : w.toList.count z = 0
  · simp [dualMultipleBlockFiveVariableState, hzero]
  · by_cases hone : w.toList.count z = 1
    · by_cases hhead : w.head = z <;>
        simp [dualMultipleBlockFiveVariableState, hone, hhead]
    · by_cases hparity : w.toList.count z % 2 = 0 <;>
        simp [dualMultipleBlockFiveVariableState, hzero, hone,
          hparity]

theorem dualMultipleBlockFiveSingletonHead_eq_some_iff
    (w : Word Nat) (z : Nat) :
    dualMultipleBlockFiveSingletonHead w = some z ↔
      dualMultipleBlockFiveVariableState w z =
        .singletonHead := by
  rw [dualMultipleBlockFiveState_singletonHead_iff]
  unfold dualMultipleBlockFiveSingletonHead
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

theorem dualMultipleBlockFiveBasis_complete :
    BasisFor dualMultipleBlockFive.semigroup
      dualMultipleBlockFiveBasis := by
  refine ⟨dualMultipleBlockFiveBasis_models, ?_⟩
  intro e valid
  apply dualMultipleBlockFiveDerivesOfInvariantEq
  · intro z
    rw [← dualMultipleBlockFiveVariableState_exponent e.lhs z,
      dualMultipleBlockFiveValid_state_eq e valid z,
      dualMultipleBlockFiveVariableState_exponent]
  · apply Option.ext
    intro z
    rw [dualMultipleBlockFiveSingletonHead_eq_some_iff,
      dualMultipleBlockFiveSingletonHead_eq_some_iff,
      dualMultipleBlockFiveValid_state_eq e valid z]

def dualMultipleBlockFiveStoredX : Word Nat := Word.singleton 0
def dualMultipleBlockFiveStoredXX : Word Nat := ⟨0, [0]⟩
def dualMultipleBlockFiveStoredXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def dualMultipleBlockFiveStoredXYX : Word Nat := ⟨0, [1, 0]⟩
def dualMultipleBlockFiveStoredYXX : Word Nat := ⟨1, [0, 0]⟩
def dualMultipleBlockFiveStoredXYZ : Word Nat := ⟨0, [1, 2]⟩
def dualMultipleBlockFiveStoredYXZ : Word Nat := ⟨1, [0, 2]⟩
def dualMultipleBlockFiveStoredXXYY : Word Nat := ⟨0, [0, 1, 1]⟩
def dualMultipleBlockFiveStoredXYYX : Word Nat := ⟨0, [1, 1, 0]⟩

def dualMultipleBlockFiveStoredPowerLaw : Identity Nat :=
  ⟨dualMultipleBlockFiveStoredXX, dualMultipleBlockFiveStoredXXXX⟩

def dualMultipleBlockFiveStoredGatherLaw : Identity Nat :=
  ⟨dualMultipleBlockFiveStoredXYX, dualMultipleBlockFiveStoredYXX⟩

def dualMultipleBlockFiveStoredPrefixSwapLaw : Identity Nat :=
  ⟨dualMultipleBlockFiveStoredXYZ, dualMultipleBlockFiveStoredYXZ⟩

def dualMultipleBlockFiveStoredSquareRotationLaw : Identity Nat :=
  ⟨dualMultipleBlockFiveStoredXXYY,
    dualMultipleBlockFiveStoredXYYX⟩

/-- The exact stored `S5_121` basis
`xx = xxxx`, `xyx = yxx`, `xyz = yxz`, `xxyy = xyyx`. -/
def dualMultipleBlockFiveStoredBasis : List (Identity Nat) :=
  [dualMultipleBlockFiveStoredPowerLaw,
    dualMultipleBlockFiveStoredGatherLaw,
    dualMultipleBlockFiveStoredPrefixSwapLaw,
    dualMultipleBlockFiveStoredSquareRotationLaw]

private def dualMultipleBlockFiveExactOppositeBasis :
    List (Identity Nat) :=
  reversedBasis dualMultipleBlockFiveStoredBasis

private def dualMultipleBlockFiveRenameReverseSwap
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => w
  | 1 => v
  | 2 => u
  | n + 3 => Word.singleton (n + 3)

private theorem dualMultipleBlockFiveNormalizedAxiomsDeriveExact :
    ∀ e : Identity Nat, e ∈ dualMultipleBlockFiveBasis →
      Derives dualMultipleBlockFiveExactOppositeBasis e.lhs e.rhs := by
  intro e he
  simp only [dualMultipleBlockFiveBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Derives.fromBasis <| by
      exact List.Mem.head _
  · exact Derives.fromBasis <| by
      exact List.Mem.tail _ (List.Mem.head _)
  · have exactLaw :
        Derives dualMultipleBlockFiveExactOppositeBasis
          (dualMultipleBlockFiveStoredPrefixSwapLaw.reversed.lhs)
          (dualMultipleBlockFiveStoredPrefixSwapLaw.reversed.rhs) :=
      Derives.fromBasis <| by
        exact List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)
    have renamed :=
      Derives.subst exactLaw
        (dualMultipleBlockFiveRenameReverseSwap
          (Word.singleton 0) (Word.singleton 1)
          (Word.singleton 2))
    simpa [dualMultipleBlockFiveStoredPrefixSwapLaw,
      dualMultipleBlockFiveStoredXYZ,
      dualMultipleBlockFiveStoredYXZ,
      Identity.reversed, Word.reverse, Word.bind,
      dualMultipleBlockFiveXYZ, dualMultipleBlockFiveXZY,
      dualMultipleBlockFiveRenameReverseSwap,
      Word.singleton, Word.append, Word.append_assoc] using renamed
  · exact Derives.fromBasis <| by
      exact List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)

private theorem dualMultipleBlockFiveExactAxiomsDeriveNormalized :
    ∀ e : Identity Nat,
      e ∈ dualMultipleBlockFiveExactOppositeBasis →
      Derives dualMultipleBlockFiveBasis e.lhs e.rhs := by
  intro e he
  simp only [dualMultipleBlockFiveExactOppositeBasis,
    dualMultipleBlockFiveStoredBasis, reversedBasis,
    List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Derives.fromBasis <| by
      exact List.Mem.head _
  · exact Derives.fromBasis <| by
      exact List.Mem.tail _ (List.Mem.head _)
  · have normalizedLaw :
        Derives dualMultipleBlockFiveBasis
          dualMultipleBlockFiveXYZ dualMultipleBlockFiveXZY :=
      Derives.fromBasis
          (e := dualMultipleBlockFiveSuffixSwapLaw) <| by
        exact List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)
    have renamed :=
      Derives.subst normalizedLaw
        (dualMultipleBlockFiveRenameReverseSwap
          (Word.singleton 0) (Word.singleton 1)
          (Word.singleton 2))
    simpa [dualMultipleBlockFiveStoredPrefixSwapLaw,
      dualMultipleBlockFiveStoredXYZ,
      dualMultipleBlockFiveStoredYXZ,
      Identity.reversed, Word.reverse, Word.bind,
      dualMultipleBlockFiveXYZ, dualMultipleBlockFiveXZY,
      dualMultipleBlockFiveRenameReverseSwap,
      Word.singleton, Word.append, Word.append_assoc] using renamed
  · exact Derives.fromBasis <| by
      exact List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)

private theorem dualMultipleBlockFiveExactOpposite_models :
    Models dualMultipleBlockFive.semigroup
      dualMultipleBlockFiveExactOppositeBasis := by
  intro e he valuation
  exact
    (dualMultipleBlockFiveExactAxiomsDeriveNormalized e he).sound
      dualMultipleBlockFiveBasis_models valuation

private theorem dualMultipleBlockFiveExactOppositeBasis_complete :
    BasisFor dualMultipleBlockFive.semigroup
      dualMultipleBlockFiveExactOppositeBasis :=
  dualMultipleBlockFiveBasis_complete.replace
    dualMultipleBlockFiveExactOpposite_models
    dualMultipleBlockFiveNormalizedAxiomsDeriveExact

private theorem dualMultipleBlockFiveReverseExactBasis :
    reversedBasis dualMultipleBlockFiveExactOppositeBasis =
      dualMultipleBlockFiveStoredBasis := by
  decide

/-- Completeness of the exact basis in the stored `S5_121` orientation. -/
theorem dualMultipleBlockFiveStoredBasis_complete :
    BasisFor dualMultipleBlockFiveStored.semigroup
      dualMultipleBlockFiveStoredBasis := by
  have reversed :=
    dualMultipleBlockFiveExactOppositeBasis_complete.oppositeReversed
  rw [dualMultipleBlockFiveReverseExactBasis] at reversed
  simpa [dualMultipleBlockFiveStored,
    dualMultipleBlockFiveStoredMul,
    dualMultipleBlockFive, FiniteTable.semigroup,
    Semigroup.opposite] using reversed

end SemigroupBasis.Examples

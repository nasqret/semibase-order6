import SemigroupBasis.Examples.CommutativePeriodThreeFromTwo
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

private def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def finiteBasis : List (Identity (Fin 2)) :=
  commutativePeriodThreeFromTwoBasis.map fun e => e.map toFinTwo

private theorem basisRoundTripChecked :
    commutativePeriodThreeFromTwoBasis.all (fun e =>
      decide ((e.map toFinTwo).map Fin.val = e)) = true := by
  decide

private theorem basisRoundTrip
    (e : Identity Nat) (member : e ∈ commutativePeriodThreeFromTwoBasis) :
    (e.map toFinTwo).map Fin.val = e := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basisRoundTripChecked) e member

private theorem modelsOfFiniteChecks
    (T : FiniteTable)
    (checked : finiteBasis.all T.checkIdentity = true) :
    Models T.semigroup commutativePeriodThreeFromTwoBasis := by
  intro e member
  have finiteMember : e.map toFinTwo ∈ finiteBasis :=
    List.mem_map.mpr ⟨e, member, rfl⟩
  have finiteValid :=
    T.checkIdentityNat_sound (e.map toFinTwo)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basisRoundTrip e member] at finiteValid
  exact finiteValid

private def exponentSeparator
    (target identity : Fin 5) (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then target else identity

private theorem exponentSeparatorFold
    (G : Semigroup (Fin 5))
    (state : Nat → Fin 5)
    (target identity : Fin 5)
    (mulTarget :
      ∀ n, G.mul (state n) target = state (n + 1))
    (mulIdentity :
      ∀ n, G.mul (state n) identity = state n)
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          G.mul current (exponentSeparator target identity z x))
        (state acc) =
      state (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show
          exponentSeparator target identity z z = target by
            simp [exponentSeparator]]
        rw [mulTarget, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show
          exponentSeparator target identity z x = identity by
            simp [exponentSeparator, hx]]
        rw [mulIdentity, ih]

private theorem evalExponentSeparator
    (G : Semigroup (Fin 5))
    (state : Nat → Fin 5)
    (target identity : Fin 5)
    (stateZero : state 0 = identity)
    (stateOne : state 1 = target)
    (mulTarget :
      ∀ n, G.mul (state n) target = state (n + 1))
    (mulIdentity :
      ∀ n, G.mul (state n) identity = state n)
    (z : Nat) (w : Word Nat) :
    G.eval (exponentSeparator target identity z) w =
      state (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              G.mul current
                (exponentSeparator target identity z x))
            (exponentSeparator target identity z head) =
          state ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show
          exponentSeparator target identity z z = state 1 by
            simp [exponentSeparator, stateOne]]
        rw [exponentSeparatorFold G state target identity
          mulTarget mulIdentity]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show
          exponentSeparator target identity z head = state 0 by
            simp [exponentSeparator, hhead, stateZero]]
        rw [exponentSeparatorFold G state target identity
          mulTarget mulIdentity]
        congr 1
        omega

/-! ## S5_1001 -/

/-- Exact zero-based multiplication for the Smallsemi representative
`S5_1001`, whose one-based table is
`[[1,1,1,1,1],[1,1,2,2,2],[1,2,3,4,5],
  [1,2,4,5,3],[1,2,5,3,4]]`. -/
def s5_1001Mul (a b : Fin 5) : Fin 5 :=
  if a = 0 then
    0
  else if a = 1 then
    if b = 0 then 0 else if b = 1 then 0 else
      if b = 2 then 1 else if b = 3 then 1 else 1
  else if a = 2 then
    if b = 0 then 0 else if b = 1 then 1 else
      if b = 2 then 2 else if b = 3 then 3 else 4
  else if a = 3 then
    if b = 0 then 0 else if b = 1 then 1 else
      if b = 2 then 3 else if b = 3 then 4 else 2
  else
    if b = 0 then 0 else if b = 1 then 1 else
      if b = 2 then 4 else if b = 3 then 2 else 3

/-- The exact order-five representative `S5_1001`. -/
def s5_1001 : FiniteTable where
  order := 5
  mul := s5_1001Mul
  assoc := by decide

private theorem s5_1001Mul_commutative (a b : Fin 5) :
    s5_1001Mul a b = s5_1001Mul b a := by
  apply Fin.ext
  revert a b
  decide

private theorem s5_1001Mul_identity (a : Fin 5) :
    s5_1001Mul a 2 = a := by
  apply Fin.ext
  revert a
  decide

set_option maxRecDepth 100000 in
/-- The exact `S5_1001` table models `xy = yx` and `x^2 = x^5`. -/
theorem s5_1001Models :
    Models s5_1001.semigroup commutativePeriodThreeFromTwoBasis :=
  modelsOfFiniteChecks s5_1001 (by decide)

/-- Powers of element `2` in one-based notation distinguish exponents zero,
one, and at least two. -/
def s5_1001ThresholdState (n : Nat) : Fin 5 :=
  if n = 0 then 2 else if n = 1 then 1 else 0

/-- Powers of element `4` in one-based notation record exponent modulo three. -/
def s5_1001PeriodState (n : Nat) : Fin 5 :=
  if n % 3 = 0 then 2 else if n % 3 = 1 then 3 else 4

def s5_1001ThresholdSeparator (z : Nat) : Nat → Fin 5 :=
  exponentSeparator 1 2 z

def s5_1001PeriodSeparator (z : Nat) : Nat → Fin 5 :=
  exponentSeparator 3 2 z

theorem s5_1001CanonicalThresholdStates :
    [0, 1, 2, 3, 4].map s5_1001ThresholdState =
      [(2 : Fin 5), 1, 0, 0, 0] := by
  decide

theorem s5_1001CanonicalPeriodStates :
    [0, 1, 2, 3, 4].map s5_1001PeriodState =
      [(2 : Fin 5), 3, 4, 2, 3] := by
  decide

private theorem s5_1001ThresholdMul_target (n : Nat) :
    s5_1001Mul (s5_1001ThresholdState n) 1 =
      s5_1001ThresholdState (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · simp [s5_1001Mul, s5_1001ThresholdState, hn0, hn1,
        show n + 1 ≠ 0 by omega, show n + 1 ≠ 1 by omega]

private theorem s5_1001PeriodMul_target (n : Nat) :
    s5_1001Mul (s5_1001PeriodState n) 3 =
      s5_1001PeriodState (n + 1) := by
  by_cases h0 : n % 3 = 0
  · have hnext : (n + 1) % 3 = 1 := by omega
    simp [s5_1001Mul, s5_1001PeriodState, h0, hnext]
  · by_cases h1 : n % 3 = 1
    · have hnext : (n + 1) % 3 = 2 := by omega
      simp [s5_1001Mul, s5_1001PeriodState, h0, h1, hnext]
    · have h2 : n % 3 = 2 := by omega
      have hnext : (n + 1) % 3 = 0 := by omega
      simp [s5_1001Mul, s5_1001PeriodState, h0, h1, h2, hnext]

theorem s5_1001EvalThresholdSeparator (z : Nat) (w : Word Nat) :
    s5_1001.semigroup.eval (s5_1001ThresholdSeparator z) w =
      s5_1001ThresholdState (w.toList.count z) := by
  exact
    evalExponentSeparator s5_1001.semigroup s5_1001ThresholdState 1 2
      (by rfl) (by rfl) s5_1001ThresholdMul_target
      (fun n => s5_1001Mul_identity (s5_1001ThresholdState n)) z w

theorem s5_1001EvalPeriodSeparator (z : Nat) (w : Word Nat) :
    s5_1001.semigroup.eval (s5_1001PeriodSeparator z) w =
      s5_1001PeriodState (w.toList.count z) := by
  exact
    evalExponentSeparator s5_1001.semigroup s5_1001PeriodState 3 2
      (by rfl) (by rfl) s5_1001PeriodMul_target
      (fun n => s5_1001Mul_identity (s5_1001PeriodState n)) z w

private def s5_1001ExponentCode
    (threshold period : Fin 5) : Nat :=
  if threshold = 2 then 0 else if threshold = 1 then 1 else
    if period = 4 then 2 else if period = 2 then 3 else 4

theorem s5_1001ExponentCode_states (n : Nat) :
    s5_1001ExponentCode
        (s5_1001ThresholdState n) (s5_1001PeriodState n) =
      periodThreeFromTwoExponent n := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · have hn2 : 2 ≤ n := by omega
      by_cases h0 : n % 3 = 0
      · have hnext : (n + 1) % 3 = 1 := by omega
        simp [s5_1001ExponentCode, s5_1001ThresholdState,
          s5_1001PeriodState, periodThreeFromTwoExponent,
          hn0, hn1, h0, hnext, show ¬n < 2 by omega]
      · by_cases h1 : n % 3 = 1
        · have hnext : (n + 1) % 3 = 2 := by omega
          simp [s5_1001ExponentCode, s5_1001ThresholdState,
            s5_1001PeriodState, periodThreeFromTwoExponent,
            hn0, hn1, h0, h1, hnext, show ¬n < 2 by omega]
        · have h2 : n % 3 = 2 := by omega
          have hnext : (n + 1) % 3 = 0 := by omega
          simp [s5_1001ExponentCode, s5_1001ThresholdState,
            s5_1001PeriodState, periodThreeFromTwoExponent,
            hn0, hn1, h0, h1, h2, hnext,
            show ¬n < 2 by omega]

private theorem periodThreeFromTwoExponent_eq_of_s5_1001States
    (m n : Nat)
    (thresholdEq :
      s5_1001ThresholdState m = s5_1001ThresholdState n)
    (periodEq : s5_1001PeriodState m = s5_1001PeriodState n) :
    periodThreeFromTwoExponent m =
      periodThreeFromTwoExponent n := by
  calc
    periodThreeFromTwoExponent m =
        s5_1001ExponentCode
          (s5_1001ThresholdState m) (s5_1001PeriodState m) :=
      (s5_1001ExponentCode_states m).symm
    _ = s5_1001ExponentCode
          (s5_1001ThresholdState n) (s5_1001PeriodState n) := by
      rw [thresholdEq, periodEq]
    _ = periodThreeFromTwoExponent n :=
      s5_1001ExponentCode_states n

/-- Every identity of `S5_1001` preserves all five canonical exponent states
for every variable. -/
theorem s5_1001Separates
    (e : Identity Nat) (valid : e.SatisfiedBy s5_1001.semigroup) :
    ∀ z,
      periodThreeFromTwoExponent (e.lhs.toList.count z) =
        periodThreeFromTwoExponent (e.rhs.toList.count z) := by
  intro z
  have thresholdEq := valid (s5_1001ThresholdSeparator z)
  have periodEq := valid (s5_1001PeriodSeparator z)
  rw [s5_1001EvalThresholdSeparator,
    s5_1001EvalThresholdSeparator] at thresholdEq
  rw [s5_1001EvalPeriodSeparator,
    s5_1001EvalPeriodSeparator] at periodEq
  exact periodThreeFromTwoExponent_eq_of_s5_1001States
    _ _ thresholdEq periodEq

/-- Complete unrestricted identity basis for `S5_1001`. -/
theorem s5_1001Basis :
    BasisFor s5_1001.semigroup commutativePeriodThreeFromTwoBasis :=
  commutativePeriodThreeFromTwoBasis_complete_of_separates
    s5_1001 s5_1001Models s5_1001Separates

theorem s5_1001SelfDual :
    s5_1001.semigroup.opposite = s5_1001.semigroup := by
  unfold s5_1001 FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  exact s5_1001Mul_commutative b a

theorem s5_1001OppositeBasis :
    BasisFor s5_1001.semigroup.opposite
      commutativePeriodThreeFromTwoBasis := by
  rw [s5_1001SelfDual]
  exact s5_1001Basis

/-! ## S5_1004 -/

/-- Exact zero-based multiplication for the Smallsemi representative
`S5_1004`, whose one-based table is
`[[1,1,1,4,5],[1,1,2,4,5],[1,2,3,4,5],
  [4,4,4,5,1],[5,5,5,1,4]]`. -/
def s5_1004Mul (a b : Fin 5) : Fin 5 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 0 else
      if b = 2 then 0 else if b = 3 then 3 else 4
  else if a = 1 then
    if b = 0 then 0 else if b = 1 then 0 else
      if b = 2 then 1 else if b = 3 then 3 else 4
  else if a = 2 then
    if b = 0 then 0 else if b = 1 then 1 else
      if b = 2 then 2 else if b = 3 then 3 else 4
  else if a = 3 then
    if b = 0 then 3 else if b = 1 then 3 else
      if b = 2 then 3 else if b = 3 then 4 else 0
  else
    if b = 0 then 4 else if b = 1 then 4 else
      if b = 2 then 4 else if b = 3 then 0 else 3

/-- The exact order-five representative `S5_1004`. -/
def s5_1004 : FiniteTable where
  order := 5
  mul := s5_1004Mul
  assoc := by decide

private theorem s5_1004Mul_commutative (a b : Fin 5) :
    s5_1004Mul a b = s5_1004Mul b a := by
  apply Fin.ext
  revert a b
  decide

private theorem s5_1004Mul_identity (a : Fin 5) :
    s5_1004Mul a 2 = a := by
  apply Fin.ext
  revert a
  decide

set_option maxRecDepth 100000 in
/-- The exact `S5_1004` table models `xy = yx` and `x^2 = x^5`. -/
theorem s5_1004Models :
    Models s5_1004.semigroup commutativePeriodThreeFromTwoBasis :=
  modelsOfFiniteChecks s5_1004 (by decide)

/-- Powers of element `2` in one-based notation distinguish exponents zero,
one, and at least two. -/
def s5_1004ThresholdState (n : Nat) : Fin 5 :=
  if n = 0 then 2 else if n = 1 then 1 else 0

/-- Powers of element `4` in one-based notation distinguish the three
periodic states after the identity state. -/
def s5_1004PeriodState (n : Nat) : Fin 5 :=
  if n = 0 then 2 else if n % 3 = 0 then 0 else
    if n % 3 = 1 then 3 else 4

def s5_1004ThresholdSeparator (z : Nat) : Nat → Fin 5 :=
  exponentSeparator 1 2 z

def s5_1004PeriodSeparator (z : Nat) : Nat → Fin 5 :=
  exponentSeparator 3 2 z

theorem s5_1004CanonicalThresholdStates :
    [0, 1, 2, 3, 4].map s5_1004ThresholdState =
      [(2 : Fin 5), 1, 0, 0, 0] := by
  decide

theorem s5_1004CanonicalPeriodStates :
    [0, 1, 2, 3, 4].map s5_1004PeriodState =
      [(2 : Fin 5), 3, 4, 0, 3] := by
  decide

private theorem s5_1004ThresholdMul_target (n : Nat) :
    s5_1004Mul (s5_1004ThresholdState n) 1 =
      s5_1004ThresholdState (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · simp [s5_1004Mul, s5_1004ThresholdState, hn0, hn1,
        show n + 1 ≠ 0 by omega, show n + 1 ≠ 1 by omega]

private theorem s5_1004PeriodMul_target (n : Nat) :
    s5_1004Mul (s5_1004PeriodState n) 3 =
      s5_1004PeriodState (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases h0 : n % 3 = 0
    · have hnext : (n + 1) % 3 = 1 := by omega
      simp [s5_1004Mul, s5_1004PeriodState, hn0, h0, hnext,
        show n + 1 ≠ 0 by omega]
    · by_cases h1 : n % 3 = 1
      · have hnext : (n + 1) % 3 = 2 := by omega
        simp [s5_1004Mul, s5_1004PeriodState, hn0, h0, h1, hnext,
          show n + 1 ≠ 0 by omega]
      · have h2 : n % 3 = 2 := by omega
        have hnext : (n + 1) % 3 = 0 := by omega
        simp [s5_1004Mul, s5_1004PeriodState, hn0, h0, h1, h2,
          hnext, show n + 1 ≠ 0 by omega]

theorem s5_1004EvalThresholdSeparator (z : Nat) (w : Word Nat) :
    s5_1004.semigroup.eval (s5_1004ThresholdSeparator z) w =
      s5_1004ThresholdState (w.toList.count z) := by
  exact
    evalExponentSeparator s5_1004.semigroup s5_1004ThresholdState 1 2
      (by rfl) (by rfl) s5_1004ThresholdMul_target
      (fun n => s5_1004Mul_identity (s5_1004ThresholdState n)) z w

theorem s5_1004EvalPeriodSeparator (z : Nat) (w : Word Nat) :
    s5_1004.semigroup.eval (s5_1004PeriodSeparator z) w =
      s5_1004PeriodState (w.toList.count z) := by
  exact
    evalExponentSeparator s5_1004.semigroup s5_1004PeriodState 3 2
      (by rfl) (by rfl) s5_1004PeriodMul_target
      (fun n => s5_1004Mul_identity (s5_1004PeriodState n)) z w

private def s5_1004ExponentCode
    (threshold period : Fin 5) : Nat :=
  if threshold = 2 then 0 else if threshold = 1 then 1 else
    if period = 4 then 2 else if period = 0 then 3 else 4

theorem s5_1004ExponentCode_states (n : Nat) :
    s5_1004ExponentCode
        (s5_1004ThresholdState n) (s5_1004PeriodState n) =
      periodThreeFromTwoExponent n := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · have hn2 : 2 ≤ n := by omega
      by_cases h0 : n % 3 = 0
      · have hnext : (n + 1) % 3 = 1 := by omega
        simp [s5_1004ExponentCode, s5_1004ThresholdState,
          s5_1004PeriodState, periodThreeFromTwoExponent,
          hn0, hn1, h0, hnext, show ¬n < 2 by omega]
      · by_cases h1 : n % 3 = 1
        · have hnext : (n + 1) % 3 = 2 := by omega
          simp [s5_1004ExponentCode, s5_1004ThresholdState,
            s5_1004PeriodState, periodThreeFromTwoExponent,
            hn0, hn1, h0, h1, hnext, show ¬n < 2 by omega]
        · have h2 : n % 3 = 2 := by omega
          have hnext : (n + 1) % 3 = 0 := by omega
          simp [s5_1004ExponentCode, s5_1004ThresholdState,
            s5_1004PeriodState, periodThreeFromTwoExponent,
            hn0, hn1, h0, h1, h2, hnext,
            show ¬n < 2 by omega]

private theorem periodThreeFromTwoExponent_eq_of_s5_1004States
    (m n : Nat)
    (thresholdEq :
      s5_1004ThresholdState m = s5_1004ThresholdState n)
    (periodEq : s5_1004PeriodState m = s5_1004PeriodState n) :
    periodThreeFromTwoExponent m =
      periodThreeFromTwoExponent n := by
  calc
    periodThreeFromTwoExponent m =
        s5_1004ExponentCode
          (s5_1004ThresholdState m) (s5_1004PeriodState m) :=
      (s5_1004ExponentCode_states m).symm
    _ = s5_1004ExponentCode
          (s5_1004ThresholdState n) (s5_1004PeriodState n) := by
      rw [thresholdEq, periodEq]
    _ = periodThreeFromTwoExponent n :=
      s5_1004ExponentCode_states n

/-- Every identity of `S5_1004` preserves all five canonical exponent states
for every variable. -/
theorem s5_1004Separates
    (e : Identity Nat) (valid : e.SatisfiedBy s5_1004.semigroup) :
    ∀ z,
      periodThreeFromTwoExponent (e.lhs.toList.count z) =
        periodThreeFromTwoExponent (e.rhs.toList.count z) := by
  intro z
  have thresholdEq := valid (s5_1004ThresholdSeparator z)
  have periodEq := valid (s5_1004PeriodSeparator z)
  rw [s5_1004EvalThresholdSeparator,
    s5_1004EvalThresholdSeparator] at thresholdEq
  rw [s5_1004EvalPeriodSeparator,
    s5_1004EvalPeriodSeparator] at periodEq
  exact periodThreeFromTwoExponent_eq_of_s5_1004States
    _ _ thresholdEq periodEq

/-- Complete unrestricted identity basis for `S5_1004`. -/
theorem s5_1004Basis :
    BasisFor s5_1004.semigroup commutativePeriodThreeFromTwoBasis :=
  commutativePeriodThreeFromTwoBasis_complete_of_separates
    s5_1004 s5_1004Models s5_1004Separates

theorem s5_1004SelfDual :
    s5_1004.semigroup.opposite = s5_1004.semigroup := by
  unfold s5_1004 FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  exact s5_1004Mul_commutative b a

theorem s5_1004OppositeBasis :
    BasisFor s5_1004.semigroup.opposite
      commutativePeriodThreeFromTwoBasis := by
  rw [s5_1004SelfDual]
  exact s5_1004Basis

/-! ## S5_1156 -/

/-- Exact zero-based multiplication for the Smallsemi representative
`S5_1156`, whose one-based table is
`[[1,1,3,4,4],[1,2,3,4,5],[3,3,4,1,1],
  [4,4,1,3,3],[4,5,1,3,3]]`. -/
def s5_1156Mul (a b : Fin 5) : Fin 5 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 0 else
      if b = 2 then 2 else if b = 3 then 3 else 3
  else if a = 1 then
    if b = 0 then 0 else if b = 1 then 1 else
      if b = 2 then 2 else if b = 3 then 3 else 4
  else if a = 2 then
    if b = 0 then 2 else if b = 1 then 2 else
      if b = 2 then 3 else if b = 3 then 0 else 0
  else if a = 3 then
    if b = 0 then 3 else if b = 1 then 3 else
      if b = 2 then 0 else if b = 3 then 2 else 2
  else
    if b = 0 then 3 else if b = 1 then 4 else
      if b = 2 then 0 else if b = 3 then 2 else 2

/-- The exact order-five representative `S5_1156`. -/
def s5_1156 : FiniteTable where
  order := 5
  mul := s5_1156Mul
  assoc := by decide

private theorem s5_1156Mul_commutative (a b : Fin 5) :
    s5_1156Mul a b = s5_1156Mul b a := by
  apply Fin.ext
  revert a b
  decide

private theorem s5_1156Mul_identity (a : Fin 5) :
    s5_1156Mul a 1 = a := by
  apply Fin.ext
  revert a
  decide

set_option maxRecDepth 100000 in
/-- The exact `S5_1156` table models `xy = yx` and `x^2 = x^5`. -/
theorem s5_1156Models :
    Models s5_1156.semigroup commutativePeriodThreeFromTwoBasis :=
  modelsOfFiniteChecks s5_1156 (by decide)

/-- Powers of element `5` in one-based notation directly encode all five
canonical exponent states. -/
def s5_1156ExponentState (n : Nat) : Fin 5 :=
  if n = 0 then 1 else if n = 1 then 4 else
    if n % 3 = 2 then 2 else if n % 3 = 0 then 0 else 3

def s5_1156ExponentSeparator (z : Nat) : Nat → Fin 5 :=
  exponentSeparator 4 1 z

theorem s5_1156CanonicalExponentStates :
    [0, 1, 2, 3, 4].map s5_1156ExponentState =
      [(1 : Fin 5), 4, 2, 0, 3] := by
  decide

private theorem s5_1156ExponentMul_target (n : Nat) :
    s5_1156Mul (s5_1156ExponentState n) 4 =
      s5_1156ExponentState (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · by_cases h2 : n % 3 = 2
      · have hnext : (n + 1) % 3 = 0 := by omega
        simp [s5_1156Mul, s5_1156ExponentState, hn0, hn1,
          h2, hnext, show n + 1 ≠ 0 by omega,
          show n + 1 ≠ 1 by omega]
      · by_cases h0 : n % 3 = 0
        · have hnext : (n + 1) % 3 = 1 := by omega
          simp [s5_1156Mul, s5_1156ExponentState, hn0, hn1,
            h2, h0, hnext, show n + 1 ≠ 0 by omega,
            show n + 1 ≠ 1 by omega]
        · have h1 : n % 3 = 1 := by omega
          have hnext : (n + 1) % 3 = 2 := by omega
          simp [s5_1156Mul, s5_1156ExponentState, hn0, hn1,
            h2, h0, h1, hnext, show n + 1 ≠ 0 by omega,
            show n + 1 ≠ 1 by omega]

theorem s5_1156EvalExponentSeparator (z : Nat) (w : Word Nat) :
    s5_1156.semigroup.eval (s5_1156ExponentSeparator z) w =
      s5_1156ExponentState (w.toList.count z) := by
  exact
    evalExponentSeparator s5_1156.semigroup s5_1156ExponentState 4 1
      (by rfl) (by rfl) s5_1156ExponentMul_target
      (fun n => s5_1156Mul_identity (s5_1156ExponentState n)) z w

private def s5_1156ExponentCode (state : Fin 5) : Nat :=
  if state = 1 then 0 else if state = 4 then 1 else
    if state = 2 then 2 else if state = 0 then 3 else 4

theorem s5_1156ExponentCode_state (n : Nat) :
    s5_1156ExponentCode (s5_1156ExponentState n) =
      periodThreeFromTwoExponent n := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · have hn2 : 2 ≤ n := by omega
      by_cases h2 : n % 3 = 2
      · have hnext : (n + 1) % 3 = 0 := by omega
        simp [s5_1156ExponentCode, s5_1156ExponentState,
          periodThreeFromTwoExponent, hn0, hn1, h2, hnext,
          show ¬n < 2 by omega]
      · by_cases h0 : n % 3 = 0
        · have hnext : (n + 1) % 3 = 1 := by omega
          simp [s5_1156ExponentCode, s5_1156ExponentState,
            periodThreeFromTwoExponent, hn0, hn1, h2, h0, hnext,
            show ¬n < 2 by omega]
        · have h1 : n % 3 = 1 := by omega
          have hnext : (n + 1) % 3 = 2 := by omega
          simp [s5_1156ExponentCode, s5_1156ExponentState,
            periodThreeFromTwoExponent, hn0, hn1, h2, h0, h1,
            hnext, show ¬n < 2 by omega]

private theorem periodThreeFromTwoExponent_eq_of_s5_1156State
    (m n : Nat)
    (stateEq : s5_1156ExponentState m = s5_1156ExponentState n) :
    periodThreeFromTwoExponent m =
      periodThreeFromTwoExponent n := by
  calc
    periodThreeFromTwoExponent m =
        s5_1156ExponentCode (s5_1156ExponentState m) :=
      (s5_1156ExponentCode_state m).symm
    _ = s5_1156ExponentCode (s5_1156ExponentState n) := by
      rw [stateEq]
    _ = periodThreeFromTwoExponent n :=
      s5_1156ExponentCode_state n

/-- Every identity of `S5_1156` preserves all five canonical exponent states
for every variable. -/
theorem s5_1156Separates
    (e : Identity Nat) (valid : e.SatisfiedBy s5_1156.semigroup) :
    ∀ z,
      periodThreeFromTwoExponent (e.lhs.toList.count z) =
        periodThreeFromTwoExponent (e.rhs.toList.count z) := by
  intro z
  have stateEq := valid (s5_1156ExponentSeparator z)
  rw [s5_1156EvalExponentSeparator,
    s5_1156EvalExponentSeparator] at stateEq
  exact periodThreeFromTwoExponent_eq_of_s5_1156State _ _ stateEq

/-- Complete unrestricted identity basis for `S5_1156`. -/
theorem s5_1156Basis :
    BasisFor s5_1156.semigroup commutativePeriodThreeFromTwoBasis :=
  commutativePeriodThreeFromTwoBasis_complete_of_separates
    s5_1156 s5_1156Models s5_1156Separates

theorem s5_1156SelfDual :
    s5_1156.semigroup.opposite = s5_1156.semigroup := by
  unfold s5_1156 FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  exact s5_1156Mul_commutative b a

theorem s5_1156OppositeBasis :
    BasisFor s5_1156.semigroup.opposite
      commutativePeriodThreeFromTwoBasis := by
  rw [s5_1156SelfDual]
  exact s5_1156Basis

end SemigroupBasis.Examples

import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo
import SemigroupBasis.FiniteReflection

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Exact zero-based multiplication for the Smallsemi representative `S4_32`,
whose one-based table is
`[[1,2,2,1],[2,1,1,2],[2,1,1,3],[1,2,3,4]]`. -/
def s4_32Mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 1 else
      if b = 2 then 1 else 0
  else if a = 1 then
    if b = 0 then 1 else if b = 1 then 0 else
      if b = 2 then 0 else 1
  else if a = 2 then
    if b = 0 then 1 else if b = 1 then 0 else
      if b = 2 then 0 else 2
  else
    b

/-- The exact four-element Smallsemi representative `S4_32`. -/
def s4_32 : FiniteTable where
  order := 4
  mul := s4_32Mul
  assoc := by decide

private def s4_32FinitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

private def s4_32FiniteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

private theorem s4_32FinitePowerLaw_map :
    s4_32FinitePowerLaw.map Fin.val =
      periodTwoFromTwoPowerLaw := rfl

private theorem s4_32FiniteCommutativityLaw_map :
    s4_32FiniteCommutativityLaw.map Fin.val =
      periodTwoFromTwoCommutativityLaw := rfl

/-- The exact S4_32 table satisfies `xx = xxxx` and `xy = yx`. -/
theorem s4_32Models :
    Models s4_32.semigroup commutativePeriodTwoFromTwoBasis := by
  intro e he
  simp only [commutativePeriodTwoFromTwoBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← s4_32FinitePowerLaw_map]
    exact s4_32.checkIdentityNat_sound s4_32FinitePowerLaw (by decide)
  · rw [← s4_32FiniteCommutativityLaw_map]
    exact
      s4_32.checkIdentityNat_sound
        s4_32FiniteCommutativityLaw (by decide)

/-- The powers of element `3` in the one-based table encode all four
normalized exponent states: zero, one, positive even, and odd at least three. -/
private def s4_32ExponentState (n : Nat) : Fin 4 :=
  if n = 0 then 3 else if n = 1 then 2 else
    if n % 2 = 0 then 0 else 1

private def s4_32ExponentSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 3

private theorem s4_32ExponentMul_target (n : Nat) :
    s4_32Mul (s4_32ExponentState n) 2 =
      s4_32ExponentState (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · by_cases hp : n % 2 = 0
      · have hnext : (n + 1) % 2 = 1 := by omega
        simp [s4_32Mul, s4_32ExponentState, hn0, hn1, hp, hnext]
      · have hmod : n % 2 = 1 := by omega
        have hnext : (n + 1) % 2 = 0 := by omega
        simp [s4_32Mul, s4_32ExponentState, hn0, hn1, hmod, hnext]

private theorem s4_32ExponentMul_other (n : Nat) :
    s4_32Mul (s4_32ExponentState n) 3 =
      s4_32ExponentState n := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · by_cases hp : n % 2 = 0
      · simp [s4_32Mul, s4_32ExponentState, hn0, hn1, hp]
      · have hmod : n % 2 = 1 := by omega
        simp [s4_32Mul, s4_32ExponentState, hn0, hn1, hmod]

private theorem s4_32ExponentFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          s4_32Mul current (s4_32ExponentSeparator z x))
        (s4_32ExponentState acc) =
      s4_32ExponentState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show s4_32ExponentSeparator z z = (2 : Fin 4) by
          simp [s4_32ExponentSeparator]]
        rw [s4_32ExponentMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show s4_32ExponentSeparator z x = (3 : Fin 4) by
          simp [s4_32ExponentSeparator, hx]]
        rw [s4_32ExponentMul_other, ih]

theorem s4_32EvalExponentSeparator (z : Nat) (w : Word Nat) :
    s4_32.semigroup.eval (s4_32ExponentSeparator z) w =
      s4_32ExponentState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              s4_32Mul current (s4_32ExponentSeparator z x))
            (s4_32ExponentSeparator z head) =
          s4_32ExponentState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show
          s4_32ExponentSeparator z z = s4_32ExponentState 1 by
            apply Fin.ext
            simp [s4_32ExponentSeparator, s4_32ExponentState]]
        rw [s4_32ExponentFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show
          s4_32ExponentSeparator z head = s4_32ExponentState 0 by
            apply Fin.ext
            simp [s4_32ExponentSeparator, s4_32ExponentState, hhead]]
        rw [s4_32ExponentFold]
        congr 1
        omega

private theorem periodTwoFromTwoExponent_eq_of_s4_32State_eq
    (m n : Nat)
    (stateEq : s4_32ExponentState m = s4_32ExponentState n) :
    periodTwoFromTwoExponent m =
      periodTwoFromTwoExponent n := by
  by_cases hm0 : m = 0
  · subst m
    have hn0 : n = 0 := by
      by_cases hn0 : n = 0
      · exact hn0
      · by_cases hn1 : n = 1
        · subst n
          simp [s4_32ExponentState] at stateEq
        · by_cases hnParity : n % 2 = 0
          · simp [s4_32ExponentState, hn0, hn1, hnParity] at stateEq
          · have hnMod : n % 2 = 1 := by omega
            simp [s4_32ExponentState, hn0, hn1, hnMod] at stateEq
    subst n
    rfl
  · by_cases hm1 : m = 1
    · subst m
      have hn1 : n = 1 := by
        by_cases hn1 : n = 1
        · exact hn1
        · by_cases hn0 : n = 0
          · subst n
            simp [s4_32ExponentState] at stateEq
          · by_cases hnParity : n % 2 = 0
            · simp [s4_32ExponentState, hn0, hn1, hnParity] at stateEq
            · have hnMod : n % 2 = 1 := by omega
              simp [s4_32ExponentState, hn0, hn1, hnMod] at stateEq
      subst n
      rfl
    · have hn0 : n ≠ 0 := by
        intro hn0
        subst n
        by_cases hmParity : m % 2 = 0
        · simp [s4_32ExponentState, hm0, hm1, hmParity] at stateEq
        · have hmMod : m % 2 = 1 := by omega
          simp [s4_32ExponentState, hm0, hm1, hmMod] at stateEq
      have hn1 : n ≠ 1 := by
        intro hn1
        subst n
        by_cases hmParity : m % 2 = 0
        · simp [s4_32ExponentState, hm0, hm1, hmParity] at stateEq
        · have hmMod : m % 2 = 1 := by omega
          simp [s4_32ExponentState, hm0, hm1, hmMod] at stateEq
      have hparity : m % 2 = n % 2 := by
        by_cases hmParity : m % 2 = 0
        · by_cases hnParity : n % 2 = 0
          · omega
          · have hnMod : n % 2 = 1 := by omega
            simp [s4_32ExponentState, hm0, hm1, hn0, hn1,
              hmParity, hnMod] at stateEq
        · have hmMod : m % 2 = 1 := by omega
          by_cases hnParity : n % 2 = 0
          · simp [s4_32ExponentState, hm0, hm1, hn0, hn1,
              hmMod, hnParity] at stateEq
          · have hnMod : n % 2 = 1 := by omega
            omega
      simp [periodTwoFromTwoExponent, show ¬m < 2 by omega,
        show ¬n < 2 by omega, hparity]

/-- Every identity of S4_32 preserves the four canonical exponent states for
each variable. -/
theorem s4_32Separates
    (e : Identity Nat)
    (valid : e.SatisfiedBy s4_32.semigroup) :
    ∀ z,
      periodTwoFromTwoExponent (e.lhs.toList.count z) =
        periodTwoFromTwoExponent (e.rhs.toList.count z) := by
  intro z
  have stateEq := valid (s4_32ExponentSeparator z)
  rw [s4_32EvalExponentSeparator, s4_32EvalExponentSeparator] at stateEq
  exact
    periodTwoFromTwoExponent_eq_of_s4_32State_eq _ _ stateEq

/-- Complete semantic identity-basis theorem for the catalogue semigroup
`S4_32`: `xx = xxxx`, `xy = yx`. -/
theorem s4_32Basis :
    BasisFor s4_32.semigroup commutativePeriodTwoFromTwoBasis :=
  commutativePeriodTwoFromTwoBasis_complete_of_separates
    s4_32 s4_32Models s4_32Separates

end SemigroupBasis.Examples

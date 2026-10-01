import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_28

open SemigroupBasis
open SemigroupBasis.Examples

/-- The zero-based multiplication of the stored Smallsemi representative
`S4_28`, whose one-based table is
`[[1,1,3,1],[1,1,3,2],[3,3,1,3],[1,2,3,4]]`. -/
def s4_28Mul (a b : Fin 4) : Fin 4 :=
  SemigroupBasis.Generated.Catalogue.S4_28.mul a b

def table : FiniteTable where
  order := 4
  mul := s4_28Mul
  assoc := by decide

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_28.table := rfl

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = periodTwoFromTwoPowerLaw := rfl

theorem finiteCommutativityLaw_map :
    finiteCommutativityLaw.map Fin.val =
      periodTwoFromTwoCommutativityLaw := rfl

theorem representative_models :
    Models table.semigroup commutativePeriodTwoFromTwoBasis := by
  intro e he
  simp only [commutativePeriodTwoFromTwoBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteCommutativityLaw_map]
    exact table.checkIdentityNat_sound finiteCommutativityLaw (by decide)

private def thresholdState (n : Nat) : Fin 4 :=
  if n = 0 then 3 else if n = 1 then 1 else 0

private def thresholdSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 3

private theorem thresholdMul_target (n : Nat) :
    s4_28Mul (thresholdState n) 1 =
      thresholdState (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · simp [s4_28Mul, SemigroupBasis.Generated.Catalogue.S4_28.mul,
        thresholdState, hn0, hn1]

private theorem thresholdMul_other (n : Nat) :
    s4_28Mul (thresholdState n) 3 = thresholdState n := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · simp [s4_28Mul, SemigroupBasis.Generated.Catalogue.S4_28.mul,
        thresholdState, hn0, hn1]

private theorem thresholdFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          s4_28Mul current (thresholdSeparator z x))
        (thresholdState acc) =
      thresholdState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show thresholdSeparator z z = (1 : Fin 4) by
          simp [thresholdSeparator]]
        rw [thresholdMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show thresholdSeparator z x = (3 : Fin 4) by
          simp [thresholdSeparator, hx]]
        rw [thresholdMul_other, ih]

theorem eval_thresholdSeparator (z : Nat) (w : Word Nat) :
    table.semigroup.eval (thresholdSeparator z) w =
      thresholdState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              s4_28Mul current (thresholdSeparator z x))
            (thresholdSeparator z head) =
          thresholdState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show thresholdSeparator z z = thresholdState 1 by
          apply Fin.ext
          simp [thresholdSeparator, thresholdState]]
        rw [thresholdFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show thresholdSeparator z head = thresholdState 0 by
          apply Fin.ext
          simp [thresholdSeparator, thresholdState, hhead]]
        rw [thresholdFold]
        congr 1
        omega

private def parityState (n : Nat) : Fin 4 :=
  if n = 0 then 3 else if n % 2 = 0 then 0 else 2

private def paritySeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 3

private theorem parityMul_target (n : Nat) :
    s4_28Mul (parityState n) 2 =
      parityState (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hp : n % 2 = 0
    · have hnext : (n + 1) % 2 = 1 := by omega
      simp [s4_28Mul, SemigroupBasis.Generated.Catalogue.S4_28.mul,
        parityState, hn0, hp, hnext]
    · have hmod : n % 2 = 1 := by omega
      have hnext : (n + 1) % 2 = 0 := by omega
      simp [s4_28Mul, SemigroupBasis.Generated.Catalogue.S4_28.mul,
        parityState, hn0, hmod, hnext]

private theorem parityMul_other (n : Nat) :
    s4_28Mul (parityState n) 3 = parityState n := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hp : n % 2 = 0
    · simp [s4_28Mul, SemigroupBasis.Generated.Catalogue.S4_28.mul,
        parityState, hn0, hp]
    · have hmod : n % 2 = 1 := by omega
      simp [s4_28Mul, SemigroupBasis.Generated.Catalogue.S4_28.mul,
        parityState, hn0, hmod]

private theorem parityFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          s4_28Mul current (paritySeparator z x))
        (parityState acc) =
      parityState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show paritySeparator z z = (2 : Fin 4) by
          simp [paritySeparator]]
        rw [parityMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show paritySeparator z x = (3 : Fin 4) by
          simp [paritySeparator, hx]]
        rw [parityMul_other, ih]

theorem eval_paritySeparator (z : Nat) (w : Word Nat) :
    table.semigroup.eval (paritySeparator z) w =
      parityState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              s4_28Mul current (paritySeparator z x))
            (paritySeparator z head) =
          parityState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show paritySeparator z z = parityState 1 by
          apply Fin.ext
          simp [paritySeparator, parityState]]
        rw [parityFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show paritySeparator z head = parityState 0 by
          apply Fin.ext
          simp [paritySeparator, parityState, hhead]]
        rw [parityFold]
        congr 1
        omega

private theorem exponent_eq_of_separator_states
    (m n : Nat)
    (thresholdEq : thresholdState m = thresholdState n)
    (parityEq : parityState m = parityState n) :
    periodTwoFromTwoExponent m =
      periodTwoFromTwoExponent n := by
  by_cases hm0 : m = 0
  · subst m
    have hn0 : n = 0 := by
      by_cases hn0 : n = 0
      · exact hn0
      · by_cases hn1 : n = 1
        · subst n
          simp [thresholdState] at thresholdEq
        · simp [thresholdState, hn0, hn1] at thresholdEq
    subst n
    rfl
  · by_cases hm1 : m = 1
    · subst m
      have hn1 : n = 1 := by
        by_cases hn1 : n = 1
        · exact hn1
        · by_cases hn0 : n = 0
          · subst n
            simp [thresholdState] at thresholdEq
          · simp [thresholdState, hn0, hn1] at thresholdEq
      subst n
      rfl
    · have hn0 : n ≠ 0 := by
        intro hn0
        subst n
        simp [thresholdState, hm0, hm1] at thresholdEq
      have hn1 : n ≠ 1 := by
        intro hn1
        subst n
        simp [thresholdState, hm0, hm1] at thresholdEq
      have hparity : m % 2 = n % 2 := by
        by_cases hm : m % 2 = 0
        · by_cases hn : n % 2 = 0
          · omega
          · have hnmod : n % 2 = 1 := by omega
            simp [parityState, hm0, hn0, hm, hnmod] at parityEq
        · have hmmod : m % 2 = 1 := by omega
          by_cases hn : n % 2 = 0
          · simp [parityState, hm0, hn0, hmmod, hn] at parityEq
          · have hnmod : n % 2 = 1 := by omega
            omega
      simp [periodTwoFromTwoExponent, show ¬m < 2 by omega,
        show ¬n < 2 by omega, hparity]

theorem representative_separates
    (e : Identity Nat)
    (valid : e.SatisfiedBy table.semigroup) :
    ∀ z,
      periodTwoFromTwoExponent (e.lhs.toList.count z) =
        periodTwoFromTwoExponent (e.rhs.toList.count z) := by
  intro z
  have thresholdEq := valid (thresholdSeparator z)
  have parityEq := valid (paritySeparator z)
  rw [eval_thresholdSeparator, eval_thresholdSeparator] at thresholdEq
  rw [eval_paritySeparator, eval_paritySeparator] at parityEq
  exact exponent_eq_of_separator_states _ _ thresholdEq parityEq

theorem representative_basis :
    BasisFor table.semigroup commutativePeriodTwoFromTwoBasis :=
  commutativePeriodTwoFromTwoBasis_complete_of_separates
    table representative_models representative_separates

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      commutativePeriodTwoFromTwoBasis :=
  commutativePeriodTwoFromTwoBasis_opposite_complete
    representative_basis

end SemigroupBasis.Generated.S4_28

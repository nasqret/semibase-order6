import SemigroupBasis.Examples.CommutativePositiveModSixFive

namespace SemigroupBasis.CoRoots.S5_1007

open SemigroupBasis
open SemigroupBasis.Examples

abbrev basis : List (Identity Nat) :=
  commutativePositiveModSixBasis

def countSeparator
    (target other : Fin 5) (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then target else other

theorem countSeparatorFold
    (G : Semigroup (Fin 5))
    (state : Nat → Fin 5)
    (target other : Fin 5)
    (mulTarget :
      ∀ n, G.mul (state n) target = state (n + 1))
    (mulOther :
      ∀ n, G.mul (state n) other = state n)
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          G.mul current (countSeparator target other z x))
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
        rw [show countSeparator target other z z = target by
          simp [countSeparator]]
        rw [mulTarget, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show countSeparator target other z x = other by
          simp [countSeparator, hx]]
        rw [mulOther, ih]

theorem evalCountSeparator
    (G : Semigroup (Fin 5))
    (state : Nat → Fin 5)
    (target other : Fin 5)
    (stateZero : state 0 = other)
    (stateOne : state 1 = target)
    (mulTarget :
      ∀ n, G.mul (state n) target = state (n + 1))
    (mulOther :
      ∀ n, G.mul (state n) other = state n)
    (z : Nat) (w : Word Nat) :
    G.eval (countSeparator target other z) w =
      state (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              G.mul current (countSeparator target other z x))
            (countSeparator target other z head) =
          state ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show countSeparator target other z z = state 1 by
          simp [countSeparator, stateOne]]
        rw [countSeparatorFold G state target other
          mulTarget mulOther]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show countSeparator target other z head = state 0 by
          simp [countSeparator, hhead, stateZero]]
        rw [countSeparatorFold G state target other
          mulTarget mulOther]
        congr 1
        omega

/-- The `C2` power states in zero-based catalogue notation. -/
def positiveModSixParityState (n : Nat) : Fin 5 :=
  if n % 2 = 0 then 0 else 1

def positiveModSixParityCode (value : Fin 5) : Nat :=
  if value = 0 then 0
  else 1

theorem positiveModSixParityCode_state (n : Nat) :
    positiveModSixParityCode (positiveModSixParityState n) =
      n % 2 := by
  by_cases h0 : n % 2 = 0
  · simp [positiveModSixParityState,
      positiveModSixParityCode, h0]
  · have h1 : n % 2 = 1 := by
      omega
    simp [positiveModSixParityState,
      positiveModSixParityCode, h0, h1]

theorem modTwo_eq_of_parityState_eq
    {m n : Nat}
    (equal :
      positiveModSixParityState m =
        positiveModSixParityState n) :
    m % 2 = n % 2 := by
  calc
    m % 2 =
        positiveModSixParityCode
          (positiveModSixParityState m) :=
      (positiveModSixParityCode_state m).symm
    _ = positiveModSixParityCode
          (positiveModSixParityState n) := by
      rw [equal]
    _ = n % 2 :=
      positiveModSixParityCode_state n

/-- The `C3` power states in zero-based catalogue notation. -/
def positiveModSixTernaryState (n : Nat) : Fin 5 :=
  if n % 3 = 0 then 2
  else if n % 3 = 1 then 3
  else 4

def positiveModSixTernaryCode (value : Fin 5) : Nat :=
  if value = 2 then 0
  else if value = 3 then 1
  else 2

theorem positiveModSixTernaryCode_state (n : Nat) :
    positiveModSixTernaryCode (positiveModSixTernaryState n) =
      n % 3 := by
  by_cases h0 : n % 3 = 0
  · simp [positiveModSixTernaryState,
      positiveModSixTernaryCode, h0]
  · by_cases h1 : n % 3 = 1
    · simp [positiveModSixTernaryState,
        positiveModSixTernaryCode, h0, h1]
    · have h2 : n % 3 = 2 := by
        omega
      simp [positiveModSixTernaryState,
        positiveModSixTernaryCode, h0, h1, h2]

theorem modThree_eq_of_ternaryState_eq
    {m n : Nat}
    (equal :
      positiveModSixTernaryState m =
        positiveModSixTernaryState n) :
    m % 3 = n % 3 := by
  calc
    m % 3 =
        positiveModSixTernaryCode
          (positiveModSixTernaryState m) :=
      (positiveModSixTernaryCode_state m).symm
    _ = positiveModSixTernaryCode
          (positiveModSixTernaryState n) := by
      rw [equal]
    _ = n % 3 :=
      positiveModSixTernaryCode_state n

theorem modSix_eq_of_modTwo_modThree_eq
    {m n : Nat}
    (modTwo : m % 2 = n % 2)
    (modThree : m % 3 = n % 3) :
    m % 6 = n % 6 := by
  omega

def supportState
    (absent present : Fin 5) (n : Nat) : Fin 5 :=
  if n = 0 then absent else present

theorem supportState_zero_iff
    (absent present : Fin 5)
    (distinct : absent ≠ present)
    {m n : Nat}
    (equal :
      supportState absent present m =
        supportState absent present n) :
    m = 0 ↔ n = 0 := by
  constructor
  · intro hm
    subst m
    apply Decidable.byContradiction
    intro hn
    apply distinct
    simpa [supportState, hn] using equal
  · intro hn
    subst n
    apply Decidable.byContradiction
    intro hm
    apply distinct
    symm
    simpa [supportState, hm] using equal

theorem support_iff_of_state_eq
    (absent present : Fin 5)
    (distinct : absent ≠ present)
    (z : Nat) (xs ys : List Nat)
    (equal :
      supportState absent present (xs.count z) =
        supportState absent present (ys.count z)) :
    z ∈ xs ↔ z ∈ ys := by
  have zeroEq :
      xs.count z = 0 ↔ ys.count z = 0 :=
    supportState_zero_iff absent present distinct equal
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  constructor
  · intro leftPositive
    have leftNonzero : xs.count z ≠ 0 := by
      omega
    have rightNonzero : ys.count z ≠ 0 :=
      fun rightZero => leftNonzero (zeroEq.mpr rightZero)
    omega
  · intro rightPositive
    have rightNonzero : ys.count z ≠ 0 := by
      omega
    have leftNonzero : xs.count z ≠ 0 :=
      fun leftZero => rightNonzero (zeroEq.mp leftZero)
    omega

end SemigroupBasis.CoRoots.S5_1007

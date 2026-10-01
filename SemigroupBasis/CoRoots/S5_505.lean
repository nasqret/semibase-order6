import SemigroupBasis.Examples.CommutativePositiveModFourFive

namespace SemigroupBasis.CoRoots.S5_505

open SemigroupBasis
open SemigroupBasis.Examples

abbrev basis : List (Identity Nat) :=
  commutativePositiveModFourBasis

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

/-- The four C4 power states in zero-based catalogue notation:
`0, 2, 1, 3` for residues `0, 1, 2, 3`. -/
def positiveModFourResidueState (n : Nat) : Fin 5 :=
  if n % 4 = 0 then 0
  else if n % 4 = 1 then 2
  else if n % 4 = 2 then 1
  else 3

def positiveModFourResidueCode (value : Fin 5) : Nat :=
  if value = 0 then 0
  else if value = 2 then 1
  else if value = 1 then 2
  else 3

theorem positiveModFourResidueCode_state (n : Nat) :
    positiveModFourResidueCode
        (positiveModFourResidueState n) =
      n % 4 := by
  by_cases h0 : n % 4 = 0
  · simp [positiveModFourResidueState,
      positiveModFourResidueCode, h0]
  · by_cases h1 : n % 4 = 1
    · simp [positiveModFourResidueState,
        positiveModFourResidueCode, h0, h1]
    · by_cases h2 : n % 4 = 2
      · simp [positiveModFourResidueState,
          positiveModFourResidueCode, h0, h1, h2]
      · have h3 : n % 4 = 3 := by
          omega
        simp [positiveModFourResidueState,
          positiveModFourResidueCode, h0, h1, h2, h3]

theorem modFour_eq_of_residueState_eq
    {m n : Nat}
    (equal :
      positiveModFourResidueState m =
        positiveModFourResidueState n) :
    m % 4 = n % 4 := by
  calc
    m % 4 =
        positiveModFourResidueCode
          (positiveModFourResidueState m) :=
      (positiveModFourResidueCode_state m).symm
    _ = positiveModFourResidueCode
          (positiveModFourResidueState n) := by
      rw [equal]
    _ = n % 4 :=
      positiveModFourResidueCode_state n

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
    by_cases hn : n = 0
    · exact hn
    · subst m
      have contradiction : absent = present := by
        simpa [supportState, hn] using equal
      exact False.elim (distinct contradiction)
  · intro hn
    by_cases hm : m = 0
    · exact hm
    · subst n
      have contradiction : present = absent := by
        simpa [supportState, hm] using equal
      exact False.elim (distinct contradiction.symm)

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

end SemigroupBasis.CoRoots.S5_505

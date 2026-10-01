import SemigroupBasis.CoRoots.EdmundsItem34
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.CoRoots.S4_31

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.EdmundsItem34

private theorem mul_prefixCommutation (a b c : Fin 4) :
    Generated.Catalogue.S4_31.mul
        (Generated.Catalogue.S4_31.mul a b) c =
      Generated.Catalogue.S4_31.mul
        (Generated.Catalogue.S4_31.mul b a) c := by
  decide +revert

private theorem mul_squareCommutation (a b : Fin 4) :
    Generated.Catalogue.S4_31.mul
        (Generated.Catalogue.S4_31.mul
          (Generated.Catalogue.S4_31.mul a a) b) b =
      Generated.Catalogue.S4_31.mul
        (Generated.Catalogue.S4_31.mul
          (Generated.Catalogue.S4_31.mul b b) a) a := by
  decide +revert

private theorem mul_prefixParity (a b : Fin 4) :
    Generated.Catalogue.S4_31.mul
        (Generated.Catalogue.S4_31.mul
          (Generated.Catalogue.S4_31.mul a a) a) b =
      Generated.Catalogue.S4_31.mul a b := by
  decide +revert

private theorem mul_terminalSwitch (a b : Fin 4) :
    Generated.Catalogue.S4_31.mul
        (Generated.Catalogue.S4_31.mul
          (Generated.Catalogue.S4_31.mul a b) b) b =
      Generated.Catalogue.S4_31.mul
        (Generated.Catalogue.S4_31.mul
          (Generated.Catalogue.S4_31.mul b a) a) a := by
  decide +revert

private theorem mul_leftIdentity (b : Fin 4) :
    Generated.Catalogue.S4_31.mul 3 b = b := by
  decide +revert

theorem models :
    Models Generated.Catalogue.S4_31.table.semigroup
      edmundsFourTwentySevenBasis := by
  intro e he
  simp only [edmundsFourTwentySevenBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · intro valuation
    change
      Generated.Catalogue.S4_31.mul
          (Generated.Catalogue.S4_31.mul
            (valuation 0) (valuation 1))
          (valuation 2) =
        Generated.Catalogue.S4_31.mul
          (Generated.Catalogue.S4_31.mul
            (valuation 1) (valuation 0))
          (valuation 2)
    exact mul_prefixCommutation
      (valuation 0) (valuation 1) (valuation 2)
  · intro valuation
    change
      Generated.Catalogue.S4_31.mul
          (Generated.Catalogue.S4_31.mul
            (Generated.Catalogue.S4_31.mul
              (valuation 0) (valuation 0))
            (valuation 1))
          (valuation 1) =
        Generated.Catalogue.S4_31.mul
          (Generated.Catalogue.S4_31.mul
            (Generated.Catalogue.S4_31.mul
              (valuation 1) (valuation 1))
            (valuation 0))
          (valuation 0)
    exact mul_squareCommutation (valuation 0) (valuation 1)
  · intro valuation
    change
      Generated.Catalogue.S4_31.mul
          (Generated.Catalogue.S4_31.mul
            (Generated.Catalogue.S4_31.mul
              (valuation 0) (valuation 0))
            (valuation 0))
          (valuation 1) =
        Generated.Catalogue.S4_31.mul
          (valuation 0) (valuation 1)
    exact mul_prefixParity (valuation 0) (valuation 1)
  · intro valuation
    change
      Generated.Catalogue.S4_31.mul
          (Generated.Catalogue.S4_31.mul
            (Generated.Catalogue.S4_31.mul
              (valuation 0) (valuation 1))
            (valuation 1))
          (valuation 1) =
        Generated.Catalogue.S4_31.mul
          (Generated.Catalogue.S4_31.mul
            (Generated.Catalogue.S4_31.mul
              (valuation 1) (valuation 0))
            (valuation 0))
          (valuation 0)
    exact mul_terminalSwitch (valuation 0) (valuation 1)

private def supportState (n : Nat) : Fin 4 :=
  if n = 0 then 3 else 0

private def supportSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 0 else 3

private theorem mul_supportTarget (n : Nat) :
    Generated.Catalogue.S4_31.mul 0 (supportState n) =
      supportState (n + 1) := by
  cases n <;>
    simp [Generated.Catalogue.S4_31.mul, supportState]

private theorem mul_supportOther (n : Nat) :
    Generated.Catalogue.S4_31.mul 3 (supportState n) =
      supportState n := by
  exact mul_leftIdentity (supportState n)

private theorem eval_supportSeparator
    (z : Nat) (pref : List Nat) (final : Nat) :
    Generated.Catalogue.S4_31.table.semigroup.eval
        (supportSeparator z) (wordOfPrefixFinal pref final) =
      supportState ((pref ++ [final]).count z) := by
  induction pref with
  | nil =>
      by_cases hfinal : final = z
      · subst final
        simp [wordOfPrefixFinal, supportSeparator, supportState]
      · simp [wordOfPrefixFinal, supportSeparator, supportState, hfinal]
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons,
        Semigroup.eval_append, Semigroup.eval_singleton, ih]
      by_cases hx : x = z
      · subst x
        rw [show supportSeparator z z = (0 : Fin 4) by
          simp [supportSeparator]]
        change
          Generated.Catalogue.S4_31.mul 0
              (supportState ((xs ++ [final]).count z)) =
            supportState ((z :: xs ++ [final]).count z)
        rw [mul_supportTarget]
        congr 1
        simp
      · rw [show supportSeparator z x = (3 : Fin 4) by
          simp [supportSeparator, hx]]
        change
          Generated.Catalogue.S4_31.mul 3
              (supportState ((xs ++ [final]).count z)) =
            supportState ((x :: xs ++ [final]).count z)
        rw [mul_supportOther]
        congr 1
        simp [hx]

private def parityState (n : Nat) : Fin 4 :=
  if n = 0 then 3 else if n % 2 = 0 then 0 else 1

private def paritySeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 3

private theorem mul_parityTarget (n : Nat) :
    Generated.Catalogue.S4_31.mul 1 (parityState n) =
      parityState (n + 1) := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      by_cases hn : (n + 1) % 2 = 0
      · have next : (n + 2) % 2 = 1 := by omega
        simp [parityState, Generated.Catalogue.S4_31.mul, hn, next]
      · have current : (n + 1) % 2 = 1 := by omega
        have next : (n + 2) % 2 = 0 := by omega
        simp [parityState, Generated.Catalogue.S4_31.mul, current, next]

private theorem mul_parityOther (n : Nat) :
    Generated.Catalogue.S4_31.mul 3 (parityState n) =
      parityState n := by
  exact mul_leftIdentity (parityState n)

private theorem eval_paritySeparator
    (z : Nat) (pref : List Nat) (final : Nat) :
    Generated.Catalogue.S4_31.table.semigroup.eval
        (paritySeparator z) (wordOfPrefixFinal pref final) =
      parityState ((pref ++ [final]).count z) := by
  induction pref with
  | nil =>
      by_cases hfinal : final = z
      · subst final
        simp [wordOfPrefixFinal, paritySeparator, parityState]
      · simp [wordOfPrefixFinal, paritySeparator, parityState, hfinal]
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons,
        Semigroup.eval_append, Semigroup.eval_singleton, ih]
      by_cases hx : x = z
      · subst x
        rw [show paritySeparator z z = (1 : Fin 4) by
          simp [paritySeparator]]
        change
          Generated.Catalogue.S4_31.mul 1
              (parityState ((xs ++ [final]).count z)) =
            parityState ((z :: xs ++ [final]).count z)
        rw [mul_parityTarget]
        congr 1
        simp
      · rw [show paritySeparator z x = (3 : Fin 4) by
          simp [paritySeparator, hx]]
        change
          Generated.Catalogue.S4_31.mul 3
              (parityState ((xs ++ [final]).count z)) =
            parityState ((x :: xs ++ [final]).count z)
        rw [mul_parityOther]
        congr 1
        simp [hx]

private theorem parityState_eq_implies_mod
    {m n : Nat} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : parityState m = parityState n) :
    m % 2 = n % 2 := by
  by_cases hmEven : m % 2 = 0
  · by_cases hnEven : n % 2 = 0
    · exact hmEven.trans hnEven.symm
    · have hnOdd : n % 2 = 1 := by omega
      simp [parityState, hm, hn, hmEven, hnOdd] at h
  · have hmOdd : m % 2 = 1 := by omega
    by_cases hnEven : n % 2 = 0
    · simp [parityState, hm, hn, hmOdd, hnEven] at h
    · have hnOdd : n % 2 = 1 := by omega
      exact hmOdd.trans hnOdd.symm

private def finalSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 3

private theorem mul_finalTarget_ne (b : Fin 4) :
    Generated.Catalogue.S4_31.mul 2 b ≠ 2 := by
  decide +revert

private theorem eval_finalSeparator_eq_two_iff
    (z : Nat) (pref : List Nat) (final : Nat) :
    Generated.Catalogue.S4_31.table.semigroup.eval
        (finalSeparator z) (wordOfPrefixFinal pref final) =
        (2 : Fin 4) ↔
      final = z ∧ z ∉ pref := by
  induction pref with
  | nil =>
      by_cases hfinal : final = z
      · subst final
        simp [wordOfPrefixFinal, finalSeparator]
      · simp [wordOfPrefixFinal, finalSeparator, hfinal]
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons,
        Semigroup.eval_append, Semigroup.eval_singleton]
      by_cases hx : x = z
      · subst x
        rw [show finalSeparator z z = (2 : Fin 4) by
          simp [finalSeparator]]
        change
          Generated.Catalogue.S4_31.mul 2
              (Generated.Catalogue.S4_31.table.semigroup.eval
                (finalSeparator z) (wordOfPrefixFinal xs final)) =
            2 ↔ _
        have hne :=
          mul_finalTarget_ne
            (Generated.Catalogue.S4_31.table.semigroup.eval
              (finalSeparator z) (wordOfPrefixFinal xs final))
        simp [finalSeparator, hne]
      · rw [show finalSeparator z x = (3 : Fin 4) by
          simp [finalSeparator, hx]]
        change
          Generated.Catalogue.S4_31.mul 3
              (Generated.Catalogue.S4_31.table.semigroup.eval
                (finalSeparator z) (wordOfPrefixFinal xs final)) =
            2 ↔ _
        rw [mul_leftIdentity]
        simpa [hx, Ne.symm hx] using ih

theorem separatesNormalForms
    (prefix₁ : List Nat) (final₁ : Nat)
    (prefix₂ : List Nat) (final₂ : Nat)
    (equal :
      ∀ valuation : Nat → Fin 4,
        Generated.Catalogue.S4_31.table.semigroup.eval valuation
            (wordOfPrefixFinal prefix₁ final₁) =
          Generated.Catalogue.S4_31.table.semigroup.eval valuation
            (wordOfPrefixFinal prefix₂ final₂)) :
    NormalInvariants prefix₁ final₁ prefix₂ final₂ := by
  have support :
      ∀ z, z ∈ prefix₁ ++ [final₁] ↔ z ∈ prefix₂ ++ [final₂] := by
    intro z
    have evaluated := equal (supportSeparator z)
    rw [eval_supportSeparator, eval_supportSeparator] at evaluated
    have zeroEq :
        (prefix₁ ++ [final₁]).count z = 0 ↔
          (prefix₂ ++ [final₂]).count z = 0 := by
      constructor
      · intro hl
        by_cases hr : (prefix₂ ++ [final₂]).count z = 0
        · exact hr
        · have impossible : False := by
            have h := evaluated
            simp only [supportState, hl, hr, if_pos, if_neg] at h
            simp at h
          exact impossible.elim
      · intro hr
        by_cases hl : (prefix₁ ++ [final₁]).count z = 0
        · exact hl
        · have impossible : False := by
            have h := evaluated
            simp only [supportState, hl, hr, if_pos, if_neg] at h
            simp at h
          exact impossible.elim
    rw [← List.count_pos_iff, ← List.count_pos_iff]
    omega
  have parity :
      ∀ z, (prefix₁ ++ [final₁]).count z % 2 =
        (prefix₂ ++ [final₂]).count z % 2 := by
    intro z
    by_cases hl : (prefix₁ ++ [final₁]).count z = 0
    · have hr : (prefix₂ ++ [final₂]).count z = 0 := by
        rw [List.count_eq_zero] at hl ⊢
        intro h
        exact hl ((support z).mpr h)
      simp [hl, hr]
    · have hr : (prefix₂ ++ [final₂]).count z ≠ 0 := by
        intro hr
        have lhsMem : z ∈ prefix₁ ++ [final₁] :=
          List.count_pos_iff.mp (Nat.pos_of_ne_zero hl)
        have rhsMem := (support z).mp lhsMem
        exact (List.count_eq_zero.mp hr) rhsMem
      have evaluated := equal (paritySeparator z)
      rw [eval_paritySeparator, eval_paritySeparator] at evaluated
      exact parityState_eq_implies_mod hl hr evaluated
  have simpleFinal :
      ∀ z, (final₁ = z ∧ z ∉ prefix₁) ↔
        (final₂ = z ∧ z ∉ prefix₂) := by
    intro z
    have evaluated := equal (finalSeparator z)
    constructor
    · intro h
      apply (eval_finalSeparator_eq_two_iff z prefix₂ final₂).1
      exact evaluated.symm.trans <|
        (eval_finalSeparator_eq_two_iff z prefix₁ final₁).2 h
    · intro h
      apply (eval_finalSeparator_eq_two_iff z prefix₁ final₁).1
      exact evaluated.trans <|
        (eval_finalSeparator_eq_two_iff z prefix₂ final₂).2 h
  exact ⟨support, parity, simpleFinal⟩

/-- Unrestricted completeness of Edmunds' item-34 basis for `S4_31`. -/
theorem basis :
    BasisFor Generated.Catalogue.S4_31.table.semigroup
      edmundsFourTwentySevenBasis :=
  basisForOfSeparatesNormalForms
    Generated.Catalogue.S4_31.table.semigroup
    models separatesNormalForms

end SemigroupBasis.CoRoots.S4_31

import SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleTables

set_option maxRecDepth 100000

/-!
Semantic invariants separated by the monoids `L21` and `T2`.

For a word list `w`:
* `firstOfPair x y w` : the first letter of `w` equal to `x` or `y`;
* `iniRec w`          : the letters of `w` in order of first occurrence;
* `fin w`             : the letters of `w` in order of last occurrence;
* `w.count y % 2`     : the count parity of `y`;
* `suffixAfterLast z w` : the suffix after the last occurrence of `z`.

Validity on `L21` pins `firstOfPair` (hence `iniRec`); validity on `T2` pins
count parities, support, `fin`, and the count parities of every
`suffixAfterLast`.
-/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleInvariants

open SemigroupBasis
open Msg0607TripleTables

/-! ## First occurrences -/

def firstOfPair (x y : Nat) : List Nat → Option Nat
  | [] => none
  | c :: w => if c = x ∨ c = y then some c else firstOfPair x y w

theorem firstOfPair_cons_of_ne {x y c : Nat} (w : List Nat) (hx : c ≠ x) (hy : c ≠ y) :
    firstOfPair x y (c :: w) = firstOfPair x y w := by
  simp [firstOfPair, hx, hy]

theorem firstOfPair_cons_left (x y : Nat) (w : List Nat) : firstOfPair x y (x :: w) = some x := by
  simp [firstOfPair]

theorem firstOfPair_cons_right (x y : Nat) (w : List Nat) : firstOfPair x y (y :: w) = some y := by
  simp [firstOfPair]

theorem firstOfPair_spec (x y : Nat) :
    ∀ (w : List Nat) (r : Nat), firstOfPair x y w = some r → (r = x ∨ r = y) ∧ r ∈ w
  | [], r, h => by simp [firstOfPair] at h
  | c :: w, r, h => by
      by_cases hc : c = x ∨ c = y
      · simp only [firstOfPair, if_pos hc, Option.some.injEq] at h
        subst h
        exact ⟨hc, by simp⟩
      · simp only [firstOfPair, if_neg hc] at h
        obtain ⟨hr, mem⟩ := firstOfPair_spec x y w r h
        exact ⟨hr, List.mem_cons_of_mem _ mem⟩

theorem firstOfPair_eq_none (x y : Nat) :
    ∀ w : List Nat, firstOfPair x y w = none ↔ x ∉ w ∧ y ∉ w
  | [] => by simp [firstOfPair]
  | c :: w => by
      by_cases hc : c = x ∨ c = y
      · simp only [firstOfPair, if_pos hc]
        constructor
        · intro h
          exact absurd h (by simp)
        · rintro ⟨hx, hy⟩
          rcases hc with rfl | rfl
          · exact absurd (List.mem_cons_self) hx
          · exact absurd (List.mem_cons_self) hy
      · simp only [firstOfPair, if_neg hc, firstOfPair_eq_none x y w]
        have hx : c ≠ x := fun h => hc (Or.inl h)
        have hy : c ≠ y := fun h => hc (Or.inr h)
        simp [List.mem_cons, hx.symm, hy.symm]

theorem firstOfPair_filter_ne {x y a : Nat} (hx : x ≠ a) (hy : y ≠ a) :
    ∀ w : List Nat, firstOfPair x y (w.filter fun c => decide (c ≠ a)) = firstOfPair x y w
  | [] => rfl
  | c :: w => by
      by_cases hc : c = a
      · subst hc
        rw [List.filter_cons_of_neg (by simp), firstOfPair_cons_of_ne w (Ne.symm hx) (Ne.symm hy)]
        exact firstOfPair_filter_ne hx hy w
      · rw [List.filter_cons_of_pos (by simp [hc])]
        simp only [firstOfPair]
        rw [firstOfPair_filter_ne hx hy w]

theorem firstOfPair_absent_left {x y : Nat} :
    ∀ w : List Nat, x ∉ w → firstOfPair x y w = firstOfPair y y w
  | [], _ => rfl
  | c :: w, absent => by
      have hc : c ≠ x := fun h => absent (by simp [h])
      have rest : x ∉ w := fun h => absent (List.mem_cons_of_mem _ h)
      simp only [firstOfPair, hc, false_or, or_self]
      by_cases hy : c = y
      · simp [hy]
      · simp only [hy, if_false]
        exact firstOfPair_absent_left w rest

theorem firstOfPair_absent_right {x y : Nat} (w : List Nat) (absent : y ∉ w) :
    firstOfPair x y w = firstOfPair x x w := by
  have swap : ∀ w : List Nat, firstOfPair x y w = firstOfPair y x w := by
    intro w
    induction w with
    | nil => rfl
    | cons c w ih =>
        simp only [firstOfPair, ih]
        by_cases h : c = x ∨ c = y
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  rw [swap, firstOfPair_absent_left w absent]

/-- Letters in order of first occurrence, with a fuel parameter. -/
def iniFuel : Nat → List Nat → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, x :: w => x :: iniFuel n (w.filter fun c => decide (c ≠ x))

theorem iniFuel_eq_of_le :
    ∀ (n m : Nat) (w : List Nat), w.length ≤ n → w.length ≤ m → iniFuel n w = iniFuel m w
  | 0, m, w, hn, _ => by
      have empty : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
      subst empty
      cases m <;> rfl
  | n + 1, m, [], _, _ => by cases m <;> rfl
  | n + 1, m, x :: w, hn, hm => by
      cases m with
      | zero => simp at hm
      | succ m =>
          simp only [iniFuel]
          have le := List.length_filter_le (fun c => decide (c ≠ x)) w
          simp only [List.length_cons] at hn hm
          rw [iniFuel_eq_of_le n m _ (by omega) (by omega)]

/-- Letters in order of first occurrence. -/
def iniRec (w : List Nat) : List Nat := iniFuel w.length w

theorem iniRec_cons (x : Nat) (w : List Nat) :
    iniRec (x :: w) = x :: iniRec (w.filter fun c => decide (c ≠ x)) := by
  unfold iniRec
  simp only [List.length_cons, iniFuel]
  rw [iniFuel_eq_of_le w.length _ _ (List.length_filter_le _ _) (Nat.le_refl _)]

theorem mem_filter_ne_self (a : Nat) (w : List Nat) : a ∉ w.filter fun c => decide (c ≠ a) := by
  intro mem
  simp [List.mem_filter] at mem

/-- Equal first-of-pair data forces equal first-occurrence orders. -/
theorem iniRec_eq_of_firstOfPair :
    ∀ (n : Nat) (u v : List Nat), u.length ≤ n →
      (∀ x y, firstOfPair x y u = firstOfPair x y v) → iniRec u = iniRec v := by
  intro n
  induction n with
  | zero =>
      intro u v length same
      have empty : u = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp length)
      subst empty
      cases v with
      | nil => rfl
      | cons b v' =>
          have := same b b
          rw [firstOfPair_cons_left] at this
          simp [firstOfPair] at this
  | succ n ih =>
      intro u v length same
      cases u with
      | nil =>
          cases v with
          | nil => rfl
          | cons b v' =>
              have := same b b
              rw [firstOfPair_cons_left] at this
              simp [firstOfPair] at this
      | cons a u' =>
          cases v with
          | nil =>
              have := same a a
              rw [firstOfPair_cons_left] at this
              simp [firstOfPair] at this
          | cons b v' =>
              have heads : a = b := by
                have := same a b
                rw [firstOfPair_cons_left, firstOfPair_cons_right] at this
                exact Option.some.inj this
              subst heads
              rw [iniRec_cons, iniRec_cons]
              congr 1
              have shorter : (u'.filter fun c => decide (c ≠ a)).length ≤ n := by
                have := List.length_filter_le (fun c => decide (c ≠ a)) u'
                simp only [List.length_cons] at length
                omega
              apply ih _ _ shorter
              intro x y
              by_cases hx : x = a
              · by_cases hy : y = a
                · rw [hx, hy]
                  rw [(firstOfPair_eq_none a a _).mpr ⟨mem_filter_ne_self a u', mem_filter_ne_self a u'⟩,
                    (firstOfPair_eq_none a a _).mpr ⟨mem_filter_ne_self a v', mem_filter_ne_self a v'⟩]
                · rw [hx]
                  rw [firstOfPair_absent_left _ (mem_filter_ne_self a u'),
                    firstOfPair_absent_left _ (mem_filter_ne_self a v'),
                    firstOfPair_filter_ne hy hy, firstOfPair_filter_ne hy hy]
                  have := same y y
                  rwa [firstOfPair_cons_of_ne u' (Ne.symm hy) (Ne.symm hy),
                    firstOfPair_cons_of_ne v' (Ne.symm hy) (Ne.symm hy)] at this
              · by_cases hy : y = a
                · rw [hy]
                  rw [firstOfPair_absent_right _ (mem_filter_ne_self a u'),
                    firstOfPair_absent_right _ (mem_filter_ne_self a v'),
                    firstOfPair_filter_ne hx hx, firstOfPair_filter_ne hx hx]
                  have := same x x
                  rwa [firstOfPair_cons_of_ne u' (Ne.symm hx) (Ne.symm hx),
                    firstOfPair_cons_of_ne v' (Ne.symm hx) (Ne.symm hx)] at this
                · rw [firstOfPair_filter_ne hx hy, firstOfPair_filter_ne hx hy]
                  have := same x y
                  rwa [firstOfPair_cons_of_ne u' (Ne.symm hx) (Ne.symm hy),
                    firstOfPair_cons_of_ne v' (Ne.symm hx) (Ne.symm hy)] at this

/-! ## Last occurrences -/

def lastOfPair (x y : Nat) (w : List Nat) : Option Nat := firstOfPair x y w.reverse

/-- Letters in order of last occurrence. -/
def fin (w : List Nat) : List Nat := (iniRec w.reverse).reverse

theorem fin_eq_of_lastOfPair {u v : List Nat}
    (same : ∀ x y, lastOfPair x y u = lastOfPair x y v) : fin u = fin v := by
  unfold fin
  rw [iniRec_eq_of_firstOfPair u.reverse.length u.reverse v.reverse (Nat.le_refl _) same]

theorem lastOfPair_append_singleton (x y c : Nat) (w : List Nat) :
    lastOfPair x y (w ++ [c]) = if c = x ∨ c = y then some c else lastOfPair x y w := by
  simp [lastOfPair, firstOfPair]

/-- The suffix after the last occurrence of `z` (empty when `z` is absent). -/
def suffixAfterLast (z : Nat) : List Nat → List Nat
  | [] => []
  | c :: w => if z ∈ w then suffixAfterLast z w else if c = z then w else suffixAfterLast z w

theorem suffixAfterLast_of_not_mem (z : Nat) :
    ∀ w : List Nat, z ∉ w → suffixAfterLast z w = []
  | [], _ => rfl
  | c :: w, absent => by
      have hc : c ≠ z := fun h => absent (by simp [h])
      have rest : z ∉ w := fun h => absent (List.mem_cons_of_mem _ h)
      simp [suffixAfterLast, rest, hc, suffixAfterLast_of_not_mem z w rest]

theorem suffixAfterLast_append_cons (z : Nat) :
    ∀ (A R : List Nat), z ∉ R → suffixAfterLast z (A ++ z :: R) = R
  | [], R, absent => by simp [suffixAfterLast, absent]
  | a :: A, R, absent => by
      have mem : z ∈ A ++ z :: R := by simp
      simp only [List.cons_append, suffixAfterLast, if_pos mem]
      exact suffixAfterLast_append_cons z A R absent

theorem suffixAfterLast_append_singleton (z c : Nat) (w : List Nat) :
    suffixAfterLast z (w ++ [c]) =
      if c = z then [] else if z ∈ w then suffixAfterLast z w ++ [c] else [] := by
  by_cases hc : c = z
  · subst hc
    rw [if_pos rfl]
    exact suffixAfterLast_append_cons c w [] (by simp)
  · rw [if_neg hc]
    by_cases mem : z ∈ w
    · rw [if_pos mem]
      obtain ⟨A, R, hw⟩ := List.mem_iff_append.mp mem
      -- take the last occurrence
      have : ∃ A R, w = A ++ z :: R ∧ z ∉ R := by
        clear hw A R
        induction w with
        | nil => simp at mem
        | cons d w ih =>
            by_cases inRest : z ∈ w
            · obtain ⟨A, R, hw, absent⟩ := ih inRest
              exact ⟨d :: A, R, by simp [hw], absent⟩
            · have hd : d = z := by
                simp only [List.mem_cons] at mem
                rcases mem with h | h
                · exact h.symm
                · exact absurd h inRest
              exact ⟨[], w, by simp [hd], inRest⟩
      obtain ⟨A, R, rfl, absent⟩ := this
      rw [suffixAfterLast_append_cons z A R absent, List.append_assoc, List.cons_append,
        suffixAfterLast_append_cons z A (R ++ [c])]
      simp [absent, Ne.symm hc]
    · rw [if_neg mem]
      apply suffixAfterLast_of_not_mem
      simp [mem, Ne.symm hc]

/-! ## Evaluation on `L21` -/

/-- `x ↦ 1`, `y ↦ 2`, everything else `↦ 0` (the identity). -/
def leftValuation (x y : Nat) (c : Nat) : Fin 3 :=
  if c = x then 1 else if c = y then 2 else 0

def leftValue (x y : Nat) (w : List Nat) : Fin 3 :=
  match firstOfPair x y w with
  | none => 0
  | some c => leftValuation x y c

theorem L21_mul_eq (a b : Fin 3) : L21.table.semigroup.mul a b = if a = 0 then b else a := by
  revert a b
  decide

theorem leftValuation_ne_zero_iff (x y c : Nat) : leftValuation x y c ≠ 0 ↔ (c = x ∨ c = y) := by
  unfold leftValuation
  by_cases hx : c = x
  · rw [if_pos hx]
    simp [hx]
  · by_cases hy : c = y
    · rw [if_neg hx, if_pos hy]
      simp [hy]
    · rw [if_neg hx, if_neg hy]
      simp [hx, hy]

private theorem leftFold (x y : Nat) :
    ∀ (w : List Nat) (init : Fin 3),
      w.foldl (fun acc c => L21.table.semigroup.mul acc (leftValuation x y c)) init =
        if init = 0 then leftValue x y w else init
  | [], init => by
      by_cases h : init = 0
      · simp [h, leftValue, firstOfPair]
      · simp [h]
  | c :: w, init => by
      rw [List.foldl_cons, leftFold x y w, L21_mul_eq]
      by_cases hinit : init = 0
      · rw [if_pos hinit, if_pos hinit]
        by_cases hc : c = x ∨ c = y
        · have ne := (leftValuation_ne_zero_iff x y c).mpr hc
          rw [if_neg ne]
          simp [leftValue, firstOfPair, hc]
        · have eq : leftValuation x y c = 0 := by
            apply Classical.byContradiction
            intro ne
            exact hc ((leftValuation_ne_zero_iff x y c).mp ne)
          rw [if_pos eq]
          simp [leftValue, firstOfPair, hc]
      · simp [hinit]

theorem eval_L21 (x y : Nat) (word : Word Nat) :
    L21.table.semigroup.eval (leftValuation x y) word = leftValue x y word.toList := by
  cases word with
  | mk head tail =>
      show tail.foldl (fun acc c => L21.table.semigroup.mul acc (leftValuation x y c))
        (leftValuation x y head) = leftValue x y (head :: tail)
      rw [leftFold]
      by_cases hhead : leftValuation x y head = 0
      · have hc : ¬ (head = x ∨ head = y) := fun h => (leftValuation_ne_zero_iff x y head).mpr h hhead
        simp [hhead, leftValue, firstOfPair, hc]
      · have hc : head = x ∨ head = y := (leftValuation_ne_zero_iff x y head).mp hhead
        simp [hhead, leftValue, firstOfPair, hc]

theorem firstOfPair_eq_of_leftValue {x y : Nat} {u v : List Nat}
    (same : leftValue x y u = leftValue x y v) : firstOfPair x y u = firstOfPair x y v := by
  unfold leftValue at same
  cases hu : firstOfPair x y u with
  | none =>
      cases hv : firstOfPair x y v with
      | none => rfl
      | some d =>
          rw [hu, hv] at same
          have hd := (firstOfPair_spec x y v d hv).1
          have ne := (leftValuation_ne_zero_iff x y d).mpr hd
          exact absurd same.symm ne
  | some c =>
      cases hv : firstOfPair x y v with
      | none =>
          rw [hu, hv] at same
          have hc := (firstOfPair_spec x y u c hu).1
          have ne := (leftValuation_ne_zero_iff x y c).mpr hc
          exact absurd same ne
      | some d =>
          rw [hu, hv] at same
          have hc := (firstOfPair_spec x y u c hu).1
          have hd := (firstOfPair_spec x y v d hv).1
          congr
          unfold leftValuation at same
          rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
          · rfl
          · by_cases h : d = c
            · exact h.symm
            · simp [h] at same
          · by_cases h : c = d
            · exact h
            · simp [h] at same
          · rfl

/-- Validity on `L21` pins the first-occurrence order. -/
theorem iniRec_eq_of_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy L21.table.semigroup) :
    iniRec identity.lhs.toList = iniRec identity.rhs.toList := by
  apply iniRec_eq_of_firstOfPair _ _ _ (Nat.le_refl _)
  intro x y
  apply firstOfPair_eq_of_leftValue
  have := valid (leftValuation x y)
  rwa [eval_L21, eval_L21] at this

/-! ## Evaluation on `T2` -/

theorem T2_mul_zero (a : Fin 4) : T2.table.semigroup.mul a (0 : Fin 4) = a := by
  revert a
  decide

theorem T2_mul_two (a : Fin 4) : T2.table.semigroup.mul a (2 : Fin 4) = (2 : Fin 4) := by
  revert a
  decide

theorem T2_mul_three (a : Fin 4) : T2.table.semigroup.mul a (3 : Fin 4) = (3 : Fin 4) := by
  revert a
  decide

theorem T2_toggle : T2.table.semigroup.mul (0 : Fin 4) (1 : Fin 4) = (1 : Fin 4) ∧
    T2.table.semigroup.mul (1 : Fin 4) (1 : Fin 4) = (0 : Fin 4) ∧
    T2.table.semigroup.mul (2 : Fin 4) (1 : Fin 4) = (3 : Fin 4) ∧
    T2.table.semigroup.mul (3 : Fin 4) (1 : Fin 4) = (2 : Fin 4) := by
  decide

/-- Generic left-fold evaluation through a semantic function respecting one step. -/
theorem eval_of_step (f : List Nat → Fin 4) (v : Nat → Fin 4)
    (init : ∀ c, f [c] = v c)
    (step : ∀ p c, f (p ++ [c]) = T2.table.semigroup.mul (f p) (v c)) (word : Word Nat) :
    T2.table.semigroup.eval v word = f word.toList := by
  cases word with
  | mk head tail =>
      show tail.foldl (fun acc c => T2.table.semigroup.mul acc (v c)) (v head) = f (head :: tail)
      have general : ∀ (t p : List Nat),
          t.foldl (fun acc c => T2.table.semigroup.mul acc (v c)) (f p) = f (p ++ t) := by
        intro t
        induction t with
        | nil => intro p; simp
        | cons c t ih =>
            intro p
            rw [List.foldl_cons, ← step p c, ih (p ++ [c])]
            simp
      have := general tail [head]
      rw [init head] at this
      simpa using this

/-- Count parity: `y ↦ g`, everything else `↦ 1`. -/
def parityValuation (y : Nat) (c : Nat) : Fin 4 := if c = y then 1 else 0

def parityValue (y : Nat) (w : List Nat) : Fin 4 := if w.count y % 2 = 0 then 0 else 1

theorem eval_parity (y : Nat) (word : Word Nat) :
    T2.table.semigroup.eval (parityValuation y) word = parityValue y word.toList := by
  apply eval_of_step
  · intro c
    by_cases hc : c = y
    · subst hc; simp [parityValue, parityValuation]
    · simp [parityValue, parityValuation, hc]
  · intro p c
    by_cases hc : c = y
    · have countEq : (p ++ [c]).count y = p.count y + 1 := by simp [List.count_append, hc]
      have valEq : parityValuation y c = 1 := by simp [parityValuation, hc]
      rw [valEq]
      simp only [parityValue, countEq]
      obtain ⟨h0, h1, _, _⟩ := T2_toggle
      by_cases even : p.count y % 2 = 0
      · rw [if_pos even, if_neg (by omega), h0]
      · rw [if_neg even, if_pos (by omega), h1]
    · simp [parityValuation, hc, parityValue, List.count_append, T2_mul_zero]

/-- Last of a pair: `x ↦ c₁`, `y ↦ c₂`, everything else `↦ 1`. -/
def lastValuation (x y : Nat) (c : Nat) : Fin 4 := if c = x then 2 else if c = y then 3 else 0

def lastValue (x y : Nat) (w : List Nat) : Fin 4 :=
  match lastOfPair x y w with
  | none => 0
  | some c => lastValuation x y c

theorem eval_last (x y : Nat) (word : Word Nat) :
    T2.table.semigroup.eval (lastValuation x y) word = lastValue x y word.toList := by
  apply eval_of_step
  · intro c
    by_cases hc : c = x ∨ c = y
    · simp [lastValue, lastOfPair, firstOfPair, hc]
    · have hx : c ≠ x := fun h => hc (Or.inl h)
      have hy : c ≠ y := fun h => hc (Or.inr h)
      simp [lastValue, lastOfPair, firstOfPair, lastValuation, hx, hy]
  · intro p c
    rw [lastValue, lastOfPair_append_singleton]
    by_cases hc : c = x ∨ c = y
    · rw [if_pos hc]
      rcases hc with rfl | rfl
      · simp [lastValuation, T2_mul_two]
      · by_cases hx : c = x
        · simp [lastValuation, hx, T2_mul_two]
        · simp [lastValuation, hx, T2_mul_three]
    · have hx : c ≠ x := fun h => hc (Or.inl h)
      have hy : c ≠ y := fun h => hc (Or.inr h)
      rw [if_neg hc]
      simp [lastValuation, hx, hy, T2_mul_zero, lastValue]

theorem lastOfPair_eq_of_lastValue {x y : Nat} {u v : List Nat}
    (same : lastValue x y u = lastValue x y v) : lastOfPair x y u = lastOfPair x y v := by
  unfold lastValue at same
  have spec : ∀ w r, lastOfPair x y w = some r → r = x ∨ r = y := fun w r h =>
    (firstOfPair_spec x y w.reverse r h).1
  have nonzero : ∀ r, r = x ∨ r = y → lastValuation x y r ≠ 0 := by
    intro r hr
    unfold lastValuation
    rcases hr with rfl | rfl
    · simp
    · by_cases h : r = x <;> simp [h]
  cases hu : lastOfPair x y u with
  | none =>
      cases hv : lastOfPair x y v with
      | none => rfl
      | some d =>
          rw [hu, hv] at same
          exact absurd same.symm (nonzero d (spec v d hv))
  | some c =>
      cases hv : lastOfPair x y v with
      | none =>
          rw [hu, hv] at same
          exact absurd same (nonzero c (spec u c hu))
      | some d =>
          rw [hu, hv] at same
          have hc := spec u c hu
          have hd := spec v d hv
          congr
          unfold lastValuation at same
          rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
          · rfl
          · by_cases h : d = c
            · exact h.symm
            · simp [h] at same
          · by_cases h : c = d
            · exact h
            · simp [h] at same
          · rfl

/-- Suffix parity after the last `z`: `z ↦ c₁`, `y ↦ g`, everything else `↦ 1`. -/
def suffixValuation (z y : Nat) (c : Nat) : Fin 4 := if c = z then 2 else if c = y then 1 else 0

def suffixValue (z y : Nat) (w : List Nat) : Fin 4 :=
  if z ∈ w then (if (suffixAfterLast z w).count y % 2 = 0 then 2 else 3)
  else (if w.count y % 2 = 0 then 0 else 1)

theorem eval_suffix (z y : Nat) (different : z ≠ y) (word : Word Nat) :
    T2.table.semigroup.eval (suffixValuation z y) word = suffixValue z y word.toList := by
  apply eval_of_step
  · intro c
    by_cases hz : c = z
    · subst hz
      simp [suffixValue, suffixValuation, suffixAfterLast]
    · by_cases hy : c = y
      · subst hy
        simp [suffixValue, suffixValuation, hz, Ne.symm hz]
      · simp [suffixValue, suffixValuation, hz, hy, Ne.symm hz]
  · intro p c
    obtain ⟨h01, h11, h21, h31⟩ := T2_toggle
    by_cases hz : c = z
    · subst hz
      simp only [suffixValuation, if_true, T2_mul_two, suffixValue]
      rw [suffixAfterLast_append_singleton, if_pos rfl]
      simp
    · by_cases hy : c = y
      · subst hy
        simp only [suffixValuation, hz, if_false, if_true, suffixValue,
          suffixAfterLast_append_singleton, List.count_append, List.count_singleton]
        by_cases memz : z ∈ p
        · have mem' : z ∈ p ++ [c] := List.mem_append_left _ memz
          simp only [memz, mem', if_true]
          rw [List.count_append, List.count_singleton]
          by_cases even : (suffixAfterLast z p).count c % 2 = 0
          · rw [if_pos even, if_neg (by simp; omega), h21]
          · rw [if_neg even, if_pos (by simp; omega), h31]
        · have mem' : z ∉ p ++ [c] := by simp [memz, Ne.symm hz]
          simp only [memz, mem', if_false]
          by_cases even : p.count c % 2 = 0
          · rw [if_pos even, if_neg (by simp; omega), h01]
          · rw [if_neg even, if_pos (by simp; omega), h11]
      · simp only [suffixValuation, hz, hy, if_false, T2_mul_zero, suffixValue,
          suffixAfterLast_append_singleton, List.count_append, List.count_singleton]
        by_cases memz : z ∈ p
        · have mem' : z ∈ p ++ [c] := List.mem_append_left _ memz
          simp [memz, mem', hy]
        · have mem' : z ∉ p ++ [c] := by simp [memz, Ne.symm hz]
          simp [memz, mem', hy]

/-! ## The invariant package -/

structure SameInvariants (u v : List Nat) : Prop where
  ini : iniRec u = iniRec v
  fin : fin u = fin v
  support : ∀ x, x ∈ u ↔ x ∈ v
  parity : ∀ y, u.count y % 2 = v.count y % 2
  suffix : ∀ z y, z ∈ u → (suffixAfterLast z u).count y % 2 = (suffixAfterLast z v).count y % 2

theorem parity_eq_of_parityValue {y : Nat} {u v : List Nat}
    (same : parityValue y u = parityValue y v) : u.count y % 2 = v.count y % 2 := by
  unfold parityValue at same
  by_cases hu : u.count y % 2 = 0 <;> by_cases hv : v.count y % 2 = 0
  · omega
  · simp [hu, hv] at same
  · simp [hu, hv] at same
  · omega

theorem support_eq_of_suffixValue {z y : Nat} {u v : List Nat}
    (same : suffixValue z y u = suffixValue z y v) : z ∈ u ↔ z ∈ v := by
  unfold suffixValue at same
  by_cases hu : z ∈ u <;> by_cases hv : z ∈ v
  · exact ⟨fun _ => hv, fun _ => hu⟩
  · exfalso
    simp only [hu, hv, if_true, if_false] at same
    split at same <;> split at same <;> simp at same
  · exfalso
    simp only [hu, hv, if_true, if_false] at same
    split at same <;> split at same <;> simp at same
  · exact ⟨fun h => absurd h hu, fun h => absurd h hv⟩

theorem suffix_eq_of_suffixValue {z y : Nat} {u v : List Nat} (memu : z ∈ u) (memv : z ∈ v)
    (same : suffixValue z y u = suffixValue z y v) :
    (suffixAfterLast z u).count y % 2 = (suffixAfterLast z v).count y % 2 := by
  unfold suffixValue at same
  simp only [memu, memv, if_true] at same
  by_cases hu : (suffixAfterLast z u).count y % 2 = 0 <;>
    by_cases hv : (suffixAfterLast z v).count y % 2 = 0
  · omega
  · simp [hu, hv] at same
  · simp [hu, hv] at same
  · omega

/-- A letter not occurring in either word. -/
theorem exists_fresh (u v : List Nat) : ∃ z, z ∉ u ∧ z ∉ v := by
  have bound : ∀ (l : List Nat) (c : Nat), c ∈ l → c ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => intro c h; simp at h
    | cons a l ih =>
        intro c h
        simp only [List.mem_cons] at h
        simp only [List.foldr_cons]
        rcases h with rfl | h
        · exact Nat.le_max_left _ _
        · exact Nat.le_trans (ih c h) (Nat.le_max_right _ _)
  refine ⟨(u ++ v).foldr max 0 + 1, ?_, ?_⟩
  · intro h
    have := bound (u ++ v) _ (List.mem_append_left _ h)
    omega
  · intro h
    have := bound (u ++ v) _ (List.mem_append_right _ h)
    omega

/-- Validity on both separating monoids yields the full invariant package. -/
theorem sameInvariants_of_valid (identity : Identity Nat)
    (validLeft : identity.SatisfiedBy L21.table.semigroup)
    (validT2 : identity.SatisfiedBy T2.table.semigroup) :
    SameInvariants identity.lhs.toList identity.rhs.toList := by
  have parity : ∀ y, identity.lhs.toList.count y % 2 = identity.rhs.toList.count y % 2 := by
    intro y
    apply parity_eq_of_parityValue
    have := validT2 (parityValuation y)
    rwa [eval_parity, eval_parity] at this
  have suffixValues : ∀ z y, z ≠ y →
      suffixValue z y identity.lhs.toList = suffixValue z y identity.rhs.toList := by
    intro z y different
    have := validT2 (suffixValuation z y)
    rwa [eval_suffix z y different, eval_suffix z y different] at this
  have support : ∀ x, x ∈ identity.lhs.toList ↔ x ∈ identity.rhs.toList := by
    intro x
    obtain ⟨y, _, _⟩ := exists_fresh [x] []
    have different : x ≠ y := fun h => by simp [h] at *
    exact support_eq_of_suffixValue (suffixValues x y different)
  refine
    { ini := iniRec_eq_of_valid identity validLeft
      fin := ?_
      support := support
      parity := parity
      suffix := ?_ }
  · apply fin_eq_of_lastOfPair
    intro x y
    apply lastOfPair_eq_of_lastValue
    have := validT2 (lastValuation x y)
    rwa [eval_last, eval_last] at this
  · intro z y memu
    have memv : z ∈ identity.rhs.toList := (support z).mp memu
    by_cases different : z = y
    · subst different
      -- the suffix after the last `z` contains no `z`
      have zeroU : (suffixAfterLast z identity.lhs.toList).count z = 0 := by
        apply List.count_eq_zero.mpr
        obtain ⟨A, R, hw, absent⟩ : ∃ A R, identity.lhs.toList = A ++ z :: R ∧ z ∉ R :=
          last_split z _ memu
        rw [hw, suffixAfterLast_append_cons z A R absent]
        exact absent
      have zeroV : (suffixAfterLast z identity.rhs.toList).count z = 0 := by
        apply List.count_eq_zero.mpr
        obtain ⟨A, R, hw, absent⟩ : ∃ A R, identity.rhs.toList = A ++ z :: R ∧ z ∉ R :=
          last_split z _ memv
        rw [hw, suffixAfterLast_append_cons z A R absent]
        exact absent
      rw [zeroU, zeroV]
    · exact suffix_eq_of_suffixValue memu memv (suffixValues z y different)
where
  last_split (z : Nat) : ∀ (w : List Nat), z ∈ w → ∃ A R, w = A ++ z :: R ∧ z ∉ R
    | [], mem => by simp at mem
    | d :: w, mem => by
        by_cases inRest : z ∈ w
        · obtain ⟨A, R, hw, absent⟩ := last_split z w inRest
          exact ⟨d :: A, R, by simp [hw], absent⟩
        · have hd : d = z := by
            simp only [List.mem_cons] at mem
            rcases mem with h | h
            · exact h.symm
            · exact absurd h inRest
          exact ⟨[], w, by simp [hd], inRest⟩

end SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleInvariants

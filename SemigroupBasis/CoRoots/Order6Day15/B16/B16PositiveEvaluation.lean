import SemigroupBasis.Examples.FinalMarkerThree

namespace SemigroupBasis.CoRoots.Order6Day15.B16

/-- The already implemented opposite final-marker semigroup, not a new basis. -/
def positive : Semigroup (Fin 3) := Examples.finalMarkerThree.semigroup.opposite

theorem positive_mul (a b : Fin 3) :
    positive.mul a b = if b = 2 then a else 0 := rfl

theorem positive_fold (rho : Nat → Fin 3) (xs : List Nat) (a : Fin 3) :
    xs.foldl (fun value x => positive.mul value (rho x)) a =
      if ∀ x ∈ xs, rho x = 2 then a else 0 := by
  induction xs generalizing a with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, false_implies, implies_true, if_true]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih, positive_mul]
      have both : (∀ y ∈ x :: xs, rho y = 2) ↔
          rho x = 2 ∧ ∀ y ∈ xs, rho y = 2 := by
        constructor
        · intro h
          exact ⟨h x (List.Mem.head _), fun y hy => h y (List.Mem.tail _ hy)⟩
        · rintro ⟨hx, hs⟩ y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hx
          · exact hs y hy
      by_cases hx : rho x = 2
      · by_cases hs : ∀ y ∈ xs, rho y = 2
        · rw [if_pos hs, if_pos hx, if_pos (both.mpr ⟨hx, hs⟩)]
        · have hn : ¬ ∀ y ∈ x :: xs, rho y = 2 := fun h => hs (both.mp h).2
          rw [if_neg hs, if_neg hn]
      · have hn : ¬ ∀ y ∈ x :: xs, rho y = 2 := fun h => hx (both.mp h).1
        rw [if_neg hx, if_neg hn]
        split <;> rfl

theorem positive_eval (rho : Nat → Fin 3) (w : Word Nat) :
    positive.eval rho w =
      if ∀ x ∈ w.tail, rho x = 2 then rho w.head else 0 := by
  exact positive_fold rho w.tail (rho w.head)

def separator (z x : Nat) : Fin 3 := if x = z then 1 else 2

theorem separator_self (z : Nat) : separator z z = 1 := by
  unfold separator
  rw [if_pos rfl]

theorem separator_other (z x : Nat) (h : x ≠ z) : separator z x = 2 := by
  unfold separator
  rw [if_neg h]

theorem separator_tail (z : Nat) (xs : List Nat) :
    (∀ x ∈ xs, separator z x = 2) ↔ z ∉ xs := by
  constructor
  · intro h hz
    have bad : (1 : Fin 3) = 2 := (separator_self z).symm.trans (h z hz)
    exact (by decide : (1 : Fin 3) ≠ 2) bad
  · intro hz x hx
    have hne : x ≠ z := by
      intro h
      exact hz (h ▸ hx)
    exact separator_other z x hne

theorem separator_eval (z : Nat) (w : Word Nat) :
    positive.eval (separator z) w =
      if z ∈ w.tail then 0 else if w.head = z then 1 else 2 := by
  rw [positive_eval]
  by_cases hz : z ∈ w.tail
  · have hn : ¬ ∀ x ∈ w.tail, separator z x = 2 :=
      fun h => (separator_tail z w.tail).mp h hz
    rw [if_neg hn, if_pos hz]
  · rw [if_pos ((separator_tail z w.tail).mpr hz), if_neg hz]
    rfl

theorem separator_zero_iff (z : Nat) (w : Word Nat) :
    positive.eval (separator z) w = 0 ↔ z ∈ w.tail := by
  rw [separator_eval]
  by_cases hz : z ∈ w.tail
  · rw [if_pos hz]
    exact ⟨fun _ => hz, fun _ => rfl⟩
  · rw [if_neg hz]
    constructor
    · intro bad
      by_cases hh : w.head = z
      · rw [if_pos hh] at bad
        exact False.elim ((by decide : (1 : Fin 3) ≠ 0) bad)
      · rw [if_neg hh] at bad
        exact False.elim ((by decide : (2 : Fin 3) ≠ 0) bad)
    · intro bad
      exact False.elim (hz bad)

theorem separator_one_iff (z : Nat) (w : Word Nat) :
    positive.eval (separator z) w = 1 ↔ w.head = z ∧ z ∉ w.tail := by
  rw [separator_eval]
  by_cases hz : z ∈ w.tail
  · rw [if_pos hz]
    constructor
    · intro bad
      exact False.elim ((by decide : (0 : Fin 3) ≠ 1) bad)
    · intro bad
      exact False.elim (bad.2 hz)
  · rw [if_neg hz]
    by_cases hh : w.head = z
    · rw [if_pos hh]
      exact ⟨fun _ => ⟨hh, hz⟩, fun _ => rfl⟩
    · rw [if_neg hh]
      constructor
      · intro bad
        exact False.elim ((by decide : (2 : Fin 3) ≠ 1) bad)
      · intro bad
        exact False.elim (hh bad.1)

theorem valid_tail_support {u v : Word Nat}
    (valid : ∀ rho : Nat → Fin 3, positive.eval rho u = positive.eval rho v) :
    ∀ z, z ∈ u.tail ↔ z ∈ v.tail := by
  intro z
  constructor
  · intro hz
    have hu : positive.eval (separator z) u = 0 := (separator_zero_iff z u).mpr hz
    have hv : positive.eval (separator z) v = 0 := (valid (separator z)).symm.trans hu
    exact (separator_zero_iff z v).mp hv
  · intro hz
    have hv : positive.eval (separator z) v = 0 := (separator_zero_iff z v).mpr hz
    have hu : positive.eval (separator z) u = 0 := (valid (separator z)).trans hv
    exact (separator_zero_iff z u).mp hu

theorem valid_simple_head {u v : Word Nat}
    (valid : ∀ rho : Nat → Fin 3, positive.eval rho u = positive.eval rho v) :
    ∀ z, (u.head = z ∧ z ∉ u.tail) ↔ (v.head = z ∧ z ∉ v.tail) := by
  intro z
  constructor
  · intro hz
    have hu : positive.eval (separator z) u = 1 := (separator_one_iff z u).mpr hz
    have hv : positive.eval (separator z) v = 1 := (valid (separator z)).symm.trans hu
    exact (separator_one_iff z v).mp hv
  · intro hz
    have hv : positive.eval (separator z) v = 1 := (separator_one_iff z v).mpr hz
    have hu : positive.eval (separator z) u = 1 := (valid (separator z)).trans hv
    exact (separator_one_iff z u).mp hu

end SemigroupBasis.CoRoots.Order6Day15.B16

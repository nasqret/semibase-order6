import SemigroupBasis.CoRoots.Order6Day15.B16.B16SquareSupport

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

def insertCanonical (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a = b then b :: bs else if a < b then a :: b :: bs else b :: insertCanonical a bs

def canonicalSupport : List Nat → List Nat
  | [] => []
  | a :: xs => insertCanonical a (canonicalSupport xs)

theorem mem_insertCanonical (x a : Nat) (xs : List Nat) :
    x ∈ insertCanonical a xs ↔ x = a ∨ x ∈ xs := by
  induction xs with
  | nil => simp only [insertCanonical, List.mem_cons, List.not_mem_nil, or_false]
  | cons b bs ih =>
      by_cases eq : a = b
      · subst a
        rw [insertCanonical, if_pos rfl]
        simp only [List.mem_cons, or_self_left]
      · by_cases lt : a < b
        · simp only [insertCanonical, if_neg eq, if_pos lt, List.mem_cons]
        · simp only [insertCanonical, if_neg eq, if_neg lt, List.mem_cons, ih, or_left_comm]

theorem mem_canonicalSupport (a : Nat) (xs : List Nat) :
    a ∈ canonicalSupport xs ↔ a ∈ xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      change a ∈ insertCanonical b (canonicalSupport bs) ↔ a ∈ b :: bs
      rw [mem_insertCanonical, ih, List.mem_cons]

theorem insertCanonical_sorted (a : Nat) (xs : List Nat)
    (sorted : List.Pairwise (fun x y : Nat => x < y) xs) :
    List.Pairwise (fun x y : Nat => x < y) (insertCanonical a xs) := by
  induction xs with
  | nil => exact List.Pairwise.cons (fun _ h => False.elim (List.not_mem_nil h)) List.Pairwise.nil
  | cons b bs ih =>
      rcases List.pairwise_cons.mp sorted with ⟨head,tail⟩
      by_cases eq : a = b
      · subst a
        rw [insertCanonical, if_pos rfl]
        exact List.pairwise_cons.mpr ⟨head,tail⟩
      · by_cases lt : a < b
        · rw [insertCanonical, if_neg eq, if_pos lt]
          apply List.pairwise_cons.mpr
          refine ⟨?_, List.pairwise_cons.mpr ⟨head,tail⟩⟩
          intro c hc
          rcases List.mem_cons.mp hc with eqc | mem
          · subst c; exact lt
          · exact Nat.lt_trans lt (head c mem)
        · rw [insertCanonical, if_neg eq, if_neg lt]
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih tail⟩
          intro c hc
          rcases (mem_insertCanonical c a bs).mp hc with eqc | mem
          · subst c; omega
          · exact head c mem

theorem canonicalSupport_sorted (xs : List Nat) :
    List.Pairwise (fun x y : Nat => x < y) (canonicalSupport xs) := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons a xs ih => exact insertCanonical_sorted a (canonicalSupport xs) ih

theorem strictly_sorted_eq_of_support (xs ys : List Nat)
    (leftSorted : List.Pairwise (fun x y : Nat => x < y) xs)
    (rightSorted : List.Pairwise (fun x y : Nat => x < y) ys)
    (same : ∀ a, a ∈ xs ↔ a ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons b bs => exact False.elim (List.not_mem_nil ((same b).mpr (List.Mem.head _)))
  | cons a as ih =>
      cases ys with
      | nil => exact False.elim (List.not_mem_nil ((same a).mp (List.Mem.head _)))
      | cons b bs =>
          rcases List.pairwise_cons.mp leftSorted with ⟨ha,has⟩
          rcases List.pairwise_cons.mp rightSorted with ⟨hb,hbs⟩
          have heads : a = b := by
            apply Classical.byContradiction
            intro ne
            have amem : a ∈ bs := by
              rcases List.mem_cons.mp ((same a).mp (List.Mem.head _)) with eq | mem
              · exact False.elim (ne eq)
              · exact mem
            have bmem : b ∈ as := by
              rcases List.mem_cons.mp ((same b).mpr (List.Mem.head _)) with eq | mem
              · exact False.elim (ne eq.symm)
              · exact mem
            have ab := ha b bmem
            have ba := hb a amem
            omega
          subst b
          have tailSame : ∀ c, c ∈ as ↔ c ∈ bs := by
            intro c
            constructor
            · intro hc
              rcases List.mem_cons.mp ((same c).mp (List.Mem.tail _ hc)) with eq | mem
              · subst c; have bad := ha a hc; omega
              · exact mem
            · intro hc
              rcases List.mem_cons.mp ((same c).mpr (List.Mem.tail _ hc)) with eq | mem
              · subst c; have bad := hb a hc; omega
              · exact mem
          exact congrArg (List.cons a) (ih bs has hbs tailSame)

theorem canonicalSupport_eq_of_support (xs ys : List Nat) (same : ∀ a, a ∈ xs ↔ a ∈ ys) :
    canonicalSupport xs = canonicalSupport ys :=
  strictly_sorted_eq_of_support _ _ (canonicalSupport_sorted xs) (canonicalSupport_sorted ys)
    (fun a => (mem_canonicalSupport a xs).trans ((same a).trans (mem_canonicalSupport a ys).symm))

theorem canonicalSupport_idempotent (xs : List Nat) :
    canonicalSupport (canonicalSupport xs) = canonicalSupport xs :=
  canonicalSupport_eq_of_support _ _ (fun a => mem_canonicalSupport a xs)

theorem squares_canonicalSupport (xs : List Nat) : Rel (squares xs) (squares (canonicalSupport xs)) :=
  squares_same_support xs (canonicalSupport xs) (fun a => (mem_canonicalSupport a xs).symm)

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach

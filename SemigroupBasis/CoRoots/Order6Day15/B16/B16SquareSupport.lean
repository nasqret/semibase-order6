import SemigroupBasis.CoRoots.Order6Day15.B16.B16Reservoir

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

theorem squares_append (xs ys : List Nat) : squares (xs ++ ys) = squares xs ++ squares ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih => exact congrArg (List.cons a) (congrArg (List.cons a) ih)

theorem mem_squares_iff (a : Nat) (xs : List Nat) : a ∈ squares xs ↔ a ∈ xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      simp only [squares, List.mem_cons, ih, or_self_left]

theorem commute_square_blocks (xs ys : List Nat) :
    Rel (squares xs ++ squares ys) (squares ys ++ squares xs) := by
  induction ys with
  | nil =>
      change Rel (squares xs ++ []) (squares xs)
      rw [List.append_nil]
      exact Rel.refl _
  | cons a ys ih =>
      have framed := (commute_squares xs a).suffix (squares ys)
      have first : Rel (squares xs ++ a :: a :: squares ys)
          (a :: a :: (squares xs ++ squares ys)) := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using framed
      have second : Rel (a :: a :: (squares xs ++ squares ys))
          (a :: a :: (squares ys ++ squares xs)) := Rel.prependCtx [a,a] ih
      exact first.trans second

theorem squares_absorb_block (xs ys : List Nat) (covered : ∀ a ∈ ys, a ∈ xs) :
    Rel (squares xs ++ squares ys) (squares xs) :=
  squares_absorb xs (squares ys) (fun a ha => covered a ((mem_squares_iff a ys).mp ha))

theorem squares_same_support (xs ys : List Nat) (same : ∀ a, a ∈ xs ↔ a ∈ ys) :
    Rel (squares xs) (squares ys) := by
  have first : Rel (squares xs) (squares xs ++ squares ys) :=
    (squares_absorb_block xs ys (fun a ha => (same a).mpr ha)).symm
  have middle : Rel (squares xs ++ squares ys) (squares ys ++ squares xs) := commute_square_blocks xs ys
  have last : Rel (squares ys ++ squares xs) (squares ys) :=
    squares_absorb_block ys xs (fun a ha => (same a).mp ha)
  exact first.trans (middle.trans last)

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach

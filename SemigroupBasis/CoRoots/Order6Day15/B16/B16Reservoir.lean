import SemigroupBasis.CoRoots.Order6Day15.B16.B16ListReach

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

open SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

theorem split_member (a : Nat) (xs : List Nat) (h : a ∈ xs) :
    ∃ pre post, xs = pre ++ a :: post := by
  induction xs with
  | nil => exact False.elim (List.not_mem_nil h)
  | cons b bs ih =>
      rcases List.mem_cons.mp h with eq | mem
      · subst b; exact ⟨[], bs, rfl⟩
      · rcases ih mem with ⟨pre, post, eq⟩
        exact ⟨b :: pre, post, congrArg (List.cons b) eq⟩

theorem member_of_positive_count (a : Nat) (xs : List Nat) (h : 1 ≤ xs.count a) : a ∈ xs := by
  by_cases hm : a ∈ xs
  · exact hm
  · have zero : xs.count a = 0 := List.count_eq_zero_of_not_mem hm
    omega

theorem split_two (a : Nat) (xs : List Nat) (h : 2 ≤ xs.count a) :
    ∃ pre mid post, xs = pre ++ a :: (mid ++ a :: post) := by
  induction xs with
  | nil => change 2 ≤ 0 at h; omega
  | cons b bs ih =>
      by_cases eq : b = a
      · subst b
        rw [List.count_cons_self] at h
        have positive : 1 ≤ bs.count a := by omega
        rcases split_member a bs (member_of_positive_count a bs positive) with ⟨mid, post, eq⟩
        exact ⟨[], mid, post, congrArg (List.cons a) eq⟩
      · have countEq : (b :: bs).count a = bs.count a := List.count_cons_of_ne eq
        have ht : 2 ≤ bs.count a := countEq ▸ h
        rcases ih ht with ⟨pre, mid, post, split⟩
        exact ⟨b :: pre, mid, post, congrArg (List.cons b) split⟩

theorem duplicate_head (a : Nat) (xs : List Nat) (h : a ∈ xs) :
    Rel (a :: xs) (a :: a :: xs) := by
  rcases split_member a xs h with ⟨pre, post, eq⟩
  rw [eq]
  cases pre with
  | nil => exact (power a).suffix post
  | cons b bs =>
      have step : Rel (a :: ((b :: bs) ++ [a]))
          (a :: a :: ((b :: bs) ++ [a])) := repeatHead a (Word.mk b bs)
      have framed := step.suffix post
      simpa only [List.cons_append, List.append_assoc, List.nil_append] using framed

theorem adjoin_head_square (a : Nat) (xs : List Nat) (h : a ∈ xs) :
    Rel (a :: xs) (a :: a :: a :: xs) :=
  (duplicate_head a xs h).trans ((power a).suffix xs)

theorem adjoin_repeated_square (a b : Nat) (xs : List Nat)
    (headRepeated : a ∈ xs) (bRepeated : 2 ≤ (a :: xs).count b) :
    Rel (a :: xs) (b :: b :: a :: xs) := by
  by_cases eq : a = b
  · subst b; exact adjoin_head_square a xs headRepeated
  · have countEq : (a :: xs).count b = xs.count b := List.count_cons_of_ne eq
    have twice : 2 ≤ xs.count b := countEq ▸ bRepeated
    rcases split_two b xs twice with ⟨pre, mid, post, split⟩
    have doubled : Rel (a :: xs) (a :: a :: xs) := duplicate_head a xs headRepeated
    have moved : Rel (a :: a :: xs) (b :: b :: a :: a :: xs) := by
      rw [split]
      have framed := (square_prefix_adjoin a b pre mid).suffix post
      simpa only [List.cons_append, List.append_assoc, List.nil_append] using framed
    have restored : Rel (b :: b :: a :: a :: xs) (b :: b :: a :: xs) :=
      Rel.prependCtx [b,b] doubled.symm
    exact doubled.trans (moved.trans restored)

def squares : List Nat → List Nat
  | [] => []
  | a :: as => a :: a :: squares as

theorem adjoin_squares (a : Nat) (xs ns : List Nat) (headRepeated : a ∈ xs)
    (repeated : ∀ b ∈ ns, 2 ≤ (a :: xs).count b) :
    Rel (a :: xs) (squares ns ++ a :: xs) := by
  induction ns with
  | nil => exact Rel.refl _
  | cons b bs ih =>
      have hb : 2 ≤ (a :: xs).count b := repeated b (List.Mem.head _)
      have ht : ∀ c ∈ bs, 2 ≤ (a :: xs).count c := fun c h => repeated c (List.Mem.tail _ h)
      have first := adjoin_repeated_square a b xs headRepeated hb
      have rest := Rel.prependCtx [b,b] (ih ht)
      exact first.trans rest

theorem commute_squares (ns : List Nat) (a : Nat) :
    Rel (squares ns ++ [a,a]) ([a,a] ++ squares ns) := by
  induction ns with
  | nil => exact Rel.refl [a,a]
  | cons b bs ih =>
      have first : Rel (b :: b :: (squares bs ++ [a,a]))
          (b :: b :: a :: a :: squares bs) := Rel.prependCtx [b,b] ih
      have second : Rel (b :: b :: a :: a :: squares bs)
          (a :: a :: b :: b :: squares bs) := (commute b a).suffix (squares bs)
      exact first.trans second

theorem squares_absorb_letter (ns : List Nat) (a : Nat) (h : a ∈ ns) :
    Rel (squares ns ++ [a]) (squares ns) := by
  induction ns with
  | nil => exact False.elim (List.not_mem_nil h)
  | cons b bs ih =>
      rcases List.mem_cons.mp h with eq | mem
      · subst b
        have first := (commute_squares bs a).symm.suffix [a]
        have first' : Rel (a :: a :: (squares bs ++ [a]))
            (squares bs ++ [a,a,a]) := by
          simpa only [List.cons_append, List.nil_append, List.append_assoc] using first
        have second : Rel (squares bs ++ [a,a,a]) (squares bs ++ [a,a]) :=
          Rel.prependCtx (squares bs) (power a).symm
        have third : Rel (squares bs ++ [a,a]) (a :: a :: squares bs) := commute_squares bs a
        exact first'.trans (second.trans third)
      · exact Rel.prependCtx [b,b] (ih mem)

theorem squares_absorb (ns gap : List Nat) (covered : ∀ a ∈ gap, a ∈ ns) :
    Rel (squares ns ++ gap) (squares ns) := by
  induction gap with
  | nil =>
      rw [List.append_nil]
      exact Rel.refl (squares ns)
  | cons a gap ih =>
      have one := (squares_absorb_letter ns a (covered a (List.Mem.head _))).suffix gap
      have first : Rel (squares ns ++ a :: gap) (squares ns ++ gap) := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using one
      have rest : Rel (squares ns ++ gap) (squares ns) :=
        ih (fun b h => covered b (List.Mem.tail _ h))
      exact first.trans rest

/-- Replace a nonempty first gap by a square reservoir; the suffix is unchanged. -/
theorem reservoir_core (a : Nat) (gap tail ns : List Nat)
    (headRepeated : a ∈ gap ++ tail)
    (repeated : ∀ b ∈ ns, 2 ≤ (a :: (gap ++ tail)).count b)
    (covered : ∀ b ∈ a :: gap, b ∈ ns) :
    Rel (a :: (gap ++ tail)) (squares ns ++ tail) := by
  have first := adjoin_squares a (gap ++ tail) ns headRepeated repeated
  have absorbed := (squares_absorb ns (a :: gap) covered).suffix tail
  have second : Rel (squares ns ++ a :: (gap ++ tail)) (squares ns ++ tail) := by
    simpa only [List.append_assoc, List.cons_append] using absorbed
  exact first.trans second

/-- The arbitrary prefix contains no selected nonsimple letter; counts are GLOBAL. -/
theorem reservoir_of_global_counts (pre : List Nat) (a : Nat) (gap tail ns : List Nat)
    (avoid : ∀ b ∈ ns, b ∉ pre)
    (repeated : ∀ b ∈ ns, 2 ≤ (pre ++ a :: (gap ++ tail)).count b)
    (covered : ∀ b ∈ a :: gap, b ∈ ns) :
    Rel (pre ++ a :: (gap ++ tail)) (pre ++ (squares ns ++ tail)) := by
  have localCounts : ∀ b ∈ ns, 2 ≤ (a :: (gap ++ tail)).count b := by
    intro b hb
    have original := repeated b hb
    have zero : pre.count b = 0 := List.count_eq_zero_of_not_mem (avoid b hb)
    rw [List.count_append, zero, Nat.zero_add] at original
    exact original
  have ha : a ∈ ns := covered a (List.Mem.head _)
  have countA := localCounts a ha
  rw [List.count_cons_self] at countA
  have positive : 1 ≤ (gap ++ tail).count a := by omega
  have actual : Rel (a :: (gap ++ tail)) (squares ns ++ tail) :=
    reservoir_core a gap tail ns (member_of_positive_count a _ positive) localCounts covered
  exact Rel.prependCtx pre actual

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach

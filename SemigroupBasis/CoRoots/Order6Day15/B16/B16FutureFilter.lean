import SemigroupBasis.CoRoots.Order6Day15.B16.B16SquareSupport
import SemigroupBasis.CoRoots.Order6Day15.B16.B16GapMoves

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

/-- Retain exactly those occurrences whose letter is absent from the future suffix. -/
def finalLetters : List Nat → List Nat → List Nat
  | [], _ => []
  | a :: xs, post => if a ∈ post then finalLetters xs post else a :: finalLetters xs post

theorem mem_finalLetters_iff (a : Nat) (xs post : List Nat) :
    a ∈ finalLetters xs post ↔ a ∈ xs ∧ a ∉ post := by
  induction xs with
  | nil =>
      constructor
      · intro h; exact False.elim (List.not_mem_nil h)
      · intro h; exact False.elim (List.not_mem_nil h.1)
  | cons b bs ih =>
      by_cases hb : b ∈ post
      · rw [finalLetters, if_pos hb]
        constructor
        · intro h
          have h' := ih.mp h
          exact ⟨List.Mem.tail _ h'.1, h'.2⟩
        · intro h
          rcases List.mem_cons.mp h.1 with eq | mem
          · subst a; exact False.elim (h.2 hb)
          · exact ih.mpr ⟨mem,h.2⟩
      · rw [finalLetters, if_neg hb]
        constructor
        · intro h
          rcases List.mem_cons.mp h with eq | mem
          · subst a; exact ⟨List.Mem.head _,hb⟩
          · have h' := ih.mp mem
            exact ⟨List.Mem.tail _ h'.1,h'.2⟩
        · intro h
          rcases List.mem_cons.mp h.1 with eq | mem
          · subst a; exact List.Mem.head _
          · exact List.Mem.tail _ (ih.mpr ⟨mem,h.2⟩)

theorem finalLetters_covered (ns xs post : List Nat) (covered : ∀ a ∈ xs, a ∈ ns) :
    ∀ a ∈ finalLetters xs post, a ∈ ns :=
  fun a ha => covered a ((mem_finalLetters_iff a xs post).mp ha).1

theorem filter_future_squares (ns pre : List Nat) (a : Nat) (xs post : List Nat)
    (ha : a ∈ ns) (covered : ∀ b ∈ xs, b ∈ ns) :
    Rel (squares ns ++ (pre ++ a :: (squares xs ++ post)))
      (squares ns ++ (pre ++ a :: (squares (finalLetters xs post) ++ post))) := by
  induction xs generalizing pre a with
  | nil => exact Rel.refl _
  | cons b bs ih =>
      have hb : b ∈ ns := covered b (List.Mem.head _)
      have restCovered : ∀ c ∈ bs, c ∈ ns := fun c hc => covered c (List.Mem.tail _ hc)
      by_cases future : b ∈ post
      · rcases split_member b post future with ⟨before, after, eq⟩
        have deletion := delete_nonfinal_square ns pre a b (squares bs ++ before) after ha hb
        have first : Rel (squares ns ++ (pre ++ a :: (squares (b :: bs) ++ post)))
            (squares ns ++ (pre ++ a :: (squares bs ++ post))) := by
          rw [eq]
          simpa only [squares, List.append_assoc, List.cons_append, List.nil_append] using deletion
        have second : Rel (squares ns ++ (pre ++ a :: (squares bs ++ post)))
            (squares ns ++ (pre ++ a :: (squares (finalLetters bs post) ++ post))) :=
          ih pre a ha restCovered
        have combined := first.trans second
        simpa only [finalLetters, if_pos future] using combined
      · have rest : Rel (squares ns ++ ((pre ++ [a,b]) ++ b :: (squares bs ++ post)))
            (squares ns ++ ((pre ++ [a,b]) ++ b :: (squares (finalLetters bs post) ++ post))) :=
          ih (pre ++ [a,b]) b hb restCovered
        simpa only [finalLetters, if_neg future, squares, List.append_assoc,
          List.cons_append, List.nil_append] using rest

/-- Keep both anchor copies, including when the anchor also occurs in the future. -/
theorem filter_future_doubled (ns pre : List Nat) (a : Nat) (xs post : List Nat)
    (ha : a ∈ ns) (covered : ∀ b ∈ xs, b ∈ ns) :
    Rel (squares ns ++ (pre ++ a :: a :: (squares xs ++ post)))
      (squares ns ++ (pre ++ a :: a :: (squares (finalLetters xs post) ++ post))) := by
  have framed := filter_future_squares ns (pre ++ [a]) a xs post ha covered
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using framed

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach

import SemigroupBasis.CoRoots.Order6Day15.B16.B16FutureFilter

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

theorem gap_render_preserving_head (ns pre : List Nat) (a : Nat) (xs post fs : List Nat)
    (ha : a ∈ ns) (covered : ∀ b ∈ xs, b ∈ ns)
    (finalSupport : ∀ b, b ∈ fs ↔ b ∈ xs ∧ b ∉ post) :
    Rel (squares ns ++ (pre ++ a :: (xs ++ post)))
      (squares ns ++ (pre ++ a :: (squares fs ++ post))) := by
  have first := gap_square_tail ns pre a xs post ha covered
  have second := filter_future_squares ns pre a xs post ha covered
  have block : Rel (squares (finalLetters xs post)) (squares fs) :=
    squares_same_support _ _ (fun b => (mem_finalLetters_iff b xs post).trans (finalSupport b).symm)
  have third : Rel (squares ns ++ (pre ++ a :: (squares (finalLetters xs post) ++ post)))
      (squares ns ++ (pre ++ a :: (squares fs ++ post))) :=
    Rel.prependCtx (squares ns) (Rel.prependCtx pre (Rel.cons a (block.suffix post)))
  exact first.trans (second.trans third)

theorem gap_render_pinned (ns pre : List Nat) (a : Nat) (xs post fs : List Nat)
    (ha : a ∈ ns) (covered : ∀ b ∈ xs, b ∈ ns)
    (pinned : a ∉ xs ++ post)
    (finalSupport : ∀ b, b ∈ fs ↔ b ∈ xs ∧ b ∉ post) :
    Rel (squares ns ++ (pre ++ a :: (xs ++ post)))
      (squares ns ++ (pre ++ a :: (squares fs ++ post))) ∧ a ∉ squares fs ++ post := by
  refine ⟨gap_render_preserving_head ns pre a xs post fs ha covered finalSupport, ?_⟩
  intro mem
  rcases List.mem_append.mp mem with left | right
  · have inFs : a ∈ fs := (mem_squares_iff a fs).mp left
    have inXs : a ∈ xs := ((finalSupport a).mp inFs).1
    exact pinned (List.mem_append.mpr (Or.inl inXs))
  · exact pinned (List.mem_append.mpr (Or.inr right))

theorem anchored_final_support (b : Nat) (xs post fs : List Nat)
    (finalSupport : ∀ c, c ∈ fs ↔ c ∈ xs ∧ c ∉ post ∧ c ≠ b) :
    ∀ c, c ∈ b :: finalLetters xs post ↔ c ∈ b :: fs := by
  intro c
  constructor
  · intro mem
    rcases List.mem_cons.mp mem with eq | tail
    · exact List.mem_cons.mpr (Or.inl eq)
    · by_cases eq : c = b
      · exact List.mem_cons.mpr (Or.inl eq)
      · have fin := (mem_finalLetters_iff c xs post).mp tail
        exact List.Mem.tail _ ((finalSupport c).mpr ⟨fin.1,fin.2,eq⟩)
  · intro mem
    rcases List.mem_cons.mp mem with eq | tail
    · exact List.mem_cons.mpr (Or.inl eq)
    · have fin := (finalSupport c).mp tail
      exact List.Mem.tail _ ((mem_finalLetters_iff c xs post).mpr ⟨fin.1,fin.2.1⟩)

theorem gap_render_unpinned (ns pre : List Nat) (a : Nat) (xs post : List Nat)
    (b : Nat) (fs : List Nat) (ha : a ∈ ns) (covered : ∀ c ∈ xs, c ∈ ns)
    (later : a ∈ xs ++ post) (hb : b ∈ ns) (active : b = a ∨ b ∈ xs ++ post)
    (finalSupport : ∀ c, c ∈ fs ↔ c ∈ a :: xs ∧ c ∉ post ∧ c ≠ b) :
    Rel (squares ns ++ (pre ++ a :: (xs ++ post)))
      (squares ns ++ (pre ++ b :: b :: (squares fs ++ post))) := by
  have first : Rel (squares ns ++ (pre ++ a :: (xs ++ post)))
      (squares ns ++ (pre ++ a :: a :: (squares xs ++ post))) :=
    gap_square_unpinned ns pre a xs post ha covered later
  have activeLift : b = a ∨ b ∈ squares xs ++ post := by
    rcases active with eq | mem
    · exact Or.inl eq
    · rcases List.mem_append.mp mem with left | right
      · exact Or.inr (List.mem_append.mpr (Or.inl ((mem_squares_iff b xs).mpr left)))
      · exact Or.inr (List.mem_append.mpr (Or.inr right))
  have second : Rel (squares ns ++ (pre ++ a :: a :: (squares xs ++ post)))
      (squares ns ++ (pre ++ b :: b :: a :: a :: (squares xs ++ post))) :=
    retarget_square_head ns pre a b (squares xs ++ post) ha hb activeLift
  have wholeCovered : ∀ c ∈ a :: xs, c ∈ ns := by
    intro c hc
    rcases List.mem_cons.mp hc with eq | mem
    · subst c; exact ha
    · exact covered c mem
  have third : Rel (squares ns ++ (pre ++ b :: b :: a :: a :: (squares xs ++ post)))
      (squares ns ++ (pre ++ b :: b :: (squares (finalLetters (a :: xs) post) ++ post))) :=
    filter_future_doubled ns pre b (a :: xs) post hb wholeCovered
  have block : Rel (squares (b :: finalLetters (a :: xs) post)) (squares (b :: fs)) :=
    squares_same_support _ _ (anchored_final_support b (a :: xs) post fs finalSupport)
  have fourth : Rel (squares ns ++ (pre ++ b :: b :: (squares (finalLetters (a :: xs) post) ++ post)))
      (squares ns ++ (pre ++ b :: b :: (squares fs ++ post))) :=
    Rel.prependCtx (squares ns) (Rel.prependCtx pre (block.suffix post))
  exact first.trans (second.trans (third.trans fourth))

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach

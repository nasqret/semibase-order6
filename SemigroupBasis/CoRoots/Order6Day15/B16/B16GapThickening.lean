import SemigroupBasis.CoRoots.Order6Day15.B16.B16Reservoir
import SemigroupBasis.CoRoots.Order6Day15.B16.B16ThickeningCertificates

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

theorem anchored_thicken_list (a b : Nat) (t : List Nat) (nonempty : t ≠ []) :
    Rel (a :: a :: b :: b :: (t ++ [a,b]))
      (a :: a :: b :: b :: (t ++ [a,b,b])) := by
  cases t with
  | nil => exact False.elim (nonempty rfl)
  | cons c cs =>
      have actual := (Rel.ofDerives anchoredThicken).subst
        (fun n => if n = 0 then Word.singleton a else
          if n = 1 then Word.singleton b else Word.mk c cs)
      exact actual

theorem adjoin_square_from_member (ns : List Nat) (a : Nat) (ha : a ∈ ns) :
    Rel (squares ns) (a :: a :: squares ns) := by
  have covered : ∀ b ∈ [a,a], b ∈ ns := by
    intro b hb
    rcases List.mem_cons.mp hb with eq | hb
    · subst b; exact ha
    · rcases List.mem_cons.mp hb with eq | hb
      · subst b; exact ha
      · exact False.elim (List.not_mem_nil hb)
  have expanded : Rel (squares ns) (squares ns ++ [a,a]) :=
    (squares_absorb ns [a,a] covered).symm
  exact expanded.trans (commute_squares ns a)

theorem adjoin_pair_from_members (ns : List Nat) (a b : Nat)
    (ha : a ∈ ns) (hb : b ∈ ns) :
    Rel (squares ns) (a :: a :: b :: b :: squares ns) := by
  have first : Rel (squares ns) (a :: a :: squares ns) := adjoin_square_from_member ns a ha
  have second : Rel (a :: a :: squares ns) (a :: a :: b :: b :: squares ns) :=
    Rel.prependCtx [a,a] (adjoin_square_from_member ns b hb)
  exact first.trans second

theorem reservoir_nonempty (ns : List Nat) (a : Nat) (ha : a ∈ ns) (pre : List Nat) :
    squares ns ++ pre ≠ [] := by
  cases ns with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons b bs => intro eq; cases eq

/-- Duplicate the second of an adjacent pair, keeping all outside context fixed. -/
theorem thicken_pair (ns pre : List Nat) (a b : Nat) (post : List Nat)
    (ha : a ∈ ns) (hb : b ∈ ns) :
    Rel (squares ns ++ (pre ++ a :: b :: post))
      (squares ns ++ (pre ++ a :: b :: b :: post)) := by
  have added := (adjoin_pair_from_members ns a b ha hb).suffix (pre ++ a :: b :: post)
  have first : Rel (squares ns ++ (pre ++ a :: b :: post))
      (a :: a :: b :: b :: (squares ns ++ (pre ++ a :: b :: post))) := added
  have framed := (anchored_thicken_list a b (squares ns ++ pre)
    (reservoir_nonempty ns a ha pre)).suffix post
  have middle : Rel (a :: a :: b :: b :: (squares ns ++ (pre ++ a :: b :: post)))
      (a :: a :: b :: b :: (squares ns ++ (pre ++ a :: b :: b :: post))) := by
    simpa only [List.cons_append, List.append_assoc, List.nil_append] using framed
  have last : Rel (a :: a :: b :: b :: (squares ns ++ (pre ++ a :: b :: b :: post)))
      (squares ns ++ (pre ++ a :: b :: b :: post)) :=
    (adjoin_pair_from_members ns a b ha hb).symm.suffix (pre ++ a :: b :: b :: post)
  exact first.trans (middle.trans last)

theorem duplicate_nonhead (ns pre : List Nat) (a : Nat) (mid : List Nat)
    (b : Nat) (post : List Nat) (ha : a ∈ ns)
    (covered : ∀ c ∈ mid, c ∈ ns) (hb : b ∈ ns) :
    Rel (squares ns ++ (pre ++ a :: (mid ++ b :: post)))
      (squares ns ++ (pre ++ a :: (mid ++ b :: b :: post))) := by
  induction mid generalizing pre a with
  | nil => exact thicken_pair ns pre a b post ha hb
  | cons c cs ih =>
      have hc : c ∈ ns := covered c (List.Mem.head _)
      have restCovered : ∀ d ∈ cs, d ∈ ns := fun d hd => covered d (List.Mem.tail _ hd)
      have moved : Rel (squares ns ++ ((pre ++ [a]) ++ c :: (cs ++ b :: post)))
          (squares ns ++ ((pre ++ [a]) ++ c :: (cs ++ b :: b :: post))) :=
        ih (pre ++ [a]) c hc restCovered
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using moved

/-- Square every tail letter, retaining the gap's first occurrence exactly once. -/
theorem gap_square_tail (ns pre : List Nat) (a : Nat) (xs post : List Nat)
    (ha : a ∈ ns) (covered : ∀ b ∈ xs, b ∈ ns) :
    Rel (squares ns ++ (pre ++ a :: (xs ++ post)))
      (squares ns ++ (pre ++ a :: (squares xs ++ post))) := by
  induction xs generalizing pre a with
  | nil => exact Rel.refl _
  | cons b bs ih =>
      have hb : b ∈ ns := covered b (List.Mem.head _)
      have restCovered : ∀ c ∈ bs, c ∈ ns := fun c hc => covered c (List.Mem.tail _ hc)
      have first : Rel (squares ns ++ (pre ++ a :: b :: (bs ++ post)))
          (squares ns ++ (pre ++ a :: b :: b :: (bs ++ post))) :=
        thicken_pair ns pre a b (bs ++ post) ha hb
      have rest : Rel (squares ns ++ ((pre ++ [a,b]) ++ b :: (bs ++ post)))
          (squares ns ++ ((pre ++ [a,b]) ++ b :: (squares bs ++ post))) :=
        ih (pre ++ [a,b]) b hb restCovered
      have aligned : Rel (squares ns ++ (pre ++ a :: b :: b :: (bs ++ post)))
          (squares ns ++ (pre ++ a :: b :: b :: (squares bs ++ post))) := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using rest
      exact first.trans aligned

/-- An unpinned head may also be doubled, using its actual later occurrence. -/
theorem gap_square_unpinned (ns pre : List Nat) (a : Nat) (xs post : List Nat)
    (ha : a ∈ ns) (covered : ∀ b ∈ xs, b ∈ ns) (later : a ∈ xs ++ post) :
    Rel (squares ns ++ (pre ++ a :: (xs ++ post)))
      (squares ns ++ (pre ++ (squares (a :: xs) ++ post))) := by
  have first : Rel (squares ns ++ (pre ++ a :: (xs ++ post)))
      (squares ns ++ (pre ++ a :: a :: (xs ++ post))) :=
    Rel.prependCtx (squares ns) (Rel.prependCtx pre (duplicate_head a (xs ++ post) later))
  have allCovered : ∀ b ∈ a :: xs, b ∈ ns := by
    intro b hb
    rcases List.mem_cons.mp hb with eq | hb
    · subst b; exact ha
    · exact covered b hb
  have second : Rel (squares ns ++ (pre ++ a :: a :: (xs ++ post)))
      (squares ns ++ (pre ++ a :: a :: a :: (squares xs ++ post))) :=
    gap_square_tail ns pre a (a :: xs) post ha allCovered
  have third : Rel (squares ns ++ (pre ++ a :: a :: a :: (squares xs ++ post)))
      (squares ns ++ (pre ++ a :: a :: (squares xs ++ post))) :=
    Rel.prependCtx (squares ns) (Rel.prependCtx pre ((power a).symm.suffix (squares xs ++ post)))
  exact first.trans (second.trans third)

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach

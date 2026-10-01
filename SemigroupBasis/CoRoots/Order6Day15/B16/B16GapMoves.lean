import SemigroupBasis.CoRoots.Order6Day15.B16.B16GapThickening
import SemigroupBasis.CoRoots.Order6Day15.B16.B16GapMoveCertificates

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

theorem anchored_delete_list (a b : Nat) (t u : List Nat)
    (tNonempty : t ≠ []) (uNonempty : u ≠ []) :
    Rel (a :: a :: b :: b :: (t ++ a :: b :: (u ++ [b])))
      (a :: a :: b :: b :: (t ++ a :: (u ++ [b]))) := by
  cases t with
  | nil => exact False.elim (tNonempty rfl)
  | cons c cs =>
      cases u with
      | nil => exact False.elim (uNonempty rfl)
      | cons d ds =>
          have actual := (Rel.ofDerives anchoredDelete).subst
            (fun n => if n = 0 then Word.singleton a else
              if n = 1 then Word.singleton b else
                if n = 2 then Word.mk c cs else Word.mk d ds)
          exact actual

theorem head_transfer_list (a b : Nat) (t u : List Nat) (tNonempty : t ≠ []) :
    Rel (a :: a :: b :: b :: (t ++ a :: a :: (u ++ [b])))
      (a :: a :: (t ++ b :: a :: a :: (u ++ [b]))) := by
  cases t with
  | nil => exact False.elim (tNonempty rfl)
  | cons c cs =>
      cases u with
      | nil =>
          have actual := (Rel.ofDerives headTransferEmpty).subst
            (fun n => if n = 0 then Word.singleton a else
              if n = 1 then Word.singleton b else Word.mk c cs)
          exact actual
      | cons d ds =>
          have actual := (Rel.ofDerives headTransfer).subst
            (fun n => if n = 0 then Word.singleton a else
              if n = 1 then Word.singleton b else
                if n = 2 then Word.mk c cs else Word.mk d ds)
          exact actual

/-- Delete a nonhead occurrence when a later copy remains, without changing that copy. -/
theorem delete_pair (ns pre : List Nat) (a b : Nat) (mid post : List Nat)
    (ha : a ∈ ns) (hb : b ∈ ns) :
    Rel (squares ns ++ (pre ++ a :: b :: (mid ++ b :: post)))
      (squares ns ++ (pre ++ a :: (mid ++ b :: post))) := by
  cases mid with
  | nil => exact (thicken_pair ns pre a b post ha hb).symm
  | cons c cs =>
      have first : Rel (squares ns ++ (pre ++ a :: b :: ((c :: cs) ++ b :: post)))
          (a :: a :: b :: b :: (squares ns ++ (pre ++ a :: b :: ((c :: cs) ++ b :: post)))) :=
        (adjoin_pair_from_members ns a b ha hb).suffix (pre ++ a :: b :: ((c :: cs) ++ b :: post))
      have framed := (anchored_delete_list a b (squares ns ++ pre) (c :: cs)
        (reservoir_nonempty ns a ha pre) (by intro eq; cases eq)).suffix post
      have middle : Rel (a :: a :: b :: b :: (squares ns ++ (pre ++ a :: b :: ((c :: cs) ++ b :: post))))
          (a :: a :: b :: b :: (squares ns ++ (pre ++ a :: ((c :: cs) ++ b :: post)))) := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using framed
      have last : Rel (a :: a :: b :: b :: (squares ns ++ (pre ++ a :: ((c :: cs) ++ b :: post))))
          (squares ns ++ (pre ++ a :: ((c :: cs) ++ b :: post))) :=
        (adjoin_pair_from_members ns a b ha hb).symm.suffix (pre ++ a :: ((c :: cs) ++ b :: post))
      exact first.trans (middle.trans last)

theorem delete_nonhead (ns pre : List Nat) (a : Nat) (before : List Nat)
    (b : Nat) (mid post : List Nat) (ha : a ∈ ns)
    (covered : ∀ c ∈ before, c ∈ ns) (hb : b ∈ ns) :
    Rel (squares ns ++ (pre ++ a :: (before ++ b :: (mid ++ b :: post))))
      (squares ns ++ (pre ++ a :: (before ++ (mid ++ b :: post)))) := by
  induction before generalizing pre a with
  | nil => exact delete_pair ns pre a b mid post ha hb
  | cons c cs ih =>
      have hc : c ∈ ns := covered c (List.Mem.head _)
      have restCovered : ∀ d ∈ cs, d ∈ ns := fun d hd => covered d (List.Mem.tail _ hd)
      have moved : Rel (squares ns ++ ((pre ++ [a]) ++ c :: (cs ++ b :: (mid ++ b :: post))))
          (squares ns ++ ((pre ++ [a]) ++ c :: (cs ++ (mid ++ b :: post)))) :=
        ih (pre ++ [a]) c hc restCovered
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using moved

/-- In particular, an entire nonfinal square can be removed after a retained head. -/
theorem delete_nonfinal_square (ns pre : List Nat) (a b : Nat) (mid post : List Nat)
    (ha : a ∈ ns) (hb : b ∈ ns) :
    Rel (squares ns ++ (pre ++ a :: b :: b :: (mid ++ b :: post)))
      (squares ns ++ (pre ++ a :: (mid ++ b :: post))) :=
  (delete_pair ns pre a b (b :: mid) post ha hb).trans (delete_pair ns pre a b mid post ha hb)

/-- A suffix-active letter can become the new doubled head; the old square is retained. -/
theorem adjoin_active_square (ns pre : List Nat) (a b : Nat) (mid post : List Nat)
    (ha : a ∈ ns) (hb : b ∈ ns) :
    Rel (squares ns ++ (pre ++ a :: a :: (mid ++ b :: post)))
      (squares ns ++ (pre ++ b :: b :: a :: a :: (mid ++ b :: post))) := by
  have first : Rel (squares ns ++ (pre ++ a :: a :: (mid ++ b :: post)))
      (a :: a :: b :: b :: (squares ns ++ (pre ++ a :: a :: (mid ++ b :: post)))) :=
    (adjoin_pair_from_members ns a b ha hb).suffix (pre ++ a :: a :: (mid ++ b :: post))
  have framed := (head_transfer_list a b (squares ns ++ pre) mid
    (reservoir_nonempty ns a ha pre)).suffix post
  have transfer : Rel (a :: a :: b :: b :: (squares ns ++ (pre ++ a :: a :: (mid ++ b :: post))))
      (a :: a :: (squares ns ++ (pre ++ b :: a :: a :: (mid ++ b :: post)))) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using framed
  have restored : Rel (a :: a :: (squares ns ++ (pre ++ b :: a :: a :: (mid ++ b :: post))))
      (a :: a :: b :: b :: (squares ns ++ (pre ++ b :: a :: a :: (mid ++ b :: post)))) :=
    Rel.prependCtx [a,a] ((adjoin_square_from_member ns b hb).suffix
      (pre ++ b :: a :: a :: (mid ++ b :: post)))
  have removed : Rel (a :: a :: b :: b :: (squares ns ++ (pre ++ b :: a :: a :: (mid ++ b :: post))))
      (squares ns ++ (pre ++ b :: a :: a :: (mid ++ b :: post))) :=
    (adjoin_pair_from_members ns a b ha hb).symm.suffix (pre ++ b :: a :: a :: (mid ++ b :: post))
  have later : b ∈ a :: a :: (mid ++ b :: post) :=
    List.Mem.tail _ (List.Mem.tail _ (List.mem_append.mpr (Or.inr (List.Mem.head _))))
  have doubled : Rel (squares ns ++ (pre ++ b :: a :: a :: (mid ++ b :: post)))
      (squares ns ++ (pre ++ b :: b :: a :: a :: (mid ++ b :: post))) :=
    Rel.prependCtx (squares ns) (Rel.prependCtx pre (duplicate_head b _ later))
  exact first.trans (transfer.trans (restored.trans (removed.trans doubled)))

theorem retarget_square_head (ns pre : List Nat) (a b : Nat) (rest : List Nat)
    (ha : a ∈ ns) (hb : b ∈ ns) (active : b = a ∨ b ∈ rest) :
    Rel (squares ns ++ (pre ++ a :: a :: rest))
      (squares ns ++ (pre ++ b :: b :: a :: a :: rest)) := by
  rcases active with eq | mem
  · subst b
    have expanded : Rel (a :: a :: rest) (a :: a :: a :: a :: rest) :=
      ((power a).suffix rest).trans ((power a).suffix (a :: rest))
    exact Rel.prependCtx (squares ns) (Rel.prependCtx pre expanded)
  · rcases split_member b rest mem with ⟨mid, post, eq⟩
    rw [eq]
    exact adjoin_active_square ns pre a b mid post ha hb

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach

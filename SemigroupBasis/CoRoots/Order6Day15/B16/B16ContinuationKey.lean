import SemigroupBasis.CoRoots.Order6Day15.B16.B16Continuation

namespace SemigroupBasis.CoRoots.Order6Day15.B16

/-- Exhaustive occurrence decomposition, not a length-bounded normal form. -/
inductive ValueSections {S : Semigroup α} (D : SplitAction S) : List α → Prop
  | positive (xs : List α) (h : ∀ x ∈ xs, D.Pos x) : ValueSections D xs
  | one (pre post : List α) (i : α)
      (hp : ∀ x ∈ pre, D.Pos x) (hi : D.Low i) (hs : ∀ x ∈ post, D.Pos x) :
      ValueSections D (pre ++ i :: post)
  | many (pre mid post : List α) (i j : α) (hi : D.Low i) (hj : D.Low j) :
      ValueSections D (pre ++ i :: (mid ++ j :: post))

theorem value_sections {S : Semigroup α} (D : SplitAction S) (xs : List α) :
    ValueSections D xs := by
  induction xs with
  | nil =>
      exact .positive [] (fun _ h => False.elim (List.not_mem_nil h))
  | cons x xs ih =>
      cases ih with
      | positive ys hy =>
          rcases D.cover x with hx | hx
          · apply ValueSections.positive
            intro y h
            rcases List.mem_cons.mp h with rfl | h
            · exact hx
            · exact hy y h
          · exact .one [] _ x (fun _ h => False.elim (List.not_mem_nil h)) hx hy
      | one pre post i hp hi hs =>
          rcases D.cover x with hx | hx
          · have hpre : ∀ y ∈ x :: pre, D.Pos y := by
              intro y h
              rcases List.mem_cons.mp h with rfl | h
              · exact hx
              · exact hp y h
            exact .one (x :: pre) post i hpre hi hs
          · exact .many [] pre post x i hx hi
      | many pre mid post i j hi hj =>
          exact .many (x :: pre) mid post i j hi hj

theorem embedding_runTail (S : Semigroup α) (embed : Fin 3 → α)
    (hom : ∀ a b, S.mul (embed a) (embed b) = embed (positive.mul a b))
    (rho : Nat → Fin 3) (xs : List Nat) (a : Fin 3) :
    runTail S (embed a) (xs.map (fun x => embed (rho x))) =
      embed (xs.foldl (fun b x => positive.mul b (rho x)) a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, runTail_cons, hom, List.foldl_cons]
      exact ih (positive.mul a (rho x))

theorem evalValues_embedding (S : Semigroup α) (embed : Fin 3 → α)
    (hom : ∀ a b, S.mul (embed a) (embed b) = embed (positive.mul a b))
    (rho : Nat → Fin 3) (w : Word Nat) :
    evalValues S (w.toList.map (fun x => embed (rho x))) =
      some (embed (positive.eval rho w)) := by
  change some (runTail S (embed (rho w.head)) (w.tail.map (fun x => embed (rho x)))) =
    some (embed (positive.eval rho w))
  have h : runTail S (embed (rho w.head)) (w.tail.map (fun x => embed (rho x))) =
      embed (positive.eval rho w) := embedding_runTail S embed hom rho w.tail (rho w.head)
  exact congrArg some h

theorem positive_tail_action (S : Semigroup α) (embed : Fin 3 → α)
    (hom : ∀ a b, S.mul (embed a) (embed b) = embed (positive.mul a b))
    (rho : Nat → Fin 3) (a : α) (w : Word Nat) :
    runTail S a (w.toList.map (fun x => embed (rho x))) =
      S.mul a (embed (positive.eval rho w)) := by
  change runTail S (S.mul a (embed (rho w.head)))
    (w.tail.map (fun x => embed (rho x))) = S.mul a (embed (positive.eval rho w))
  have h : runTail S (embed (rho w.head)) (w.tail.map (fun x => embed (rho x))) =
      embed (positive.eval rho w) := embedding_runTail S embed hom rho w.tail (rho w.head)
  exact (runTail_mul S a (embed (rho w.head)) (w.tail.map (fun x => embed (rho x)))).trans
    (congrArg (S.mul a) h)

theorem samePKey_continuation (S : Semigroup α) (embed : Fin 3 → α)
    (hom : ∀ a b, S.mul (embed a) (embed b) = embed (positive.mul a b))
    {u v : Word Nat} (h : SamePKey u v) (rho : Nat → Fin 3) (a : α) :
    runTail S a (u.toList.map (fun x => embed (rho x))) =
      runTail S a (v.toList.map (fun x => embed (rho x))) := by
  rw [positive_tail_action S embed hom, positive_tail_action S embed hom]
  exact congrArg (fun b => S.mul a (embed b)) (positive_eval_eq_of_key h rho)

end SemigroupBasis.CoRoots.Order6Day15.B16

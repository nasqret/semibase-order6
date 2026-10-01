import SemigroupBasis.CoRoots.Order6Day15.B16.B16ObservationOne

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Literal

def positiveProject (a : Fin 6) : Fin 3 := if a = 3 then 0 else if a = 4 then 1 else 2

theorem positiveProject_spec : ∀ a : Fin 6,
    3 ≤ a.val → positiveEmbed (positiveProject a) = a := by decide

def liftedValuation (rho : Nat → Fin 6) : Nat → Fin 3 := fun x => positiveProject (rho x)

theorem map_positive_lift (rho : Nat → Fin 6) (xs : List Nat)
    (hp : ∀ x ∈ xs, 3 ≤ (rho x).val) :
    xs.map rho = xs.map (fun x => positiveEmbed (liftedValuation rho x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have headEq : rho x = positiveEmbed (liftedValuation rho x) :=
        (positiveProject_spec (rho x) (hp x (List.Mem.head _))).symm
      have tailPos : ∀ y ∈ xs, 3 ≤ (rho y).val := fun y hy => hp y (List.Mem.tail _ hy)
      have tailEq : xs.map rho = xs.map (fun y => positiveEmbed (liftedValuation rho y)) := ih tailPos
      exact (congrArg (fun a => a :: xs.map rho) headEq).trans
        (congrArg (List.cons (positiveEmbed (liftedValuation rho x))) tailEq)

theorem mapped_property (rho : Nat → α) (xs : List Nat) (Q : α → Prop)
    (h : ∀ x ∈ xs, Q (rho x)) : ∀ a ∈ xs.map rho, Q a := by
  intro a ha
  rcases List.mem_map.mp ha with ⟨x, hx, rfl⟩
  exact h x hx

theorem evalValues_valuation (S : Semigroup α) (rho : Nat → α) (w : Word Nat) :
    evalValues S (w.toList.map rho) = some (S.eval rho w) := by
  change some ((w.tail.map rho).foldl S.mul (rho w.head)) =
    some (w.tail.foldl (fun a x => S.mul a (rho x)) (rho w.head))
  rw [List.foldl_map]

theorem positive_word_value (S : Semigroup (Fin 6))
    (hom : ∀ a b, S.mul (positiveEmbed a) (positiveEmbed b) = positiveEmbed (positive.mul a b))
    (rho : Nat → Fin 6) (w : Word Nat) (hp : ∀ x ∈ w.toList, 3 ≤ (rho x).val) :
    evalValues S (w.toList.map rho) = some (positiveEmbed (positive.eval (liftedValuation rho) w)) := by
  have mapped : w.toList.map rho = w.toList.map (fun x => positiveEmbed (liftedValuation rho x)) :=
    map_positive_lift rho w.toList hp
  have value : evalValues S (w.toList.map (fun x => positiveEmbed (liftedValuation rho x))) =
      some (positiveEmbed (positive.eval (liftedValuation rho) w)) :=
    evalValues_embedding S positiveEmbed hom (liftedValuation rho) w
  exact (congrArg (evalValues S) mapped).trans value

theorem positive_word_equal (S : Semigroup (Fin 6))
    (hom : ∀ a b, S.mul (positiveEmbed a) (positiveEmbed b) = positiveEmbed (positive.mul a b))
    {u v : Word Nat} (h : SamePKey u v) (rho : Nat → Fin 6)
    (hu : ∀ x ∈ u.toList, 3 ≤ (rho x).val) (hv : ∀ x ∈ v.toList, 3 ≤ (rho x).val) :
    evalValues S (u.toList.map rho) = evalValues S (v.toList.map rho) := by
  have left := positive_word_value S hom rho u hu
  have right := positive_word_value S hom rho v hv
  have middle : some (positiveEmbed (positive.eval (liftedValuation rho) u)) =
      some (positiveEmbed (positive.eval (liftedValuation rho) v)) :=
    congrArg (fun a => some (positiveEmbed a)) (positive_eval_eq_of_key h (liftedValuation rho))
  exact left.trans (middle.trans right.symm)

theorem mapped_one_value (S : Semigroup α) (D : SplitAction S)
    (rho : Nat → α) (pre post : List Nat) (x : Nat)
    (hx : D.Low (rho x)) (hp : ∀ y ∈ pre, D.Pos (rho y)) :
    evalValues S ((pre ++ x :: post).map rho) = some (runTail S (rho x) (post.map rho)) := by
  have representation : (pre ++ x :: post).map rho = pre.map rho ++ rho x :: post.map rho := by
    rw [List.map_append, List.map_cons]
  have positioned : evalValues S (pre.map rho ++ rho x :: post.map rho) =
      some (runTail S (rho x) (post.map rho)) :=
    evalValues_one_low D (pre.map rho) (post.map rho) (rho x) hx (mapped_property rho pre D.Pos hp)
  exact (congrArg (evalValues S) representation).trans positioned

theorem mapped_many_value (S : Semigroup α) (D : SplitAction S)
    (rho : Nat → α) (pre mid post : List Nat) (x y : Nat)
    (hx : D.Low (rho x)) (hy : D.Low (rho y)) :
    evalValues S ((pre ++ x :: (mid ++ y :: post)).map rho) = some D.zero := by
  have representation : (pre ++ x :: (mid ++ y :: post)).map rho =
      pre.map rho ++ rho x :: (mid.map rho ++ rho y :: post.map rho) := by
    simp only [List.map_append, List.map_cons]
  have positioned : evalValues S (pre.map rho ++ rho x :: (mid.map rho ++ rho y :: post.map rho)) =
      some D.zero := evalValues_two_low D (pre.map rho) (mid.map rho) (post.map rho) (rho x) (rho y) hx hy
  exact (congrArg (evalValues S) representation).trans positioned

theorem mapped_continuation_equal (S : Semigroup (Fin 6))
    (hom : ∀ a b, S.mul (positiveEmbed a) (positiveEmbed b) = positiveEmbed (positive.mul a b))
    (rho : Nat → Fin 6) (xs ys : List Nat) (h : SameOptionalKey xs ys)
    (hx : ∀ x ∈ xs, 3 ≤ (rho x).val) (hy : ∀ x ∈ ys, 3 ≤ (rho x).val) (a : Fin 6) :
    runTail S a (xs.map rho) = runTail S a (ys.map rho) := by
  have left : xs.map rho = xs.map (fun x => positiveEmbed (liftedValuation rho x)) := map_positive_lift rho xs hx
  have right : ys.map rho = ys.map (fun x => positiveEmbed (liftedValuation rho x)) := map_positive_lift rho ys hy
  have middle : runTail S a (xs.map (fun x => positiveEmbed (liftedValuation rho x))) =
      runTail S a (ys.map (fun x => positiveEmbed (liftedValuation rho x))) :=
    optional_key_continuation S positiveEmbed hom xs ys h (liftedValuation rho) a
  exact (congrArg (runTail S a) left).trans (middle.trans (congrArg (runTail S a) right.symm))

end SemigroupBasis.CoRoots.Order6Day15.B16.Literal

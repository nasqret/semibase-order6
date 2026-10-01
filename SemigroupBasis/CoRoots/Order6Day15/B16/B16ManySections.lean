import SemigroupBasis.CoRoots.Order6Day15.B16.B16ObservationOne

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Literal

inductive PredicateSections (P : Nat → Prop) : List Nat → Prop
  | positive (xs) (h : ∀ x ∈ xs, P x) : PredicateSections P xs
  | one (pre post) (x) (hp : ∀ y ∈ pre, P y) (hx : ¬ P x)
      (hs : ∀ y ∈ post, P y) : PredicateSections P (pre ++ x :: post)
  | many (pre mid post) (x y) (hx : ¬ P x) (hy : ¬ P y) :
      PredicateSections P (pre ++ x :: (mid ++ y :: post))

theorem predicate_sections (P : Nat → Prop) (xs : List Nat) : PredicateSections P xs := by
  classical
  induction xs with
  | nil => exact .positive [] (fun _ h => False.elim (List.not_mem_nil h))
  | cons x xs ih =>
      cases ih with
      | positive ys hp =>
          by_cases hx : P x
          · apply PredicateSections.positive
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact hx
            · exact hp y hy
          · exact .one [] _ x (fun _ h => False.elim (List.not_mem_nil h)) hx hp
      | one pre post y hp hy hs =>
          by_cases hx : P x
          · have hpre : ∀ a ∈ x :: pre, P a := by
              intro a ha
              rcases List.mem_cons.mp ha with rfl | ha
              · exact hx
              · exact hp a ha
            exact .one (x :: pre) post y hpre hy hs
          · exact .many [] pre post x y hx hy
      | many pre mid post y z hy hz => exact .many (x :: pre) mid post y z hy hz

theorem predicate_cases (P : Nat → Prop) (xs : List Nat) :
    (∀ x ∈ xs, P x) ∨
    (∃ pre post x, xs = pre ++ x :: post ∧ (∀ y ∈ pre, P y) ∧ ¬ P x ∧ (∀ y ∈ post, P y)) ∨
    (∃ pre mid post x y, xs = pre ++ x :: (mid ++ y :: post) ∧ ¬ P x ∧ ¬ P y) := by
  cases predicate_sections P xs with
  | positive ys hp => exact Or.inl hp
  | one pre post x hp hx hs => exact Or.inr (Or.inl ⟨pre, post, x, rfl, hp, hx, hs⟩)
  | many pre mid post x y hx hy => exact Or.inr (Or.inr ⟨pre, mid, post, x, y, rfl, hx, hy⟩)

theorem not_single_twice (x : Nat) (pre mid post : List Nat) :
    ¬ Single x (pre ++ x :: (mid ++ x :: post)) := by
  intro h
  change (pre ++ x :: (mid ++ x :: post)).count x = 1 at h
  rw [List.count_append, List.count_cons_self, List.count_append, List.count_cons_self] at h
  omega

theorem two_marker_left_mem (x y : Nat) (pre mid post : List Nat) :
    x ∈ pre ++ x :: (mid ++ y :: post) :=
  List.mem_append.mpr (Or.inr (List.Mem.head _))

theorem two_marker_right_mem (x y : Nat) (pre mid post : List Nat) :
    y ∈ pre ++ x :: (mid ++ y :: post) :=
  List.mem_append.mpr (Or.inr (List.Mem.tail _ (List.mem_append.mpr (Or.inr (List.Mem.head _)))))

theorem two_marked_impossible (P : Nat → Prop) (pre mid post : List Nat) (x y a : Nat)
    (hx : ¬ P x) (hy : ¬ P y)
    (one : Single a (pre ++ x :: (mid ++ y :: post)))
    (other : ∀ z ∈ pre ++ x :: (mid ++ y :: post), z ≠ a → P z) : False := by
  classical
  have xa : x = a := by
    by_cases h : x = a
    · exact h
    · exact False.elim (hx (other x (two_marker_left_mem x y pre mid post) h))
  have ya : y = a := by
    by_cases h : y = a
    · exact h
    · exact False.elim (hy (other y (two_marker_right_mem x y pre mid post) h))
  subst x
  subst y
  exact not_single_twice a pre mid post one

theorem many_marked_transfer {xs ys : List Nat} (h : SameOccurrences xs ys)
    (P : Nat → Prop) (pre mid post : List Nat) (x y : Nat)
    (eq : xs = pre ++ x :: (mid ++ y :: post)) (hx : ¬ P x) (hy : ¬ P y) :
    ∃ pre' mid' post' x' y', ys = pre' ++ x' :: (mid' ++ y' :: post') ∧ ¬ P x' ∧ ¬ P y' := by
  rcases predicate_cases P ys with hp | ⟨left, right, a, eq', hl, ha, hr⟩ | many
  · have allSource : ∀ z ∈ xs, P z := positive_transfer (sameOccurrences_symm h) P hp
    have member : x ∈ xs := eq ▸ two_marker_left_mem x y pre mid post
    exact False.elim (hx (allSource x member))
  · have singleTarget : Single a ys := eq' ▸ one_marked_single P a left right ha hl hr
    have singleSource : Single a xs := (h.2 a).mpr singleTarget
    have positioned : Single a (pre ++ x :: (mid ++ y :: post)) := eq ▸ singleSource
    have other : ∀ z ∈ pre ++ x :: (mid ++ y :: post), z ≠ a → P z := by
      intro z hz ne
      have source : z ∈ xs := eq ▸ hz
      have target : z ∈ ys := (h.1 z).mp source
      have targetPosition : z ∈ left ++ a :: right := eq' ▸ target
      exact one_marked_other P a left right hl hr z targetPosition ne
    exact False.elim (two_marked_impossible P pre mid post x y a hx hy positioned other)
  · exact many

theorem observation_many {u v : Word Nat} (h : SameObservation u v)
    (P : Nat → Prop) (pre mid post : List Nat) (x y : Nat)
    (eq : u.toList = pre ++ x :: (mid ++ y :: post)) (hx : ¬ P x) (hy : ¬ P y) :
    ∃ pre' mid' post' x' y', v.toList = pre' ++ x' :: (mid' ++ y' :: post') ∧ ¬ P x' ∧ ¬ P y' :=
  many_marked_transfer (sameObservation_occurrences h) P pre mid post x y eq hx hy

end SemigroupBasis.CoRoots.Order6Day15.B16.Literal

import SemigroupBasis.CoRoots.Order6Day15.B16.B16Occurrences

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Literal

theorem sameOptionalKey_symm {xs ys : List Nat} (h : SameOptionalKey xs ys) :
    SameOptionalKey ys xs := by
  apply (positiveList_key_iff ys xs).mp
  intro rho
  exact ((positiveList_key_iff xs ys).mpr h rho).symm

/-- Global PKey, simple-letter domain, then suffix-LOCAL optional PKeys. -/
def SameObservation (u v : Word Nat) : Prop :=
  SamePKey u v ∧
  (∀ x, Single x u.toList ↔ Single x v.toList) ∧
  (∀ x, Single x u.toList →
    SameOptionalKey (afterLetter x u.toList) (afterLetter x v.toList))

theorem sameObservation_occurrences {u v : Word Nat} (h : SameObservation u v) :
    SameOccurrences u.toList v.toList := ⟨h.1.1, h.2.1⟩

theorem sameObservation_symm {u v : Word Nat} (h : SameObservation u v) :
    SameObservation v u := by
  refine ⟨samePKey_symm h.1, (fun x => (h.2.1 x).symm), ?_⟩
  intro x hx
  exact sameOptionalKey_symm (h.2.2 x ((h.2.1 x).mpr hx))

theorem observation_positive {u v : Word Nat} (h : SameObservation u v)
    (P : Nat → Prop) (hp : ∀ x ∈ u.toList, P x) : ∀ x ∈ v.toList, P x :=
  positive_transfer (sameObservation_occurrences h) P hp

theorem observation_one {u v : Word Nat} (h : SameObservation u v)
    (P : Nat → Prop) (x : Nat) (pre post : List Nat)
    (eq : u.toList = pre ++ x :: post) (hn : ¬ P x)
    (hp : ∀ y ∈ pre, P y) (hs : ∀ y ∈ post, P y) :
    ∃ pre' post', v.toList = pre' ++ x :: post' ∧
      (∀ y ∈ pre', P y) ∧ (∀ y ∈ post', P y) ∧ SameOptionalKey post post' := by
  rcases one_marked_transfer (sameObservation_occurrences h) P x pre post eq hn hp hs with
    ⟨pre', post', target, left, right, tailEq⟩
  have one : Single x u.toList := eq ▸ one_marked_single P x pre post hn hp hs
  have sourceTail : afterLetter x u.toList = post :=
    (congrArg (afterLetter x) eq).trans
      (afterLetter_prefix x pre post (marker_absent P x pre hn hp))
  have keys : SameOptionalKey (afterLetter x u.toList) (afterLetter x v.toList) := h.2.2 x one
  have actual : SameOptionalKey post post' := by
    rw [sourceTail, ← tailEq] at keys
    exact keys
  exact ⟨pre', post', target, left, right, actual⟩

theorem optional_key_continuation (S : Semigroup α) (embed : Fin 3 → α)
    (hom : ∀ a b, S.mul (embed a) (embed b) = embed (positive.mul a b))
    (xs ys : List Nat) (h : SameOptionalKey xs ys) (rho : Nat → Fin 3) (a : α) :
    runTail S a (xs.map (fun x => embed (rho x))) =
      runTail S a (ys.map (fun x => embed (rho x))) := by
  cases xs with
  | nil =>
      cases ys with
      | nil => rfl
      | cons b ys => exact False.elim h
  | cons b xs =>
      cases ys with
      | nil => exact False.elim h
      | cons c ys =>
          have key : SamePKey (Word.mk b xs) (Word.mk c ys) := h
          exact samePKey_continuation S embed hom key rho a

theorem one_section_action (S : Semigroup α) (D : SplitAction S)
    (embed : Fin 3 → α)
    (hom : ∀ a b, S.mul (embed a) (embed b) = embed (positive.mul a b))
    (pre pre' : List α) (xs ys : List Nat) (a : α)
    (ha : D.Low a) (hp : ∀ y ∈ pre, D.Pos y) (hp' : ∀ y ∈ pre', D.Pos y)
    (h : SameOptionalKey xs ys) (rho : Nat → Fin 3) :
    evalValues S (pre ++ a :: xs.map (fun x => embed (rho x))) =
      evalValues S (pre' ++ a :: ys.map (fun x => embed (rho x))) := by
  have left : evalValues S (pre ++ a :: xs.map (fun x => embed (rho x))) =
      some (runTail S a (xs.map (fun x => embed (rho x)))) :=
    evalValues_one_low D pre _ a ha hp
  have right : evalValues S (pre' ++ a :: ys.map (fun x => embed (rho x))) =
      some (runTail S a (ys.map (fun x => embed (rho x)))) :=
    evalValues_one_low D pre' _ a ha hp'
  have actions : runTail S a (xs.map (fun x => embed (rho x))) =
      runTail S a (ys.map (fun x => embed (rho x))) :=
    optional_key_continuation S embed hom xs ys h rho a
  exact left.trans ((congrArg some actions).trans right.symm)

theorem one_section_action6432 (pre pre' : List (Fin 6)) (xs ys : List Nat) (a : Fin 6)
    (ha : a.val < 3) (hp : ∀ y ∈ pre, 3 ≤ y.val) (hp' : ∀ y ∈ pre', 3 ≤ y.val)
    (h : SameOptionalKey xs ys) (rho : Nat → Fin 3) :
    evalValues s6432 (pre ++ a :: xs.map (fun x => positiveEmbed (rho x))) =
      evalValues s6432 (pre' ++ a :: ys.map (fun x => positiveEmbed (rho x))) :=
  one_section_action s6432 split6432 positiveEmbed positiveEmbed_hom6432 pre pre' xs ys a ha hp hp' h rho

theorem one_section_action6439 (pre pre' : List (Fin 6)) (xs ys : List Nat) (a : Fin 6)
    (ha : a.val < 3) (hp : ∀ y ∈ pre, 3 ≤ y.val) (hp' : ∀ y ∈ pre', 3 ≤ y.val)
    (h : SameOptionalKey xs ys) (rho : Nat → Fin 3) :
    evalValues s6439 (pre ++ a :: xs.map (fun x => positiveEmbed (rho x))) =
      evalValues s6439 (pre' ++ a :: ys.map (fun x => positiveEmbed (rho x))) :=
  one_section_action s6439 split6439 positiveEmbed positiveEmbed_hom6439 pre pre' xs ys a ha hp hp' h rho

end SemigroupBasis.CoRoots.Order6Day15.B16.Literal

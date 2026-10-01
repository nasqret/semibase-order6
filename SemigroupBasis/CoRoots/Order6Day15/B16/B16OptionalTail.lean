import SemigroupBasis.CoRoots.Order6Day15.B16.B16LiteralActions

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Literal

def positiveList (rho : Nat → Fin 3) : List Nat → Option (Fin 3)
  | [] => none
  | a :: xs => some (positive.eval rho ⟨a, xs⟩)

/-- Extend exactly O1's key to empty continuations, without an empty word. -/
def SameOptionalKey : List Nat → List Nat → Prop
  | [], [] => True
  | a :: xs, b :: ys => SamePKey ⟨a, xs⟩ ⟨b, ys⟩
  | _, _ => False

theorem positiveList_key_iff (xs ys : List Nat) :
    (∀ rho : Nat → Fin 3, positiveList rho xs = positiveList rho ys) ↔ SameOptionalKey xs ys := by
  cases xs with
  | nil =>
      cases ys with
      | nil =>
          change (∀ _rho : Nat → Fin 3, (none : Option (Fin 3)) = none) ↔ True
          exact ⟨fun _ => True.intro, fun _ _ => rfl⟩
      | cons b bs =>
          change (∀ rho : Nat → Fin 3, none = some (positive.eval rho ⟨b, bs⟩)) ↔ False
          constructor
          · intro h
            have bad : (none : Option (Fin 3)) = some (positive.eval (fun _ => 0) ⟨b, bs⟩) := h _
            cases bad
          · intro h
            exact False.elim h
  | cons a xs =>
      cases ys with
      | nil =>
          change (∀ rho : Nat → Fin 3, some (positive.eval rho ⟨a, xs⟩) = none) ↔ False
          constructor
          · intro h
            have bad : some (positive.eval (fun _ => 0) ⟨a, xs⟩) = (none : Option (Fin 3)) := h _
            cases bad
          · intro h
            exact False.elim h
      | cons b ys =>
          change (∀ rho : Nat → Fin 3,
            some (positive.eval rho ⟨a, xs⟩) = some (positive.eval rho ⟨b, ys⟩)) ↔
              SamePKey ⟨a, xs⟩ ⟨b, ys⟩
          constructor
          · intro h
            exact (positive_valid_iff_key ⟨a, xs⟩ ⟨b, ys⟩).mp (fun rho => Option.some.inj (h rho))
          · intro h rho
            exact congrArg some (positive_eval_eq_of_key h rho)

theorem positiveList_action6432 (rho : Nat → Fin 3) (i : Fin 2) (xs : List Nat) :
    runTail s6432 (idealEmbed i) (xs.map (fun x => positiveEmbed (rho x))) =
      optionalAction s6432 (positiveList rho xs) i := by
  cases xs with
  | nil => exact (optionalAction_empty s6432 i).symm
  | cons a xs =>
      have tail : runTail s6432 (idealEmbed i)
          ((Word.mk a xs).toList.map (fun x => positiveEmbed (rho x))) =
          s6432.mul (idealEmbed i) (positiveEmbed (positive.eval rho ⟨a, xs⟩)) :=
        positive_tail_action s6432 positiveEmbed positiveEmbed_hom6432 rho (idealEmbed i) ⟨a, xs⟩
      have action : optionalAction s6432 (some (positive.eval rho ⟨a, xs⟩)) i =
          s6432.mul (idealEmbed i) (positiveEmbed (positive.eval rho ⟨a, xs⟩)) :=
        optionalAction_some6432 (positive.eval rho ⟨a, xs⟩) i
      exact tail.trans action.symm

theorem positiveList_action6439 (rho : Nat → Fin 3) (i : Fin 2) (xs : List Nat) :
    runTail s6439 (idealEmbed i) (xs.map (fun x => positiveEmbed (rho x))) =
      optionalAction s6439 (positiveList rho xs) i := by
  cases xs with
  | nil => exact (optionalAction_empty s6439 i).symm
  | cons a xs =>
      have tail : runTail s6439 (idealEmbed i)
          ((Word.mk a xs).toList.map (fun x => positiveEmbed (rho x))) =
          s6439.mul (idealEmbed i) (positiveEmbed (positive.eval rho ⟨a, xs⟩)) :=
        positive_tail_action s6439 positiveEmbed positiveEmbed_hom6439 rho (idealEmbed i) ⟨a, xs⟩
      have action : optionalAction s6439 (some (positive.eval rho ⟨a, xs⟩)) i =
          s6439.mul (idealEmbed i) (positiveEmbed (positive.eval rho ⟨a, xs⟩)) :=
        optionalAction_some6439 (positive.eval rho ⟨a, xs⟩) i
      exact tail.trans action.symm

theorem all_actions_key_iff (S : Semigroup (Fin 6))
    (bridge : ∀ (rho : Nat → Fin 3) (i : Fin 2) (xs : List Nat),
      runTail S (idealEmbed i) (xs.map (fun x => positiveEmbed (rho x))) =
        optionalAction S (positiveList rho xs) i)
    (faithful : ∀ p q : Option (Fin 3),
      (∀ i : Fin 2, optionalAction S p i = optionalAction S q i) → p = q)
    (xs ys : List Nat) :
    (∀ (rho : Nat → Fin 3) (i : Fin 2),
      runTail S (idealEmbed i) (xs.map (fun x => positiveEmbed (rho x))) =
        runTail S (idealEmbed i) (ys.map (fun x => positiveEmbed (rho x)))) ↔
      SameOptionalKey xs ys := by
  constructor
  · intro h
    apply (positiveList_key_iff xs ys).mp
    intro rho
    apply faithful
    intro i
    exact (bridge rho i xs).symm.trans ((h rho i).trans (bridge rho i ys))
  · intro h rho i
    have values : positiveList rho xs = positiveList rho ys := (positiveList_key_iff xs ys).mpr h rho
    calc
      runTail S (idealEmbed i) (xs.map (fun x => positiveEmbed (rho x))) =
          optionalAction S (positiveList rho xs) i := bridge rho i xs
      _ = optionalAction S (positiveList rho ys) i := congrArg (fun p => optionalAction S p i) values
      _ = runTail S (idealEmbed i) (ys.map (fun x => positiveEmbed (rho x))) := (bridge rho i ys).symm

theorem tailAction_iff_key6432 (xs ys : List Nat) :
    (∀ (rho : Nat → Fin 3) (i : Fin 2),
      runTail s6432 (idealEmbed i) (xs.map (fun x => positiveEmbed (rho x))) =
        runTail s6432 (idealEmbed i) (ys.map (fun x => positiveEmbed (rho x)))) ↔
      SameOptionalKey xs ys :=
  all_actions_key_iff s6432 positiveList_action6432 optionalAction_faithful6432 xs ys

theorem tailAction_iff_key6439 (xs ys : List Nat) :
    (∀ (rho : Nat → Fin 3) (i : Fin 2),
      runTail s6439 (idealEmbed i) (xs.map (fun x => positiveEmbed (rho x))) =
        runTail s6439 (idealEmbed i) (ys.map (fun x => positiveEmbed (rho x)))) ↔
      SameOptionalKey xs ys :=
  all_actions_key_iff s6439 positiveList_action6439 optionalAction_faithful6439 xs ys

end SemigroupBasis.CoRoots.Order6Day15.B16.Literal

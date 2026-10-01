import SemigroupBasis.CoRoots.Order6Day15.B16.B16OptionalTail

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Literal

/-- The suffix after the first occurrence; absence is handled separately. -/
def afterLetter (x : Nat) : List Nat → List Nat
  | [] => []
  | a :: xs => if a = x then xs else afterLetter x xs

def Single (x : Nat) (xs : List Nat) : Prop := xs.count x = 1

theorem afterLetter_prefix (x : Nat) (pre post : List Nat) (hp : x ∉ pre) :
    afterLetter x (pre ++ x :: post) = post := by
  induction pre with
  | nil =>
      change (if x = x then post else afterLetter x post) = post
      rw [if_pos rfl]
  | cons a pre ih =>
      have ha : a ≠ x := fun h => hp (List.mem_cons.mpr (Or.inl h.symm))
      have ht : x ∉ pre := fun h => hp (List.Mem.tail _ h)
      change (if a = x then pre ++ x :: post else afterLetter x (pre ++ x :: post)) = post
      rw [if_neg ha]
      exact ih ht

theorem single_split (x : Nat) (xs : List Nat) (h : Single x xs) :
    ∃ pre post, xs = pre ++ x :: post ∧ x ∉ pre ∧ x ∉ post := by
  change xs.count x = 1 at h
  induction xs with
  | nil =>
      change 0 = 1 at h
      exact False.elim ((by decide : (0 : Nat) ≠ 1) h)
  | cons a xs ih =>
      by_cases ha : a = x
      · subst a
        rw [List.count_cons_self] at h
        have hz : xs.count x = 0 :=
          Nat.add_right_cancel (show xs.count x + 1 = 0 + 1 from h)
        exact ⟨[], xs, rfl, List.not_mem_nil, List.count_eq_zero.mp hz⟩
      · have ht : xs.count x = 1 := (List.count_cons_of_ne ha).symm.trans h
        rcases ih ht with ⟨pre, post, eq, hp, hs⟩
        refine ⟨a :: pre, post, congrArg (List.cons a) eq, ?_, hs⟩
        intro hm
        rcases List.mem_cons.mp hm with hx | hx
        · exact ha hx.symm
        · exact hp hx

theorem single_of_split (x : Nat) (pre post : List Nat)
    (hp : x ∉ pre) (hs : x ∉ post) : Single x (pre ++ x :: post) := by
  change (pre ++ x :: post).count x = 1
  rw [List.count_append, List.count_cons_self,
    List.count_eq_zero_of_not_mem hp, List.count_eq_zero_of_not_mem hs]

theorem single_mem (x : Nat) (xs : List Nat) (h : Single x xs) : x ∈ xs := by
  rcases single_split x xs h with ⟨pre, post, eq, _, _⟩
  rw [eq]
  exact List.mem_append.mpr (Or.inr (List.Mem.head _))

theorem single_canonical_split (x : Nat) (xs : List Nat) (h : Single x xs) :
    ∃ pre, xs = pre ++ x :: afterLetter x xs ∧ x ∉ pre ∧ x ∉ afterLetter x xs := by
  rcases single_split x xs h with ⟨pre, post, eq, hp, hs⟩
  have tailEq : afterLetter x xs = post :=
    (congrArg (afterLetter x) eq).trans (afterLetter_prefix x pre post hp)
  rw [tailEq]
  exact ⟨pre, eq, hp, hs⟩

/-- Support plus the globally simple-letter set; no suffix coordinate here. -/
def SameOccurrences (xs ys : List Nat) : Prop :=
  (∀ x, x ∈ xs ↔ x ∈ ys) ∧ (∀ x, Single x xs ↔ Single x ys)

theorem sameOccurrences_symm {xs ys : List Nat} (h : SameOccurrences xs ys) :
    SameOccurrences ys xs := ⟨fun x => (h.1 x).symm, fun x => (h.2 x).symm⟩

theorem positive_transfer {xs ys : List Nat} (h : SameOccurrences xs ys)
    (P : Nat → Prop) (hp : ∀ x ∈ xs, P x) : ∀ x ∈ ys, P x := by
  intro x hx
  exact hp x ((h.1 x).mpr hx)

theorem marker_absent (P : Nat → Prop) (x : Nat) (xs : List Nat)
    (hn : ¬ P x) (hp : ∀ y ∈ xs, P y) : x ∉ xs := fun h => hn (hp x h)

theorem one_marked_single (P : Nat → Prop) (x : Nat) (pre post : List Nat)
    (hn : ¬ P x) (hp : ∀ y ∈ pre, P y) (hs : ∀ y ∈ post, P y) :
    Single x (pre ++ x :: post) :=
  single_of_split x pre post (marker_absent P x pre hn hp) (marker_absent P x post hn hs)

theorem one_marked_other (P : Nat → Prop) (x : Nat) (pre post : List Nat)
    (hp : ∀ y ∈ pre, P y) (hs : ∀ y ∈ post, P y) :
    ∀ y ∈ pre ++ x :: post, y ≠ x → P y := by
  intro y hy hn
  rcases List.mem_append.mp hy with hy | hy
  · exact hp y hy
  · rcases List.mem_cons.mp hy with hy | hy
    · exact False.elim (hn hy)
    · exact hs y hy

theorem one_marked_transfer {xs ys : List Nat} (h : SameOccurrences xs ys)
    (P : Nat → Prop) (x : Nat) (pre post : List Nat)
    (eq : xs = pre ++ x :: post) (hn : ¬ P x)
    (hp : ∀ y ∈ pre, P y) (hs : ∀ y ∈ post, P y) :
    ∃ pre' post', ys = pre' ++ x :: post' ∧
      (∀ y ∈ pre', P y) ∧ (∀ y ∈ post', P y) ∧ post' = afterLetter x ys := by
  have one : Single x xs := eq ▸ one_marked_single P x pre post hn hp hs
  have target : Single x ys := (h.2 x).mp one
  rcases single_split x ys target with ⟨pre', post', eq', hp', hs'⟩
  have other : ∀ y ∈ ys, y ≠ x → P y := by
    intro y hy ne
    have source : y ∈ xs := (h.1 y).mpr hy
    have positioned : y ∈ pre ++ x :: post := eq ▸ source
    exact one_marked_other P x pre post hp hs y positioned ne
  have left : ∀ y ∈ pre', P y := by
    intro y hy
    have member : y ∈ ys := eq' ▸ (List.mem_append.mpr (Or.inl hy))
    have ne : y ≠ x := fun e => hp' (e ▸ hy)
    exact other y member ne
  have right : ∀ y ∈ post', P y := by
    intro y hy
    have member : y ∈ ys := eq' ▸ (List.mem_append.mpr (Or.inr (List.Mem.tail _ hy)))
    have ne : y ≠ x := fun e => hs' (e ▸ hy)
    exact other y member ne
  have tailEq : afterLetter x ys = post' :=
    (congrArg (afterLetter x) eq').trans (afterLetter_prefix x pre' post' hp')
  exact ⟨pre', post', eq', left, right, tailEq.symm⟩

end SemigroupBasis.CoRoots.Order6Day15.B16.Literal

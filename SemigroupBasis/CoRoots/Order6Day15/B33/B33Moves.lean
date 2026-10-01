import SemigroupBasis.CoRoots.Order6Sunday.Msg0513B33FiveSlotCountermodel

namespace SemigroupBasis.CoRoots.Order6Day15.B33

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Sunday.Msg0513B33FiveSlotCountermodel.basis

/-- List presentation of semigroup derivability, with only the reflexive empty case. -/
def Rel : List Nat → List Nat → Prop
  | [], [] => True
  | a :: u, b :: v => Derives basis ⟨a, u⟩ ⟨b, v⟩
  | _, _ => False

namespace Rel

theorem refl (u : List Nat) : Rel u u := by
  cases u with
  | nil => trivial
  | cons a u => exact Derives.refl ⟨a, u⟩

theorem symm {u v : List Nat} (h : Rel u v) : Rel v u := by
  cases u <;> cases v
  · trivial
  · exact False.elim h
  · exact False.elim h
  · exact Derives.symm h

theorem trans {u v w : List Nat} (h : Rel u v) (k : Rel v w) : Rel u w := by
  cases u <;> cases v <;> cases w
  all_goals first | trivial | exact False.elim h | exact False.elim k | exact Derives.trans h k

theorem prepend {u v : List Nat} (h : Rel u v) (p : List Nat) :
    Rel (p ++ u) (p ++ v) := by
  cases p with
  | nil => exact h
  | cons a p =>
    cases u <;> cases v
    · exact refl _
    · exact False.elim h
    · exact False.elim h
    · exact Derives.prepend ⟨a, p⟩ h

theorem suffix {u v : List Nat} (h : Rel u v) (q : List Nat) :
    Rel (u ++ q) (v ++ q) := by
  cases q with
  | nil => simpa only [List.append_nil] using h
  | cons b q =>
    cases u <;> cases v
    · exact refl _
    · exact False.elim h
    · exact False.elim h
    · exact Derives.appendRight h ⟨b, q⟩

theorem context {u v : List Nat} (h : Rel u v) (p q : List Nat) :
    Rel (p ++ u ++ q) (p ++ v ++ q) := by
  simpa only [List.append_assoc] using (h.prepend p).suffix q

theorem ofDerives {u v : Word Nat} (h : Derives basis u v) :
    Rel u.toList v.toList := by
  cases u; cases v; exact h

theorem toDerives {u v : Word Nat} (h : Rel u.toList v.toList) :
    Derives basis u v := by
  cases u; cases v; exact h

end Rel

private theorem law01 :
    Derives basis (⟨0, [0]⟩ : Word Nat) ⟨0, [0, 0, 0]⟩ :=
  Derives.fromBasis (e := ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩) (by decide)

private theorem law02 :
    Derives basis (⟨0, [1, 0]⟩ : Word Nat) ⟨0, [0, 1, 1, 1]⟩ :=
  Derives.fromBasis (e := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1, 1]⟩⟩) (by decide)

private theorem law03 :
    Derives basis (⟨0, [1, 2]⟩ : Word Nat) ⟨0, [1, 1, 1, 2]⟩ :=
  Derives.fromBasis (e := ⟨⟨0, [1, 2]⟩, ⟨0, [1, 1, 1, 2]⟩⟩) (by decide)

private theorem law26 :
    Derives basis (⟨0, [0, 1, 2, 2]⟩ : Word Nat) ⟨0, [1, 2, 2, 0]⟩ :=
  Derives.fromBasis (e := ⟨⟨0, [0, 1, 2, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩) (by decide)

theorem square_four (x : Word Nat) :
    Rel (x.toList ++ x.toList)
      (x.toList ++ x.toList ++ x.toList ++ x.toList) := by
  have h : Derives basis (x ++ x) (((x ++ x) ++ x) ++ x) :=
    Derives.subst law01 (fun _ => x)
  simpa only [Word.toList_append, List.append_assoc] using Rel.ofDerives h

theorem sandwich (x y : Word Nat) :
    Rel (x.toList ++ y.toList ++ x.toList)
      (x.toList ++ x.toList ++ y.toList ++ y.toList ++ y.toList) := by
  have h : Derives basis ((x ++ y) ++ x) ((((x ++ x) ++ y) ++ y) ++ y) :=
    Derives.subst law02 (fun n => if n = 0 then x else y)
  simpa only [Word.toList_append, List.append_assoc] using Rel.ofDerives h

theorem thickenBetween (x y z : Word Nat) :
    Rel (x.toList ++ y.toList ++ z.toList)
      (x.toList ++ y.toList ++ y.toList ++ y.toList ++ z.toList) := by
  have h : Derives basis ((x ++ y) ++ z) ((((x ++ y) ++ y) ++ y) ++ z) :=
    Derives.subst law03 (fun n => if n = 0 then x else if n = 1 then y else z)
  simpa only [Word.toList_append, List.append_assoc] using Rel.ofDerives h

theorem gatherSquare (x y z : Word Nat) :
    Rel (x.toList ++ y.toList ++ z.toList ++ z.toList ++ x.toList)
      (x.toList ++ x.toList ++ y.toList ++ z.toList ++ z.toList) := by
  have h : Derives basis ((((x ++ x) ++ y) ++ z) ++ z)
      ((((x ++ y) ++ z) ++ z) ++ x) :=
    Derives.subst law26 (fun n => if n = 0 then x else if n = 1 then y else z)
  simpa only [Word.toList_append, List.append_assoc] using Rel.ofDerives (Derives.symm h)

/-- The empty-middle case is proved separately, never by an empty substitution. -/
theorem gatherEmpty (x z : Word Nat) :
    Rel (x.toList ++ z.toList ++ z.toList ++ x.toList)
      (x.toList ++ x.toList ++ z.toList ++ z.toList) := by
  have h1 : Rel (x.toList ++ z.toList ++ z.toList ++ x.toList)
      (x.toList ++ x.toList ++ z.toList ++ z.toList ++ z.toList ++
        z.toList ++ z.toList ++ z.toList) := by
    simpa only [Word.toList_append, List.append_assoc] using sandwich x (z ++ z)
  have h2 : Rel
      (x.toList ++ x.toList ++ z.toList ++ z.toList ++ z.toList ++
        z.toList ++ z.toList ++ z.toList)
      (x.toList ++ x.toList ++ z.toList ++ z.toList ++ z.toList ++ z.toList) := by
    simpa only [List.append_assoc] using
      (square_four z).symm.context (x.toList ++ x.toList) (z.toList ++ z.toList)
  have h3 : Rel
      (x.toList ++ x.toList ++ z.toList ++ z.toList ++ z.toList ++ z.toList)
      (x.toList ++ x.toList ++ z.toList ++ z.toList) := by
    simpa only [List.append_assoc] using (square_four z).symm.prepend (x.toList ++ x.toList)
  exact h1.trans (h2.trans h3)

theorem gather_square (a b : Nat) (m : List Nat) :
    Rel ([a] ++ m ++ [b, b, a]) ([a, a] ++ m ++ [b, b]) := by
  cases m with
  | nil =>
    simpa only [Word.toList_singleton, List.append_nil, List.cons_append,
      List.nil_append] using gatherEmpty (Word.singleton a) (Word.singleton b)
  | cons c cs =>
    simpa only [Word.toList, Word.singleton, List.cons_append, List.nil_append,
      List.append_assoc] using gatherSquare (Word.singleton a) ⟨c, cs⟩ (Word.singleton b)

theorem gather_cube (a b : Nat) (m : List Nat) :
    Rel ([a] ++ m ++ [b, b, b, a]) ([a, a] ++ m ++ [b, b, b]) := by
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    gather_square a b (m ++ [b])

theorem gather_single (a b : Nat) (m : List Nat) :
    Rel ([a] ++ m ++ [b, a]) ([a, a] ++ m ++ [b, b, b]) := by
  have expand : Rel ([a] ++ m ++ [b, a]) ([a] ++ m ++ [b, b, b, a]) := by
    simpa only [Word.toList, Word.singleton, List.cons_append, List.nil_append,
      List.append_assoc] using thickenBetween (⟨a, m⟩ : Word Nat)
        (Word.singleton b) (Word.singleton a)
  exact expand.trans (gather_cube a b m)

theorem thin_internal (p q : List Nat) (a : Nat) (hp : p ≠ []) (hq : q ≠ []) :
    Rel (p ++ [a, a, a] ++ q) (p ++ [a] ++ q) := by
  cases p with
  | nil => exact False.elim (hp rfl)
  | cons x xs =>
    cases q with
    | nil => exact False.elim (hq rfl)
    | cons y ys =>
      simpa only [Word.toList, Word.singleton, List.cons_append, List.nil_append,
        List.append_assoc] using
        (thickenBetween (⟨x, xs⟩ : Word Nat) (Word.singleton a) ⟨y, ys⟩).symm

theorem four_two (a : Nat) (p q : List Nat) :
    Rel (p ++ [a, a, a, a] ++ q) (p ++ [a, a] ++ q) := by
  simpa only [Word.toList_singleton, List.cons_append, List.nil_append] using
    (square_four (Word.singleton a)).symm.context p q

end SemigroupBasis.CoRoots.Order6Day15.B33

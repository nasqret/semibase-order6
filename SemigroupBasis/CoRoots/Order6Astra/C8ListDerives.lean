import SemigroupBasis.CoRoots.Order6Astra.C8TailCuts
import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedPresentation

namespace SemigroupBasis.CoRoots.Order6Astra.C8ListDerives

open Order6SporadicSection19.Published C8TailCuts
open Order6SporadicSection19.Published.SemanticSimpleAdjacency

/-- Empty lists are contexts only. This relation never supplies an empty
semigroup substitution: its nonempty case is the original `Derives`. -/
def Rel : List Nat → List Nat → Prop
  | [], [] => True
  | x :: xs, y :: ys => Derives basis (Word.mk x xs) (Word.mk y ys)
  | _, _ => False

theorem refl (xs : List Nat) : Rel xs xs := by
  cases xs with
  | nil => trivial
  | cons x xs => exact Derives.refl _

theorem of_words {u v : Word Nat} (h : Derives basis u v) : Rel u.toList v.toList := h

theorem to_words {u v : Word Nat} (h : Rel u.toList v.toList) : Derives basis u v := h

theorem symm {xs ys : List Nat} (h : Rel xs ys) : Rel ys xs := by
  cases xs <;> cases ys
  · trivial
  · exact False.elim h
  · exact False.elim h
  · exact Derives.symm h

theorem trans {xs ys zs : List Nat} (h : Rel xs ys) (k : Rel ys zs) : Rel xs zs := by
  cases xs <;> cases ys <;> cases zs
  · trivial
  · exact False.elim k
  · exact False.elim h
  · exact False.elim h
  · exact False.elim h
  · exact False.elim h
  · exact False.elim k
  · exact Derives.trans h k

theorem append {a b c d : List Nat} (h : Rel a b) (k : Rel c d) :
    Rel (a ++ c) (b ++ d) := by
  cases a with
  | nil =>
    cases b with
    | nil => exact k
    | cons y ys => exact False.elim h
  | cons x xs =>
    cases b with
    | nil => exact False.elim h
    | cons y ys =>
      cases c with
      | nil =>
        cases d with
        | nil => simpa only [List.append_nil] using h
        | cons z zs => exact False.elim k
      | cons z zs =>
        cases d with
        | nil => exact False.elim k
        | cons t ts =>
          exact (Derives.appendRight h (Word.mk z zs)).trans
            (Derives.prepend (Word.mk y ys) k)

theorem frame {a b : List Nat} (h : Rel a b) (left right : List Nat) :
    Rel (left ++ a ++ right) (left ++ b ++ right) :=
  append (append (refl left) h) (refl right)

inductive Aligned {α β : Type} (relation : α → β → Prop) : List α → List β → Prop
  | nil : Aligned relation [] []
  | cons {x xs y ys} : relation x y → Aligned relation xs ys →
      Aligned relation (x :: xs) (y :: ys)

theorem flatten {left right : List (List Nat)}
    (related : Aligned Rel left right) : Rel left.flatten right.flatten := by
  induction related with
  | nil => trivial
  | cons h _ ih => exact append h ih

theorem support {xs ys : List Nat} (h : Rel xs ys) : SameSupport xs ys := by
  cases xs with
  | nil =>
    cases ys with
    | nil => intro x; exact Iff.rfl
    | cons y ys => exact False.elim h
  | cons x xs =>
    cases ys with
    | nil => exact False.elim h
    | cons y ys =>
      exact semantic_support (Word.mk x xs) (Word.mk y ys)
        (fun valuation => Derives.sound models h valuation)

theorem simple {xs ys : List Nat} (h : Rel xs ys) (t : Nat) :
    xs.count t = 1 ↔ ys.count t = 1 := by
  cases xs with
  | nil =>
    cases ys with
    | nil => exact Iff.rfl
    | cons y ys => exact False.elim h
  | cons x xs =>
    cases ys with
    | nil => exact False.elim h
    | cons y ys =>
      exact (semantic_occurrence_categories (Word.mk x xs) (Word.mk y ys)
        (fun valuation => Derives.sound models h valuation) t).2.1

theorem empty_iff {xs ys : List Nat} (h : Rel xs ys) : xs = [] ↔ ys = [] := by
  cases xs <;> cases ys
  · exact Iff.rfl
  · exact False.elim h
  · exact False.elim h
  · simp

end SemigroupBasis.CoRoots.Order6Astra.C8ListDerives

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8ListDerives.append
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8ListDerives.flatten
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8ListDerives.support

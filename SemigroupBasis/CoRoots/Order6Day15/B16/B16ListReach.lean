import SemigroupBasis.CoRoots.Order6Day15.B16.B16SquareCertificates

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

open SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

/-- Empty lists relate only to empty lists; nonempty cases are real Derives. -/
def Rel : List Nat → List Nat → Prop
  | [], [] => True
  | a :: as, b :: bs => Derives basis (Word.mk a as) (Word.mk b bs)
  | _, _ => False

namespace Rel

theorem refl (xs : List Nat) : Rel xs xs := by
  cases xs with
  | nil => exact True.intro
  | cons a as => exact Derives.refl (Word.mk a as)

theorem symm {xs ys : List Nat} (h : Rel xs ys) : Rel ys xs := by
  cases xs <;> cases ys
  · exact True.intro
  · exact False.elim h
  · exact False.elim h
  · exact Derives.symm h

theorem trans {xs ys zs : List Nat} (h : Rel xs ys) (k : Rel ys zs) : Rel xs zs := by
  cases xs <;> cases ys <;> cases zs
  · exact True.intro
  · exact False.elim k
  · exact False.elim h
  · exact False.elim h
  · exact False.elim h
  · exact False.elim h
  · exact False.elim k
  · exact Derives.trans h k

theorem ofDerives {u v : Word Nat} (h : Derives basis u v) : Rel u.toList v.toList := by
  cases u; cases v; exact h

theorem toDerives {u v : Word Nat} (h : Rel u.toList v.toList) : Derives basis u v := by
  cases u; cases v; exact h

theorem cons (a : Nat) {xs ys : List Nat} (h : Rel xs ys) : Rel (a :: xs) (a :: ys) := by
  cases xs with
  | nil =>
      cases ys with
      | nil => exact refl [a]
      | cons b bs => exact False.elim h
  | cons b bs =>
      cases ys with
      | nil => exact False.elim h
      | cons c cs => exact Derives.prepend (Word.singleton a) h

theorem prependCtx (pre : List Nat) {xs ys : List Nat} (h : Rel xs ys) :
    Rel (pre ++ xs) (pre ++ ys) := by
  induction pre with
  | nil => exact h
  | cons a pre ih => exact cons a ih

theorem suffix {xs ys : List Nat} (h : Rel xs ys) (post : List Nat) :
    Rel (xs ++ post) (ys ++ post) := by
  cases xs with
  | nil =>
      cases ys with
      | nil => exact refl post
      | cons b bs => exact False.elim h
  | cons a as =>
      cases ys with
      | nil => exact False.elim h
      | cons b bs =>
          cases post with
          | nil =>
              have hx : (a :: as) ++ [] = a :: as := List.append_nil _
              have hy : (b :: bs) ++ [] = b :: bs := List.append_nil _
              exact hx.symm ▸ hy.symm ▸ h
          | cons c cs => exact Derives.appendRight h (Word.mk c cs)

theorem subst {xs ys : List Nat} (h : Rel xs ys) (sigma : Nat → Word Nat) :
    Rel (xs.flatMap (fun a => (sigma a).toList))
      (ys.flatMap (fun a => (sigma a).toList)) := by
  cases xs with
  | nil =>
      cases ys with
      | nil => exact True.intro
      | cons b bs => exact False.elim h
  | cons a as =>
      cases ys with
      | nil => exact False.elim h
      | cons b bs =>
          have actual : Derives basis (Word.mk a as) (Word.mk b bs) := h
          have lifted : Rel ((Word.mk a as).bind sigma).toList
              ((Word.mk b bs).bind sigma).toList := ofDerives (actual.subst sigma)
          rw [Word.toList_bind, Word.toList_bind] at lifted
          exact lifted

end Rel

theorem power (a : Nat) : Rel [a, a] [a, a, a] := by
  have h := (Rel.ofDerives powerStep).subst (fun _ => Word.singleton a)
  exact h

theorem repeatHead (a : Nat) (p : Word Nat) :
    Rel (a :: (p.toList ++ [a])) (a :: a :: (p.toList ++ [a])) := by
  have h := (Rel.ofDerives repeatStep).subst
    (fun n => if n = 0 then Word.singleton a else p)
  exact h

theorem commute (a b : Nat) : Rel [a,a,b,b] [b,b,a,a] := by
  have h := (Rel.ofDerives squareCommute).subst
    (fun n => if n = 0 then Word.singleton a else Word.singleton b)
  exact h

theorem square_prefix_adjoin (a b : Nat) (p q : List Nat) :
    Rel (a :: a :: (p ++ b :: (q ++ [b])))
      (b :: b :: a :: a :: (p ++ b :: (q ++ [b]))) := by
  cases p with
  | nil =>
      cases q with
      | nil =>
          have h := (Rel.ofDerives squareMove).subst
            (fun n => if n = 0 then Word.singleton a else Word.singleton b)
          exact h
      | cons c cs =>
          have h := (Rel.ofDerives squareMoveQ).subst
            (fun n => if n = 0 then Word.singleton a else
              if n = 1 then Word.singleton b else Word.mk c cs)
          exact h
  | cons c cs =>
      cases q with
      | nil =>
          have h := (Rel.ofDerives squareMoveP).subst
            (fun n => if n = 0 then Word.singleton a else
              if n = 1 then Word.singleton b else Word.mk c cs)
          exact h
      | cons d ds =>
          have h := (Rel.ofDerives squareMovePQ).subst
            (fun n => if n = 0 then Word.singleton a else
              if n = 1 then Word.singleton b else if n = 2 then Word.mk c cs else Word.mk d ds)
          exact h

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach

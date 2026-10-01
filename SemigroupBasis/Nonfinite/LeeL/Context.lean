import SemigroupBasis.Nonfinite.LeeL.SourceWords

namespace SemigroupBasis.Examples.LeeL

open SemigroupBasis

/-- List form of `Q_n`, needed because an external semigroup context may be
empty on either side of the substituted word. -/
def ListInQ (n : Nat) (letters : List Nat) : Prop :=
  ListInP n letters.reverse

namespace ContextWords

private def appendList (word : Word Nat) : List Nat → Word Nat
  | [] => word
  | head :: tail => word ++ ⟨head, tail⟩

/-- Add possibly empty list contexts around a nonempty semigroup word. -/
def wrap (pre : List Nat) (middle : Word Nat) (post : List Nat) : Word Nat :=
  match pre with
  | [] => appendList middle post
  | head :: tail => appendList (⟨head, tail⟩ ++ middle) post

@[simp]
theorem toList_wrap (pre : List Nat) (middle : Word Nat) (post : List Nat) :
    (wrap pre middle post).toList =
      pre ++ middle.toList ++ post := by
  cases pre <;> cases post <;>
    simp [wrap, appendList, Word.toList, List.append_assoc]

theorem eval_wrap_congr
    (pre post : List Nat) (left right : Word Nat)
    (valuation : Nat → Fin 6)
    (middleEquality :
      table.semigroup.eval valuation left =
        table.semigroup.eval valuation right) :
    table.semigroup.eval valuation (wrap pre left post) =
      table.semigroup.eval valuation (wrap pre right post) := by
  cases pre <;> cases post <;>
    simp [wrap, appendList, Semigroup.eval_append, middleEquality]

def identity (source : Identity Nat)
    (pre post : List Nat) (substitution : Nat → Word Nat) :
    Identity Nat :=
  ⟨wrap pre (source.lhs.bind substitution) post,
    wrap pre (source.rhs.bind substitution) post⟩

theorem identity_valid
    {source : Identity Nat}
    (valid : source.SatisfiedBy table.semigroup)
    (pre post : List Nat) (substitution : Nat → Word Nat) :
    (identity source pre post substitution).SatisfiedBy table.semigroup := by
  intro valuation
  apply eval_wrap_congr
  rw [Semigroup.eval_bind, Semigroup.eval_bind]
  exact valid (fun letter =>
    table.semigroup.eval valuation (substitution letter))

@[simp]
theorem identity_lhs_toList
    (source : Identity Nat)
    (pre post : List Nat) (substitution : Nat → Word Nat) :
    (identity source pre post substitution).lhs.toList =
      pre ++ (source.lhs.bind substitution).toList ++ post :=
  toList_wrap pre _ post

@[simp]
theorem identity_rhs_toList
    (source : Identity Nat)
    (pre post : List Nat) (substitution : Nat → Word Nat) :
    (identity source pre post substitution).rhs.toList =
      pre ++ (source.rhs.bind substitution).toList ++ post :=
  toList_wrap pre _ post

theorem lhs_inP_iff
    (n : Nat) (source : Identity Nat)
    (pre post : List Nat) (substitution : Nat → Word Nat) :
    InP n (identity source pre post substitution).lhs ↔
      ListInP n
        (pre ++ (source.lhs.bind substitution).toList ++ post) := by
  simp [InP]

theorem rhs_inP_iff
    (n : Nat) (source : Identity Nat)
    (pre post : List Nat) (substitution : Nat → Word Nat) :
    InP n (identity source pre post substitution).rhs ↔
      ListInP n
        (pre ++ (source.rhs.bind substitution).toList ++ post) := by
  simp [InP]

theorem rhs_inQ_iff
    (n : Nat) (source : Identity Nat)
    (pre post : List Nat) (substitution : Nat → Word Nat) :
    InQ n (identity source pre post substitution).rhs ↔
      ListInQ n
        (pre ++ (source.rhs.bind substitution).toList ++ post) := by
  simp [InQ, ListInQ, InP, Word.toList_reverse]

end ContextWords

end SemigroupBasis.Examples.LeeL

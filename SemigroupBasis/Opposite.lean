import SemigroupBasis.Equational

namespace SemigroupBasis

namespace Word

def reverseAux (head : α) : List α → Word α
  | [] => singleton head
  | next :: rest => reverseAux next rest ++ singleton head

def reverse (w : Word α) : Word α :=
  reverseAux w.head w.tail

private theorem toList_reverseAux (head : α) (tail : List α) :
    (reverseAux head tail).toList = (head :: tail).reverse := by
  induction tail generalizing head with
  | nil => rfl
  | cons next rest ih =>
      simp [reverseAux, toList_append, ih, List.reverse_cons,
        List.append_assoc]

@[simp]
theorem toList_reverse (w : Word α) :
    w.reverse.toList = w.toList.reverse := by
  cases w
  exact toList_reverseAux _ _

@[simp]
theorem reverse_singleton (x : α) : (singleton x).reverse = singleton x := rfl

@[simp]
theorem reverse_append (u v : Word α) :
    (u ++ v).reverse = v.reverse ++ u.reverse := by
  apply toList_injective
  simp only [toList_reverse, toList_append, List.reverse_append]

@[simp]
theorem reverse_reverse (w : Word α) : w.reverse.reverse = w := by
  apply toList_injective
  simp only [toList_reverse, List.reverse_reverse]

@[simp]
theorem reverse_bind (w : Word α) (σ : α → Word β) :
    (w.bind σ).reverse =
      w.reverse.bind (fun x => (σ x).reverse) := by
  apply toList_injective
  simp only [toList_reverse, toList_bind, List.reverse_flatMap]
  rfl

end Word

namespace Semigroup

def opposite (G : Semigroup S) : Semigroup S where
  mul := fun a b => G.mul b a
  assoc := by
    intro a b c
    exact (G.assoc c b a).symm

@[simp]
theorem opposite_mul (G : Semigroup S) (a b : S) :
    G.opposite.mul a b = G.mul b a := rfl

theorem eval_opposite_eq_reverse (G : Semigroup S) (valuation : α → S)
    (w : Word α) :
    G.opposite.eval valuation w = G.eval valuation w.reverse := by
  cases w with
  | mk head tail =>
      induction tail generalizing head with
      | nil => rfl
      | cons next rest ih =>
          change
            G.opposite.eval valuation
                (Word.singleton head ++ Word.mk next rest) =
              G.eval valuation
                ((Word.mk next rest).reverse ++ Word.singleton head)
          rw [eval_append, eval_append, ih]
          rfl

end Semigroup

namespace Identity

def reversed (e : Identity α) : Identity α :=
  ⟨e.lhs.reverse, e.rhs.reverse⟩

@[simp]
theorem reversed_reversed (e : Identity α) : e.reversed.reversed = e := by
  cases e
  simp [reversed]

theorem satisfiedBy_opposite_iff_reversed (e : Identity α) (G : Semigroup S) :
    e.SatisfiedBy G.opposite ↔ e.reversed.SatisfiedBy G := by
  constructor
  · intro h valuation
    simpa [reversed, Semigroup.eval_opposite_eq_reverse] using h valuation
  · intro h valuation
    simpa [reversed, Semigroup.eval_opposite_eq_reverse] using h valuation

end Identity

def reversedBasis (basis : List (Identity α)) : List (Identity α) :=
  basis.map Identity.reversed

@[simp]
theorem reversedBasis_reversedBasis (basis : List (Identity α)) :
    reversedBasis (reversedBasis basis) = basis := by
  induction basis with
  | nil => rfl
  | cons identity rest ih =>
      change identity.reversed.reversed ::
          reversedBasis (reversedBasis rest) = identity :: rest
      rw [Identity.reversed_reversed, ih]

theorem Derives.reverse {basis : List (Identity α)} {u v : Word α}
    (h : Derives basis u v) :
    Derives (reversedBasis basis) u.reverse v.reverse := by
  induction h with
  | fromBasis hmem =>
      exact Derives.fromBasis (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  | refl => exact Derives.refl _
  | symm _ ih => exact Derives.symm ih
  | trans _ _ ih₁ ih₂ => exact Derives.trans ih₁ ih₂
  | prepend p _ ih =>
      simpa using Derives.appendRight ih p.reverse
  | appendRight _ q ih =>
      simpa using Derives.prepend q.reverse ih
  | subst _ σ ih =>
      simpa using Derives.subst ih (fun x => (σ x).reverse)

theorem Models.oppositeReversed (h : Models G basis) :
    Models G.opposite (reversedBasis basis) := by
  intro reversedIdentity hmem
  obtain ⟨identity, identityMem, rfl⟩ := List.mem_map.mp hmem
  rw [Identity.satisfiedBy_opposite_iff_reversed]
  simpa using h identity identityMem

theorem BasisFor.oppositeReversed (h : BasisFor G basis) :
    BasisFor G.opposite (reversedBasis basis) := by
  refine ⟨h.1.oppositeReversed, ?_⟩
  intro identity identityValid
  have reversedValid : identity.reversed.SatisfiedBy G :=
    (Identity.satisfiedBy_opposite_iff_reversed identity G).mp identityValid
  have derivation := (h.2 identity.reversed reversedValid).reverse
  cases identity
  simpa [Identity.reversed] using derivation

end SemigroupBasis

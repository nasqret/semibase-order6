import SemigroupBasis.FiniteTable

namespace SemigroupBasis

namespace Semigroup

private theorem foldl_map (G : Semigroup S) (valuation : β → S)
    (f : α → β) (letters : List α) (initial : S) :
    (letters.map f).foldl
        (fun current x => G.mul current (valuation x)) initial =
      letters.foldl
        (fun current x => G.mul current (valuation (f x))) initial := by
  induction letters generalizing initial with
  | nil => rfl
  | cons next rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih (G.mul initial (valuation (f next)))

theorem eval_map (G : Semigroup S) (valuation : β → S) (f : α → β)
    (word : Word α) :
    G.eval valuation (word.map f) =
      G.eval (fun x => valuation (f x)) word := by
  cases word with
  | mk head tail =>
      exact foldl_map G valuation f tail (valuation (f head))

end Semigroup

namespace Identity

def map (f : α → β) (identity : Identity α) : Identity β :=
  ⟨identity.lhs.map f, identity.rhs.map f⟩

theorem satisfiedBy_map (identity : Identity α) (f : α → β)
    (G : Semigroup S) (h : identity.SatisfiedBy G) :
    (identity.map f).SatisfiedBy G := by
  intro valuation
  simpa only [Identity.map, Semigroup.eval_map] using
    h (fun x => valuation (f x))

end Identity

namespace FiniteTable

/--
Turn an exhaustively checked finite-variable identity into the corresponding
identity over natural-number variable names.
-/
theorem checkIdentityNat_sound (T : FiniteTable)
    (identity : Identity (Fin variables))
    (h : T.checkIdentity identity = true) :
    (identity.map Fin.val).SatisfiedBy T.semigroup :=
  identity.satisfiedBy_map Fin.val T.semigroup
    (T.checkIdentity_sound identity h)

/-- Natural-variable reflection for the fused finite checker. -/
theorem checkIdentityFusedNat_sound (T : FiniteTable)
    (identity : Identity (Fin variables))
    (h : T.checkIdentityFused identity = true) :
    (identity.map Fin.val).SatisfiedBy T.semigroup :=
  identity.satisfiedBy_map Fin.val T.semigroup
    (T.checkIdentityFused_sound identity h)

end FiniteTable

end SemigroupBasis

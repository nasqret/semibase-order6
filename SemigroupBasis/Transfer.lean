import SemigroupBasis.Equational

namespace SemigroupBasis

/-- A homomorphism between two explicitly supplied semigroup structures. -/
structure Hom (G : Semigroup A) (H : Semigroup B) where
  toFun : A → B
  map_mul : ∀ a b, toFun (G.mul a b) = H.mul (toFun a) (toFun b)

namespace Hom

private theorem map_fold {A : Type u} {B : Type v} {α : Type w}
    {G : Semigroup A} {H : Semigroup B}
    (f : Hom G H) (valuation : α → A) (xs : List α) (initial : A) :
    f.toFun (xs.foldl (fun current x => G.mul current (valuation x)) initial) =
      xs.foldl (fun current x => H.mul current (f.toFun (valuation x)))
        (f.toFun initial) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons next rest ih =>
      simp only [List.foldl_cons]
      rw [ih, f.map_mul]

theorem map_eval {A : Type u} {B : Type v} {α : Type w}
    {G : Semigroup A} {H : Semigroup B}
    (f : Hom G H) (valuation : α → A) (word : Word α) :
    f.toFun (G.eval valuation word) =
      H.eval (fun x => f.toFun (valuation x)) word := by
  cases word
  exact map_fold f valuation _ _

end Hom

/-- An injective semigroup homomorphism. -/
structure Embedding (G : Semigroup A) (H : Semigroup B) extends Hom G H where
  injective : Function.Injective toFun

namespace Embedding

theorem pullback_identity {A : Type u} {B : Type v} {α : Type w}
    {G : Semigroup A} {H : Semigroup B}
    (f : Embedding G H) (e : Identity α)
    (h : e.SatisfiedBy H) : e.SatisfiedBy G := by
  intro valuation
  apply f.injective
  rw [f.toHom.map_eval, f.toHom.map_eval]
  exact h (fun x => f.toFun (valuation x))

end Embedding

/-- The embedded-subsemigroup identity-theory sandwich. -/
theorem BasisFor.inheritAlongEmbedding
    {A : Type u} {B : Type v} {α : Type w}
    {G : Semigroup A} {H : Semigroup B} {basis : List (Identity α)}
    (sourceBasis : BasisFor G basis)
    (embedding : Embedding G H) (targetModels : Models H basis) :
    BasisFor H basis := by
  refine ⟨targetModels, ?_⟩
  intro e targetIdentity
  exact sourceBasis.2 e (embedding.pullback_identity e targetIdentity)

end SemigroupBasis

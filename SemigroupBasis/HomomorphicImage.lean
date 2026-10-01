import SemigroupBasis.Congruence
import SemigroupBasis.Equational
import SemigroupBasis.Transfer

namespace SemigroupBasis

/-- Identities are preserved by surjective semigroup homomorphisms. -/
theorem Identity.satisfiedBy_homomorphicImage
    {G : Semigroup A} {H : Semigroup B}
    (identity : Identity α)
    (sourceValid : identity.SatisfiedBy G)
    (hom : Hom G H) (onto : Function.Surjective hom.toFun) :
    identity.SatisfiedBy H := by
  intro valuation
  classical
  let preimage : α → A := fun letter =>
    Classical.choose (onto (valuation letter))
  have preimage_spec (letter : α) :
      hom.toFun (preimage letter) = valuation letter :=
    Classical.choose_spec (onto (valuation letter))
  calc
    H.eval valuation identity.lhs =
        H.eval (fun letter => hom.toFun (preimage letter)) identity.lhs := by
      apply congrArg (fun rho => H.eval rho identity.lhs)
      funext letter
      exact (preimage_spec letter).symm
    _ = hom.toFun (G.eval preimage identity.lhs) :=
      (hom.map_eval preimage identity.lhs).symm
    _ = hom.toFun (G.eval preimage identity.rhs) :=
      congrArg hom.toFun (sourceValid preimage)
    _ = H.eval (fun letter => hom.toFun (preimage letter)) identity.rhs :=
      hom.map_eval preimage identity.rhs
    _ = H.eval valuation identity.rhs := by
      apply congrArg (fun rho => H.eval rho identity.rhs)
      funext letter
      exact preimage_spec letter

/-- Every homomorphic image of a model of a basis is again a model. -/
theorem Models.homomorphicImage
    {G : Semigroup A} {H : Semigroup B}
    {basis : List (Identity α)}
    (sourceModels : Models G basis)
    (hom : Hom G H) (onto : Function.Surjective hom.toFun) :
    Models H basis := by
  intro identity member
  exact identity.satisfiedBy_homomorphicImage
    (sourceModels identity member) hom onto

/-- A congruence quotient inherits every identity of its source semigroup. -/
theorem Semigroup.Congruence.quotient_models
    {G : Semigroup A} (congruence : G.Congruence)
    {basis : List (Identity α)} (sourceModels : Models G basis) :
    Models congruence.quotientSemigroup basis :=
  sourceModels.homomorphicImage congruence.projection
    congruence.projection_surjective

end SemigroupBasis

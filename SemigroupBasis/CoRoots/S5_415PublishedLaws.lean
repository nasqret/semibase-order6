import SemigroupBasis.BrandtLaws
import SemigroupBasis.CoRoots.S5_415

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-- Every explicit semigroup satisfying the published `S5_415` identities
satisfies the three pointwise Brandt laws. -/
theorem brandtLaws_of_models {G : Semigroup S}
    (models : Models G basis) : G.BrandtLaws := by
  refine
    { square_eq_cube := ?_
      sandwich := ?_
      squares_commute := ?_ }
  · intro x
    simpa only [Semigroup.eval_append, Semigroup.eval_singleton] using
      Derives.sound models
        (derivesPowerExpansion (Word.singleton 0))
        (fun _ => x)
  · intro x y
    simpa only [Semigroup.eval_append, Semigroup.eval_singleton] using
      Derives.sound models
        (derivesSandwichExpansion
          (Word.singleton 0) (Word.singleton 1))
        (fun
          | 0 => x
          | _ => y)
  · intro x y
    simpa only [Semigroup.eval_append, Semigroup.eval_singleton] using
      Derives.sound models
        (derivesSquareCommutation
          (Word.singleton 0) (Word.singleton 1))
        (fun
          | 0 => x
          | _ => y)

/-- The semantic exponent-two Kublanovskii consequence of the published
`S5_415` identities. -/
theorem kublanovskii_two_of_models {G : Semigroup S}
    (models : Models G basis) (x y : S) :
    G.mul (G.mul x y) x =
      G.mul
        (G.mul
          (G.mul (G.mul x y) (G.mul x y))
          (G.mul x y))
        x :=
  (brandtLaws_of_models models).kublanovskii_two x y

/-- Idempotents commute in every explicit semigroup satisfying the published
`S5_415` identities. -/
theorem idempotentsCommute_of_models {G : Semigroup S}
    (models : Models G basis) : G.IdempotentsCommute :=
  (brandtLaws_of_models models).idempotentsCommute

end SemigroupBasis.CoRoots.S5_415

import SemigroupBasis.Regular

namespace SemigroupBasis
namespace Semigroup

/-- The three standard identities of the five-element Brandt semigroup,
stated pointwise for an explicitly supplied semigroup. -/
structure BrandtLaws (G : Semigroup S) : Prop where
  square_eq_cube :
    ∀ x, G.mul x x = G.mul (G.mul x x) x
  sandwich :
    ∀ x y,
      G.mul (G.mul x y) x =
        G.mul (G.mul (G.mul (G.mul x y) x) y) x
  squares_commute :
    ∀ x y,
      G.mul (G.mul x x) (G.mul y y) =
        G.mul (G.mul y y) (G.mul x x)

/-- The exponent-two Kublanovskii consequence `xyx = (xy)^3 x`. -/
theorem BrandtLaws.kublanovskii_two {G : Semigroup S}
    (laws : G.BrandtLaws) (x y : S) :
    G.mul (G.mul x y) x =
      G.mul
        (G.mul
          (G.mul (G.mul x y) (G.mul x y))
          (G.mul x y))
        x := by
  calc
    G.mul (G.mul x y) x =
        G.mul (G.mul (G.mul (G.mul x y) x) y) x :=
      laws.sandwich x y
    _ = G.mul (G.mul (G.mul x y) (G.mul x y)) x := by
      rw [G.assoc (G.mul x y) x y]
    _ =
        G.mul
          (G.mul
            (G.mul (G.mul x y) (G.mul x y))
            (G.mul x y))
          x :=
      congrArg (fun product => G.mul product x)
        (laws.square_eq_cube (G.mul x y))

/-- The graph-switch consequence `xyxzx = xzxyx` of the three Brandt
identities. The proof expands both sandwich cells, commutes the resulting
square blocks, and contracts the two cells in the opposite order. -/
theorem BrandtLaws.graph_switch {G : Semigroup S}
    (laws : G.BrandtLaws) (x y z : S) :
    G.mul (G.mul (G.mul (G.mul x y) x) z) x =
      G.mul (G.mul (G.mul (G.mul x z) x) y) x := by
  have expandY :=
    congrArg (fun cell => G.mul (G.mul cell z) x)
      (laws.sandwich x y)
  have expandZ :=
    congrArg
      (fun cell =>
        G.mul (G.mul (G.mul x y) (G.mul x y)) cell)
      (laws.sandwich x z)
  have commute :=
    congrArg (fun blocks => G.mul blocks x)
      (laws.squares_commute (G.mul x y) (G.mul x z))
  have contractZ :=
    congrArg
      (fun cell => G.mul (G.mul (G.mul (G.mul cell y) x) y) x)
      (laws.sandwich x z).symm
  have contractY :=
    congrArg (fun cell => G.mul (G.mul x z) cell)
      (laws.sandwich x y).symm
  calc
    G.mul (G.mul (G.mul (G.mul x y) x) z) x =
        G.mul
          (G.mul
            (G.mul
              (G.mul
                (G.mul (G.mul x y) x)
                y)
              x)
            z)
          x := expandY
    _ = G.mul
          (G.mul
            (G.mul (G.mul x y) (G.mul x y))
            (G.mul (G.mul x z) (G.mul x z)))
          x := by
      simpa only [G.assoc] using expandZ
    _ = G.mul
          (G.mul
            (G.mul (G.mul x z) (G.mul x z))
            (G.mul (G.mul x y) (G.mul x y)))
          x := commute
    _ = G.mul (G.mul x z)
          (G.mul (G.mul (G.mul (G.mul x y) x) y) x) := by
      simpa only [G.assoc] using contractZ
    _ = G.mul (G.mul (G.mul (G.mul x z) x) y) x := by
      simpa only [G.assoc] using contractY

/-- The commuting-squares law forces all idempotents to commute. -/
theorem BrandtLaws.idempotentsCommute {G : Semigroup S}
    (laws : G.BrandtLaws) : G.IdempotentsCommute := by
  intro a b ha hb
  change G.mul a a = a at ha
  change G.mul b b = b at hb
  calc
    G.mul a b = G.mul (G.mul a a) (G.mul b b) := by
      rw [ha, hb]
    _ = G.mul (G.mul b b) (G.mul a a) :=
      laws.squares_commute a b
    _ = G.mul b a := by
      rw [ha, hb]

end Semigroup
end SemigroupBasis

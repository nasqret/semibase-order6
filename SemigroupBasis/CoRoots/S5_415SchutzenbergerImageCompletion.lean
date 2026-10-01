import SemigroupBasis.CoRoots.S5_415SchutzenbergerZeroSimple

namespace SemigroupBasis
namespace Semigroup

/-- The Hall--Kublanovskii fixed representative at exponent two. If `z` is
regular and `x` is outside `I_z`, then one element `y` of `S z S` has the
same right action as `x` on all of `S z S`.

Choose an inverse `zInv` and a factorization `z = p * x * q`, set
`w = q * zInv * p`, and take `y = x * w * x`. The graph-switch law is what
makes this representative independent of the tested element. -/
theorem BrandtLaws.exists_fixed_rightActionRepresentative_of_not_mem_I_z
    {G : Semigroup S} (laws : G.BrandtLaws) {z x : S}
    (zRegular : G.IsRegular z) (xNotInIdeal : ¬ (x ∈ I_z G z)) :
    ∃ y, G.PrincipalSandwichMem z y ∧
      ∀ t, G.PrincipalSandwichMem z t →
        G.mul x t = G.mul y t := by
  rcases zRegular with ⟨zInv, zInverse⟩
  rcases principalSandwichMem_of_not_mem_I_z xNotInIdeal with
    ⟨p, q, zFactor⟩
  let w := G.mul (G.mul q zInv) p
  let y := G.mul (G.mul x w) x
  have wInSandwich : G.PrincipalSandwichMem z w := by
    have zInvInSandwich : G.PrincipalSandwichMem z zInv :=
      zInverse.inverse_principalSandwichMem
    exact (zInvInSandwich.mul_left q).mul_right p
  have yInSandwich : G.PrincipalSandwichMem z y := by
    exact (wInSandwich.mul_left x).mul_right x
  have zInYSandwich : G.PrincipalSandwichMem y z := by
    refine ⟨p, q, ?_⟩
    calc
      z = G.mul (G.mul z zInv) z := zInverse.1.symm
      _ = G.mul
          (G.mul (G.mul (G.mul p x) q) zInv)
          (G.mul (G.mul p x) q) := by
        calc
          G.mul (G.mul z zInv) z =
              G.mul (G.mul (G.mul (G.mul p x) q) zInv) z :=
            congrArg (fun u => G.mul (G.mul u zInv) z) zFactor
          _ = G.mul
              (G.mul (G.mul (G.mul p x) q) zInv)
              (G.mul (G.mul p x) q) :=
            congrArg
              (fun u =>
                G.mul (G.mul (G.mul (G.mul p x) q) zInv) u)
              zFactor
      _ = G.mul (G.mul p y) q := by
        simp only [w, y, G.assoc]
  have principalSandwichEq :
      G.PrincipalSandwichMem z = G.PrincipalSandwichMem y :=
    principalSandwich_eq_of_mutual_mem zInYSandwich yInSandwich
  refine ⟨y, yInSandwich, ?_⟩
  intro t tInSandwich
  have tInYSandwich : G.PrincipalSandwichMem y t := by
    rw [← principalSandwichEq]
    exact tInSandwich
  rcases tInYSandwich with ⟨r, s, tFactor⟩
  have expandW :=
    congrArg
      (fun cell => G.mul (G.mul (G.mul x r) cell) s)
      (laws.sandwich x w)
  have switchPrefix :=
    congrArg
      (fun partialProduct => G.mul (G.mul (G.mul partialProduct w) x) s)
      (laws.graph_switch x r w)
  calc
    G.mul x t = G.mul x (G.mul (G.mul r y) s) :=
      congrArg (fun value => G.mul x value) tFactor
    _ = G.mul (G.mul (G.mul x r) (G.mul (G.mul x w) x)) s := by
      simp only [y, G.assoc]
    _ = G.mul
          (G.mul (G.mul x r)
            (G.mul (G.mul (G.mul (G.mul x w) x) w) x))
          s := expandW
    _ = G.mul y (G.mul (G.mul r y) s) := by
      simpa only [y, G.assoc] using switchPrefix
    _ = G.mul y t :=
      (congrArg (fun value => G.mul y value) tFactor).symm

/-- The fixed Hall--Kublanovskii representative discharges the right
Schutzenberger image condition without a pointwise-to-uniform premise. -/
theorem BrandtLaws.rightSchutzenbergerImageCondition
    {G : Semigroup S} (laws : G.BrandtLaws) {z : S}
    (zRegular : G.IsRegular z) :
    G.RightSchutzenbergerImageCondition z := by
  intro x xNotInIdeal _
  rcases laws.exists_fixed_rightActionRepresentative_of_not_mem_I_z
      zRegular xNotInIdeal with ⟨y, yInSandwich, sameAction⟩
  exact ⟨y, yInSandwich,
    rightSchutzenbergerRel_of_mul_eq_on_principalSandwich
      G z sameAction⟩

/-- Every right Schutzenberger class at a regular element has a representative
in `S z S`. The ideal class, an already represented class, and the remaining
classes are handled by the standard three-way image-condition reduction. -/
theorem BrandtLaws.exists_principalSandwich_rightSchutzenbergerRel_direct
    {G : Semigroup S} (laws : G.BrandtLaws) {z x : S}
    (zRegular : G.IsRegular z) :
    ∃ y, G.PrincipalSandwichMem z y ∧
      G.RightSchutzenbergerRel z x y := by
  exact exists_principalSandwich_rightSchutzenbergerRel_of_imageCondition
    G z x (laws.rightSchutzenbergerImageCondition zRegular)

end Semigroup

namespace CoRoots.S5_415

open SemigroupBasis

/-- The presented `S5_415` term semigroup satisfies the right
Schutzenberger image condition at every regular class. -/
theorem rightSchutzenbergerImageCompleteness :
    RightSchutzenbergerImageCompleteness := by
  intro z zRegular
  exact termSemigroup_brandtLaws.rightSchutzenbergerImageCondition zRegular

/-- The Hall--Kublanovskii image theorem closes the published
minimal-counterexample reduction for the three `S5_415` identities. -/
theorem brandtDerivationalCompleteness :
    BrandtDerivationalCompleteness :=
  derivationalCompleteness_of_imageCompleteness
    rightSchutzenbergerImageCompleteness

end CoRoots.S5_415
end SemigroupBasis

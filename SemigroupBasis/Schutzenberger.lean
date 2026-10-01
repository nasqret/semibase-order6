import SemigroupBasis.Ideal

namespace SemigroupBasis
namespace Semigroup

/-- Left multiplication preserves membership in the principal sandwich `S * z * S`. -/
theorem PrincipalSandwichMem.mul_left {G : Semigroup S} {z t : S}
    (ht : G.PrincipalSandwichMem z t) (a : S) :
    G.PrincipalSandwichMem z (G.mul a t) := by
  rcases ht with ⟨p, q, rfl⟩
  refine ⟨G.mul a p, q, ?_⟩
  simp only [G.assoc]

/-- Volkov's right Schutzenberger relation associated to `z`.

Two elements are related when all of their right translates by elements of
`S * z * S` are Rees-related modulo `I_z`.
-/
def RightSchutzenbergerRel (G : Semigroup S) (z x y : S) : Prop :=
  ∀ t, G.PrincipalSandwichMem z t →
    (I_z G z).ReesRel (G.mul x t) (G.mul y t)

theorem rightSchutzenbergerRel_refl (G : Semigroup S) (z x : S) :
    G.RightSchutzenbergerRel z x x := by
  intro t _
  exact Ideal.reesRel_refl (I_z G z) (G.mul x t)

theorem rightSchutzenbergerRel_symm (G : Semigroup S) (z : S) {x y : S}
    (h : G.RightSchutzenbergerRel z x y) :
    G.RightSchutzenbergerRel z y x := by
  intro t ht
  exact Ideal.reesRel_symm (I_z G z) (h t ht)

theorem rightSchutzenbergerRel_trans (G : Semigroup S) (z : S) {x y w : S}
    (hxy : G.RightSchutzenbergerRel z x y)
    (hyw : G.RightSchutzenbergerRel z y w) :
    G.RightSchutzenbergerRel z x w := by
  intro t ht
  exact Ideal.reesRel_trans (I_z G z) (hxy t ht) (hyw t ht)

theorem rightSchutzenbergerRel_equivalence (G : Semigroup S) (z : S) :
    Equivalence (G.RightSchutzenbergerRel z) where
  refl := rightSchutzenbergerRel_refl G z
  symm := rightSchutzenbergerRel_symm G z
  trans := rightSchutzenbergerRel_trans G z

/-- The Rees relation modulo `I_z` is contained in `rho_z`. -/
theorem reesRel_imp_rightSchutzenbergerRel (G : Semigroup S) (z : S)
    {x y : S} (h : (I_z G z).ReesRel x y) :
    G.RightSchutzenbergerRel z x y := by
  intro t _
  exact Congruence.mul_compat_right (Ideal.reesCongruence (I_z G z)) h t

/-- Volkov's right Schutzenberger relation, packaged as a semigroup congruence. -/
def rightSchutzenbergerCongruence (G : Semigroup S) (z : S) : Congruence G where
  r := G.RightSchutzenbergerRel z
  iseqv := rightSchutzenbergerRel_equivalence G z
  mul_compat := by
    intro a₁ a₂ b₁ b₂ ha hb t ht
    have hbAt :
        (I_z G z).ReesRel (G.mul b₁ t) (G.mul b₂ t) :=
      hb t ht
    have leftStep :
        (I_z G z).ReesRel
          (G.mul a₁ (G.mul b₁ t))
          (G.mul a₁ (G.mul b₂ t)) :=
      Congruence.mul_compat_left
        (Ideal.reesCongruence (I_z G z)) a₁ hbAt
    have haAt :
        (I_z G z).ReesRel
          (G.mul a₁ (G.mul b₂ t))
          (G.mul a₂ (G.mul b₂ t)) :=
      ha (G.mul b₂ t) (PrincipalSandwichMem.mul_left ht b₂)
    simpa only [G.assoc] using
      Ideal.reesRel_trans (I_z G z) leftStep haAt

@[simp]
theorem rightSchutzenbergerCongruence_rel_iff (G : Semigroup S) (z x y : S) :
    (rightSchutzenbergerCongruence G z).r x y ↔
      G.RightSchutzenbergerRel z x y :=
  Iff.rfl

/-- Equality in the `rho_z` quotient is exactly right Schutzenberger equivalence. -/
theorem rightSchutzenberger_classOf_eq_iff (G : Semigroup S) (z : S)
    {x y : S} :
    (rightSchutzenbergerCongruence G z).classOf x =
        (rightSchutzenbergerCongruence G z).classOf y ↔
      G.RightSchutzenbergerRel z x y := by
  change
    (rightSchutzenbergerCongruence G z).classOf x =
        (rightSchutzenbergerCongruence G z).classOf y ↔
      (rightSchutzenbergerCongruence G z).r x y
  exact (rightSchutzenbergerCongruence G z).classOf_eq_iff

/-- The canonical quotient projection identifies exactly the `rho_z`-related pairs. -/
theorem rightSchutzenberger_projection_eq_iff (G : Semigroup S) (z : S)
    {x y : S} :
    (rightSchutzenbergerCongruence G z).projection.toFun x =
        (rightSchutzenbergerCongruence G z).projection.toFun y ↔
      G.RightSchutzenbergerRel z x y := by
  simpa only [Congruence.projection_apply] using
    (rightSchutzenberger_classOf_eq_iff G z (x := x) (y := y))

/-- A concrete right translate witnessing failure of `rho_z`. -/
def RightSchutzenbergerSeparates (G : Semigroup S) (z x y : S) : Prop :=
  ∃ t, G.PrincipalSandwichMem z t ∧
    ¬ (I_z G z).ReesRel (G.mul x t) (G.mul y t)

/-- Distinct quotient classes are equivalent to an explicit separating translate. -/
theorem rightSchutzenberger_classOf_ne_iff_exists_separator
    (G : Semigroup S) (z : S) {x y : S} :
    (rightSchutzenbergerCongruence G z).classOf x ≠
        (rightSchutzenbergerCongruence G z).classOf y ↔
      G.RightSchutzenbergerSeparates z x y := by
  classical
  unfold RightSchutzenbergerSeparates
  constructor
  · intro hne
    apply Classical.byContradiction
    intro hnot
    apply hne
    apply (rightSchutzenberger_classOf_eq_iff G z).2
    intro t ht
    apply Classical.byContradiction
    intro hrees
    exact hnot ⟨t, ht, hrees⟩
  · rintro ⟨t, ht, hrees⟩ heq
    exact hrees (((rightSchutzenberger_classOf_eq_iff G z).1 heq) t ht)

/-- Projection inequality is equivalent to an explicit separating translate. -/
theorem rightSchutzenberger_projection_ne_iff_exists_separator
    (G : Semigroup S) (z : S) {x y : S} :
    (rightSchutzenbergerCongruence G z).projection.toFun x ≠
        (rightSchutzenbergerCongruence G z).projection.toFun y ↔
      G.RightSchutzenbergerSeparates z x y := by
  simpa only [Congruence.projection_apply] using
    (rightSchutzenberger_classOf_ne_iff_exists_separator G z
      (x := x) (y := y))

end Semigroup
end SemigroupBasis

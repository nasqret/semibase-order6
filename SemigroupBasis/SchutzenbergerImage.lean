import SemigroupBasis.BrandtLaws
import SemigroupBasis.Schutzenberger

namespace SemigroupBasis
namespace Semigroup

/-- Right multiplication preserves membership in the principal sandwich
`S * z * S`. -/
theorem PrincipalSandwichMem.mul_right {G : Semigroup S} {z t : S}
    (ht : G.PrincipalSandwichMem z t) (a : S) :
    G.PrincipalSandwichMem z (G.mul t a) := by
  rcases ht with ⟨p, q, rfl⟩
  refine ⟨p, G.mul q a, ?_⟩
  exact G.assoc (G.mul p z) q a

/-- Membership in principal sandwiches composes. -/
theorem PrincipalSandwichMem.trans {G : Semigroup S} {x y z : S}
    (hxy : G.PrincipalSandwichMem y x)
    (hyz : G.PrincipalSandwichMem z y) :
    G.PrincipalSandwichMem z x := by
  rcases hxy with ⟨p, q, hx⟩
  rcases hyz with ⟨r, s, hy⟩
  refine ⟨G.mul p r, G.mul s q, ?_⟩
  calc
    x = G.mul (G.mul p y) q := hx
    _ = G.mul (G.mul p (G.mul (G.mul r z) s)) q := by rw [hy]
    _ = G.mul (G.mul (G.mul p r) z) (G.mul s q) := by
      simp only [G.assoc]

/-- Mutual principal-sandwich membership is equality of principal ideals. -/
theorem principalSandwich_eq_of_mutual_mem {G : Semigroup S} {x y : S}
    (hxy : G.PrincipalSandwichMem y x)
    (hyx : G.PrincipalSandwichMem x y) :
    G.PrincipalSandwichMem x = G.PrincipalSandwichMem y := by
  funext t
  apply propext
  constructor
  · intro ht
    exact ht.trans hxy
  · intro ht
    exact ht.trans hyx

/-- Being outside `I_z` supplies the reverse principal-ideal inclusion. -/
theorem principalSandwichMem_of_not_mem_I_z {G : Semigroup S} {z u : S}
    (hu : ¬ (u ∈ I_z G z)) :
    G.PrincipalSandwichMem u z := by
  classical
  apply Classical.byContradiction
  intro hzu
  apply hu
  change ¬ G.PrincipalSandwichMem u z
  exact hzu

/-- An element of `S z S` outside `I_z` generates exactly `S z S`. -/
theorem principalSandwich_eq_of_mem_not_mem_I_z
    {G : Semigroup S} {z u : S}
    (huz : G.PrincipalSandwichMem z u)
    (hu : ¬ (u ∈ I_z G z)) :
    G.PrincipalSandwichMem z = G.PrincipalSandwichMem u :=
  principalSandwich_eq_of_mutual_mem
    (principalSandwichMem_of_not_mem_I_z hu) huz

/-- A regular element belongs to its own principal sandwich. -/
theorem IsInverse.self_principalSandwichMem
    {G : Semigroup S} {a aInv : S} (h : G.IsInverse a aInv) :
    G.PrincipalSandwichMem a a := by
  refine ⟨G.mul a aInv, G.mul aInv a, ?_⟩
  calc
    a = G.mul (G.mul a aInv) a := h.1.symm
    _ = G.mul a (G.mul aInv a) := G.assoc a aInv a
    _ = G.mul (G.mul (G.mul a aInv) a) (G.mul aInv a) := by
      rw [h.1]

/-- A chosen inverse of `a` belongs to `S a S`. -/
theorem IsInverse.inverse_principalSandwichMem
    {G : Semigroup S} {a aInv : S} (h : G.IsInverse a aInv) :
    G.PrincipalSandwichMem a aInv :=
  ⟨aInv, aInv, h.2.symm⟩

/-- A concrete representative in `S z S` for the Rees-zero class. -/
def reesZeroRepresentative (G : Semigroup S) (z x : S) : S :=
  G.mul (G.mul x z) x

theorem reesZeroRepresentative_principalSandwichMem
    (G : Semigroup S) (z x : S) :
    G.PrincipalSandwichMem z (reesZeroRepresentative G z x) :=
  ⟨x, x, rfl⟩

theorem reesZeroRepresentative_mem_I_z
    (G : Semigroup S) (z : S) {x : S} (hx : x ∈ I_z G z) :
    reesZeroRepresentative G z x ∈ I_z G z := by
  exact (I_z G z).mul_mem_right
    ((I_z G z).mul_mem_right hx z) x

/-- Every element in `I_z` is `rho_z`-related to an explicit element of
`I_z ∩ S z S`; this handles the Rees-zero class without assuming it exists. -/
theorem rightSchutzenbergerRel_reesZeroRepresentative
    (G : Semigroup S) (z : S) {x : S} (hx : x ∈ I_z G z) :
    G.RightSchutzenbergerRel z x (reesZeroRepresentative G z x) := by
  apply reesRel_imp_rightSchutzenbergerRel G z
  exact Or.inr ⟨hx, reesZeroRepresentative_mem_I_z G z hx⟩

theorem exists_principalSandwich_rightSchutzenbergerRel_of_mem_I_z
    (G : Semigroup S) (z : S) {x : S} (hx : x ∈ I_z G z) :
    ∃ y, G.PrincipalSandwichMem z y ∧
      G.RightSchutzenbergerRel z x y :=
  ⟨reesZeroRepresentative G z x,
    reesZeroRepresentative_principalSandwichMem G z x,
    rightSchutzenbergerRel_reesZeroRepresentative G z hx⟩

/-- Literal equality on all right translates by `S z S` implies
right Schutzenberger equivalence. -/
theorem rightSchutzenbergerRel_of_mul_eq_on_principalSandwich
    (G : Semigroup S) (z : S) {x y : S}
    (hxy : ∀ t, G.PrincipalSandwichMem z t →
      G.mul x t = G.mul y t) :
    G.RightSchutzenbergerRel z x y := by
  intro t ht
  exact Or.inl (hxy t ht)

/-- The factor `r * x * w * x * s` used in the middle calculation of
Volkov's Lemma 5. -/
def schutzenbergerMiddleFactor
    (G : Semigroup S) (x w r s : S) : S :=
  G.mul (G.mul (G.mul (G.mul r x) w) x) s

/-- The factorization furnished by equality of the principal ideals has a
left factor that may depend on the tested element `t`. -/
def PointwisePrincipalFactorization
    (G : Semigroup S) (z x : S) : Prop :=
  ∃ w, G.PrincipalSandwichMem z w ∧
    ∀ t, G.PrincipalSandwichMem z t →
      ∃ r s, t = schutzenbergerMiddleFactor G x w r s

/-- The uniform strengthening needed to turn Volkov's pointwise calculation
into one fixed representative of a `rho_z`-class. -/
def UniformPrincipalFactorization
    (G : Semigroup S) (z x : S) : Prop :=
  ∃ w r, G.PrincipalSandwichMem z w ∧
    ∀ t, G.PrincipalSandwichMem z t →
      ∃ s, t = schutzenbergerMiddleFactor G x w r s

/-- The exact quantifier-uniformization condition left after the regularity
and principal-ideal arguments: `∀ t, ∃ r, s` must be strengthened to a
single `r` that works for every `t`. -/
def RightSchutzenbergerImageUniformity
    (G : Semigroup S) (z : S) : Prop :=
  ∀ x, ¬ (x ∈ I_z G z) →
    ¬ G.PrincipalSandwichMem z x →
    G.PointwisePrincipalFactorization z x →
    G.UniformPrincipalFactorization z x

/-- The exact residual condition for surjectivity: only classes represented
by elements outside both `I_z` and `S z S` need an additional witness. -/
def RightSchutzenbergerImageCondition
    (G : Semigroup S) (z : S) : Prop :=
  ∀ x, ¬ (x ∈ I_z G z) →
    ¬ G.PrincipalSandwichMem z x →
    ∃ y, G.PrincipalSandwichMem z y ∧
      G.RightSchutzenbergerRel z x y

/-- A fixed element of `S z S` which has the same right action as `x` once
the left factor `r` is uniform. -/
def brandtRightActionWitness
    (G : Semigroup S) (x w r : S) : S :=
  G.mul
    (G.mul
      (G.mul (G.mul x r)
        (G.mul (G.mul x w) (G.mul x w)))
      (G.mul x r))
    x

theorem brandtRightActionWitness_principalSandwichMem
    {G : Semigroup S} {z x w r : S}
    (hw : G.PrincipalSandwichMem z w) :
    G.PrincipalSandwichMem z (brandtRightActionWitness G x w r) := by
  have hxw : G.PrincipalSandwichMem z (G.mul x w) :=
    hw.mul_left x
  have hxwSquare :
      G.PrincipalSandwichMem z (G.mul (G.mul x w) (G.mul x w)) :=
    hxw.mul_right (G.mul x w)
  exact (((hxwSquare.mul_left (G.mul x r)).mul_right (G.mul x r)).mul_right x)

/-- The exponent-two calculation in the middle of Volkov's Lemma 5, with a
fixed left factor `r`. -/
theorem BrandtLaws.mul_middleFactor_eq_rightActionWitness_mul
    {G : Semigroup S} (laws : G.BrandtLaws) (x w r s : S) :
    G.mul x (schutzenbergerMiddleFactor G x w r s) =
      G.mul (brandtRightActionWitness G x w r)
        (schutzenbergerMiddleFactor G x w r s) := by
  let a := G.mul x r
  let b := G.mul x w
  change
    G.mul x (G.mul (G.mul (G.mul (G.mul r x) w) x) s) =
      G.mul
        (G.mul (G.mul (G.mul a (G.mul b b)) a) x)
        (G.mul (G.mul (G.mul (G.mul r x) w) x) s)
  calc
    G.mul x (G.mul (G.mul (G.mul (G.mul r x) w) x) s) =
        G.mul (G.mul (G.mul x r) x) (G.mul w (G.mul x s)) := by
      simp only [G.assoc]
    _ = G.mul
          (G.mul (G.mul (G.mul a a) a) x)
          (G.mul w (G.mul x s)) := by
      exact congrArg
        (fun cell => G.mul cell (G.mul w (G.mul x s)))
        (laws.kublanovskii_two x r)
    _ = G.mul (G.mul (G.mul a a) a)
          (G.mul (G.mul (G.mul x w) x) s) := by
      simp only [G.assoc]
    _ = G.mul (G.mul (G.mul a a) a)
          (G.mul (G.mul (G.mul (G.mul b b) b) x) s) := by
      exact congrArg
        (fun cell => G.mul (G.mul (G.mul a a) a) (G.mul cell s))
        (laws.kublanovskii_two x w)
    _ = G.mul a
          (G.mul (G.mul (G.mul a a) (G.mul b b))
            (G.mul b (G.mul x s))) := by
      simp only [G.assoc]
    _ = G.mul a
          (G.mul (G.mul (G.mul b b) (G.mul a a))
            (G.mul b (G.mul x s))) := by
      exact congrArg
        (fun squares => G.mul a (G.mul squares (G.mul b (G.mul x s))))
        (laws.squares_commute a b)
    _ = G.mul
          (G.mul (G.mul (G.mul a (G.mul b b)) a) x)
          (G.mul (G.mul (G.mul (G.mul r x) w) x) s) := by
      simp only [a, b, G.assoc]

/-- Regularity gives Volkov's pointwise factorization. It deliberately has
the quantifier order `∀ t, ∃ r, s`; no uniform `r` is claimed. -/
theorem IsInverse.pointwisePrincipalFactorization
    {G : Semigroup S} {z zInv x : S}
    (hz : G.IsInverse z zInv) (hx : ¬ (x ∈ I_z G z)) :
    G.PointwisePrincipalFactorization z x := by
  classical
  rcases principalSandwichMem_of_not_mem_I_z hx with ⟨p, q, hzpxq⟩
  let w := G.mul (G.mul q zInv) p
  have hw : G.PrincipalSandwichMem z w := by
    have hzInvMem : G.PrincipalSandwichMem z zInv :=
      hz.inverse_principalSandwichMem
    exact (hzInvMem.mul_left q).mul_right p
  refine ⟨w, hw, ?_⟩
  have hMiddleMem :
      G.PrincipalSandwichMem z (G.mul (G.mul x w) x) :=
    (hw.mul_left x).mul_right x
  have hzMiddle :
      G.PrincipalSandwichMem (G.mul (G.mul x w) x) z := by
    refine ⟨p, q, ?_⟩
    calc
      z = G.mul (G.mul z zInv) z := hz.1.symm
      _ = G.mul
          (G.mul (G.mul (G.mul p x) q) zInv)
          (G.mul (G.mul p x) q) := by
        calc
          G.mul (G.mul z zInv) z =
              G.mul (G.mul (G.mul (G.mul p x) q) zInv) z :=
            congrArg (fun u => G.mul (G.mul u zInv) z) hzpxq
          _ = G.mul
              (G.mul (G.mul (G.mul p x) q) zInv)
              (G.mul (G.mul p x) q) :=
            congrArg
              (fun u =>
                G.mul (G.mul (G.mul (G.mul p x) q) zInv) u)
              hzpxq
      _ = G.mul (G.mul p (G.mul (G.mul x w) x)) q := by
        simp only [w, G.assoc]
  have hMiddleNotI :
      ¬ (G.mul (G.mul x w) x ∈ I_z G z) := by
    intro hMiddleI
    change ¬ G.PrincipalSandwichMem (G.mul (G.mul x w) x) z at hMiddleI
    exact hMiddleI hzMiddle
  have hPrincipalEq :
      G.PrincipalSandwichMem z =
        G.PrincipalSandwichMem (G.mul (G.mul x w) x) :=
    principalSandwich_eq_of_mem_not_mem_I_z hMiddleMem hMiddleNotI
  intro t ht
  have htMiddle :
      G.PrincipalSandwichMem (G.mul (G.mul x w) x) t := by
    rw [← hPrincipalEq]
    exact ht
  rcases htMiddle with ⟨r, s, ht⟩
  refine ⟨r, s, ?_⟩
  calc
    t = G.mul (G.mul r (G.mul (G.mul x w) x)) s := ht
    _ = schutzenbergerMiddleFactor G x w r s := by
      simp only [schutzenbergerMiddleFactor, G.assoc]

theorem pointwisePrincipalFactorization_of_isRegular
    {G : Semigroup S} {z x : S}
    (hz : G.IsRegular z) (hx : ¬ (x ∈ I_z G z)) :
    G.PointwisePrincipalFactorization z x := by
  rcases hz with ⟨zInv, hzInv⟩
  exact hzInv.pointwisePrincipalFactorization hx

/-- The strongest unconditional output of the displayed middle calculation:
for each tested `t`, some sandwich element has the same value after right
multiplication by that `t`. The element may depend on `t`. -/
theorem BrandtLaws.pointwise_rightAction_witness
    {G : Semigroup S} {z x : S} (laws : G.BrandtLaws)
    (hfactor : G.PointwisePrincipalFactorization z x) :
    ∀ t, G.PrincipalSandwichMem z t →
      ∃ y, G.PrincipalSandwichMem z y ∧
        G.mul x t = G.mul y t := by
  rcases hfactor with ⟨w, hw, hfactor⟩
  intro t ht
  rcases hfactor t ht with ⟨r, s, rfl⟩
  refine ⟨brandtRightActionWitness G x w r,
    brandtRightActionWitness_principalSandwichMem hw, ?_⟩
  exact laws.mul_middleFactor_eq_rightActionWitness_mul x w r s

theorem BrandtLaws.pointwise_rightAction_witness_of_isRegular
    {G : Semigroup S} {z x : S} (laws : G.BrandtLaws)
    (hz : G.IsRegular z) (hx : ¬ (x ∈ I_z G z)) :
    ∀ t, G.PrincipalSandwichMem z t →
      ∃ y, G.PrincipalSandwichMem z y ∧
        G.mul x t = G.mul y t :=
  laws.pointwise_rightAction_witness
    (pointwisePrincipalFactorization_of_isRegular hz hx)

/-- A uniform middle factor gives one fixed representative of the entire
`rho_z`-class. -/
theorem BrandtLaws.exists_principalSandwich_rightSchutzenbergerRel_of_uniform
    {G : Semigroup S} {z x : S} (laws : G.BrandtLaws)
    (hfactor : G.UniformPrincipalFactorization z x) :
    ∃ y, G.PrincipalSandwichMem z y ∧
      G.RightSchutzenbergerRel z x y := by
  rcases hfactor with ⟨w, r, hw, hfactor⟩
  refine ⟨brandtRightActionWitness G x w r,
    brandtRightActionWitness_principalSandwichMem hw, ?_⟩
  apply rightSchutzenbergerRel_of_mul_eq_on_principalSandwich G z
  intro t ht
  rcases hfactor t ht with ⟨s, rfl⟩
  exact laws.mul_middleFactor_eq_rightActionWitness_mul x w r s

/-- The pointwise-to-uniform hypothesis discharges the exact residual image
condition under the hypotheses used in Volkov's middle claim. -/
theorem BrandtLaws.rightSchutzenbergerImageCondition_of_uniformity
    {G : Semigroup S} {z : S} (laws : G.BrandtLaws)
    (hz : G.IsRegular z) (uniform : G.RightSchutzenbergerImageUniformity z) :
    G.RightSchutzenbergerImageCondition z := by
  intro x hxI hxSandwich
  have hpointwise : G.PointwisePrincipalFactorization z x :=
    pointwisePrincipalFactorization_of_isRegular hz hxI
  exact laws.exists_principalSandwich_rightSchutzenbergerRel_of_uniform
    (uniform x hxI hxSandwich hpointwise)

/-- The exact image condition, together with the unconditional Rees-zero and
already-in-the-sandwich cases, supplies a representative for every element. -/
theorem exists_principalSandwich_rightSchutzenbergerRel_of_imageCondition
    (G : Semigroup S) (z x : S)
    (imageCondition : G.RightSchutzenbergerImageCondition z) :
    ∃ y, G.PrincipalSandwichMem z y ∧
      G.RightSchutzenbergerRel z x y := by
  classical
  by_cases hxI : x ∈ I_z G z
  · exact exists_principalSandwich_rightSchutzenbergerRel_of_mem_I_z G z hxI
  · by_cases hxSandwich : G.PrincipalSandwichMem z x
    · exact ⟨x, hxSandwich, rightSchutzenbergerRel_refl G z x⟩
    · exact imageCondition x hxI hxSandwich

/-- Conditional form of the middle claim in Volkov's Lemma 5. The zero
class and classes already meeting `S z S` are unconditional; only the
pointwise-to-uniform step uses `RightSchutzenbergerImageUniformity`. -/
theorem BrandtLaws.exists_principalSandwich_rightSchutzenbergerRel
    {G : Semigroup S} {z x : S} (laws : G.BrandtLaws)
    (hz : G.IsRegular z) (uniform : G.RightSchutzenbergerImageUniformity z) :
    ∃ y, G.PrincipalSandwichMem z y ∧
      G.RightSchutzenbergerRel z x y := by
  exact exists_principalSandwich_rightSchutzenbergerRel_of_imageCondition G z x
    (laws.rightSchutzenbergerImageCondition_of_uniformity hz uniform)

/-- Every quotient class has a principal-sandwich representative exactly
when the unresolved element classes satisfy the image condition. -/
theorem every_rightSchutzenberger_class_has_principalRepresentative_of_imageCondition
    (G : Semigroup S) (z : S)
    (imageCondition : G.RightSchutzenbergerImageCondition z)
    (c : (rightSchutzenbergerCongruence G z).Quotient) :
    ∃ y, G.PrincipalSandwichMem z y ∧
      (rightSchutzenbergerCongruence G z).classOf y = c := by
  refine _root_.Quotient.inductionOn c ?_
  intro x
  rcases exists_principalSandwich_rightSchutzenbergerRel_of_imageCondition
      G z x imageCondition with ⟨y, hy, hxy⟩
  refine ⟨y, hy, ?_⟩
  exact ((rightSchutzenberger_classOf_eq_iff G z).2 hxy).symm

/-- Every quotient class has a representative in `S z S`, conditional only
on the explicit uniformization premise. -/
theorem BrandtLaws.every_rightSchutzenberger_class_has_principalRepresentative
    {G : Semigroup S} {z : S} (laws : G.BrandtLaws)
    (hz : G.IsRegular z) (uniform : G.RightSchutzenbergerImageUniformity z)
    (c : (rightSchutzenbergerCongruence G z).Quotient) :
    ∃ y, G.PrincipalSandwichMem z y ∧
      (rightSchutzenbergerCongruence G z).classOf y = c := by
  exact every_rightSchutzenberger_class_has_principalRepresentative_of_imageCondition
    G z (laws.rightSchutzenbergerImageCondition_of_uniformity hz uniform) c

/-- The restriction of the quotient map to the principal sandwich. -/
def principalSandwichClassOf (G : Semigroup S) (z : S) :
    {x : S // G.PrincipalSandwichMem z x} →
      (rightSchutzenbergerCongruence G z).Quotient :=
  fun x => (rightSchutzenbergerCongruence G z).classOf x.1

theorem principalSandwichClassOf_surjective_of_imageCondition
    (G : Semigroup S) (z : S)
    (imageCondition : G.RightSchutzenbergerImageCondition z) :
    Function.Surjective (principalSandwichClassOf G z) := by
  intro c
  rcases every_rightSchutzenberger_class_has_principalRepresentative_of_imageCondition
      G z imageCondition c with ⟨y, hy, hclass⟩
  exact ⟨⟨y, hy⟩, hclass⟩

/-- `RightSchutzenbergerImageCondition` is necessary and sufficient for the
restricted quotient map to be onto. -/
theorem principalSandwichClassOf_surjective_iff_imageCondition
    (G : Semigroup S) (z : S) :
    Function.Surjective (principalSandwichClassOf G z) ↔
      G.RightSchutzenbergerImageCondition z := by
  constructor
  · intro surjective x _ _
    rcases surjective ((rightSchutzenbergerCongruence G z).classOf x) with
      ⟨y, hy⟩
    refine ⟨y.1, y.2, ?_⟩
    apply rightSchutzenbergerRel_symm G z
    apply (rightSchutzenberger_classOf_eq_iff G z).1
    change
      (rightSchutzenbergerCongruence G z).classOf y.1 =
        (rightSchutzenbergerCongruence G z).classOf x at hy
    exact hy
  · intro imageCondition
    exact principalSandwichClassOf_surjective_of_imageCondition G z imageCondition

theorem BrandtLaws.principalSandwichClassOf_surjective
    {G : Semigroup S} {z : S} (laws : G.BrandtLaws)
    (hz : G.IsRegular z) (uniform : G.RightSchutzenbergerImageUniformity z) :
    Function.Surjective (principalSandwichClassOf G z) := by
  exact principalSandwichClassOf_surjective_of_imageCondition G z
    (laws.rightSchutzenbergerImageCondition_of_uniformity hz uniform)

end Semigroup
end SemigroupBasis

import SemigroupBasis.Transfer

namespace SemigroupBasis

namespace Semigroup

def pi (G : Semigroup S) (I : Type v) : Semigroup (I → S) where
  mul := fun a b i => G.mul (a i) (b i)
  assoc := by
    intro a b c
    funext i
    exact G.assoc (a i) (b i) (c i)

end Semigroup

namespace Hom

def piProjection (G : Semigroup S) (I : Type v) (i : I) :
    Hom (G.pi I) G where
  toFun := fun value => value i
  map_mul := by intros; rfl

/-- The homomorphism into a direct power assembled coordinatewise from a family. -/
def diagonal {A : Type u} {B : Type v} {I : Type w}
    {G : Semigroup A} {H : Semigroup B}
    (family : I → Hom G H) : Hom G (H.pi I) where
  toFun := fun value i => (family i).toFun value
  map_mul := by
    intro a b
    funext i
    exact (family i).map_mul a b

end Hom

namespace Embedding

/-- A separating family of homomorphisms embeds its source in a direct power. -/
def ofSeparatingHoms {A : Type u} {B : Type v} {I : Type w}
    {G : Semigroup A} {H : Semigroup B}
    (family : I → Hom G H)
    (separates :
      ∀ x y, (∀ i, (family i).toFun x = (family i).toFun y) → x = y) :
    Embedding G (H.pi I) where
  toFun := (Hom.diagonal family).toFun
  map_mul := (Hom.diagonal family).map_mul
  injective := by
    intro x y equalImages
    apply separates x y
    intro i
    exact congrFun equalImages i

end Embedding

namespace Identity

theorem satisfiedByPi (e : Identity α) (G : Semigroup S) (I : Type v)
    (h : e.SatisfiedBy G) : e.SatisfiedBy (G.pi I) := by
  intro valuation
  funext i
  have lhsMap := (Hom.piProjection G I i).map_eval valuation e.lhs
  have rhsMap := (Hom.piProjection G I i).map_eval valuation e.rhs
  exact lhsMap.trans
    ((h (fun x => valuation x i)).trans rhsMap.symm)

end Identity

/-- A homomorphism with a recorded right-inverse, avoiding an external choice step. -/
structure SplitSurjection {A : Type u} {B : Type v}
    (G : Semigroup A) (H : Semigroup B)
    extends Hom G H where
  preimage : B → A
  right_inverse : ∀ b, toFun (preimage b) = b

namespace SplitSurjection

theorem pushforwardIdentity {A : Type u} {B : Type v} {α : Type w}
    {G : Semigroup A} {H : Semigroup B}
    (f : SplitSurjection G H) (e : Identity α)
    (h : e.SatisfiedBy G) : e.SatisfiedBy H := by
  intro valuation
  let lifted : α → A := fun x => f.preimage (valuation x)
  have valuationEq : (fun x => f.toFun (lifted x)) = valuation := by
    funext x
    exact f.right_inverse (valuation x)
  have lhsMap := f.toHom.map_eval lifted e.lhs
  have rhsMap := f.toHom.map_eval lifted e.rhs
  rw [valuationEq] at lhsMap rhsMap
  exact lhsMap.symm.trans
    ((congrArg f.toFun (h lifted)).trans rhsMap)

end SplitSurjection

/-- A source embedded in a direct power of the target gives the reverse identity inclusion. -/
theorem BasisFor.inheritAlongPowerEmbedding
    {A : Type u} {B : Type v} {I : Type w} {α : Type z}
    {source : Semigroup A} {target : Semigroup B}
    {basis : List (Identity α)}
    (sourceBasis : BasisFor source basis)
    (embedding : Embedding source (target.pi I))
    (targetModels : Models target basis) :
    BasisFor target basis := by
  refine ⟨targetModels, ?_⟩
  intro e targetValid
  have powerValid := e.satisfiedByPi target I targetValid
  exact sourceBasis.2 e (embedding.pullback_identity e powerValid)

/-- A quotient of a subsemigroup supplies the reverse identity inclusion. -/
theorem BasisFor.inheritAlongSubsemigroupQuotient
    {A : Type u} {B : Type v} {U : Type w} {α : Type z}
    {source : Semigroup A} {target : Semigroup B} {sub : Semigroup U}
    {basis : List (Identity α)}
    (sourceBasis : BasisFor source basis)
    (subEmbedding : Embedding sub target)
    (quotient : SplitSurjection sub source)
    (targetModels : Models target basis) :
    BasisFor target basis := by
  refine ⟨targetModels, ?_⟩
  intro e targetValid
  have subValid := subEmbedding.pullback_identity e targetValid
  have sourceValid := quotient.pushforwardIdentity e subValid
  exact sourceBasis.2 e sourceValid

/-- A source divisor of a direct power of the target supplies the reverse inclusion. -/
theorem BasisFor.inheritAlongPowerDivisor
    {A : Type u} {B : Type v} {U : Type w} {I : Type z}
    {α : Type q} {source : Semigroup A} {target : Semigroup B}
    {sub : Semigroup U} {basis : List (Identity α)}
    (sourceBasis : BasisFor source basis)
    (subEmbedding : Embedding sub (target.pi I))
    (quotient : SplitSurjection sub source)
    (targetModels : Models target basis) :
    BasisFor target basis := by
  refine ⟨targetModels, ?_⟩
  intro e targetValid
  have powerValid := e.satisfiedByPi target I targetValid
  have subValid := subEmbedding.pullback_identity e powerValid
  have sourceValid := quotient.pushforwardIdentity e subValid
  exact sourceBasis.2 e sourceValid

end SemigroupBasis

import SemigroupBasis.Inflation

namespace SemigroupBasis

/-- Every identity in the basis has a genuine product on both sides. -/
def ProductSidedBasis (basis : List (Identity α)) : Prop :=
  ∀ identity, identity ∈ basis →
    identity.lhs.tail ≠ [] ∧ identity.rhs.tail ≠ []

namespace Inflation

/--
A product-sided basis valid in the embedded source is also valid in the
inflation.
-/
theorem modelsProductSidedBasis
    {A : Type u} {B : Type v} {α : Type w}
    {source : Semigroup A} {target : Semigroup B}
    (inflation : Inflation source target)
    {basis : List (Identity α)}
    (productSided : ProductSidedBasis basis)
    (sourceModels : Models source basis) :
    Models target basis := by
  intro identity member
  exact inflation.pushforwardProductIdentity identity
    (productSided identity member).1
    (productSided identity member).2
    (sourceModels identity member)

/--
Sufficient one-fiber-inflation transfer theorem used by the order-seven
proposal: a complete source basis transfers unchanged when all of its
identities have length at least two on both sides.
-/
theorem inheritProductSidedBasis
    {A : Type u} {B : Type v} {α : Type w}
    {source : Semigroup A} {target : Semigroup B}
    (inflation : Inflation source target)
    {basis : List (Identity α)}
    (sourceBasis : BasisFor source basis)
    (productSided : ProductSidedBasis basis) :
    BasisFor target basis :=
  sourceBasis.inheritAlongEmbedding inflation.embedding
    (inflation.modelsProductSidedBasis productSided sourceBasis.1)

end Inflation

end SemigroupBasis

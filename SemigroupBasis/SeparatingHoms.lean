import SemigroupBasis.TransferPower

namespace SemigroupBasis

namespace Embedding

/-- A point-separating family of homomorphisms gives the diagonal embedding
into the corresponding direct power. -/
def embeddingOfSeparatingHoms
    {A : Type u} {B : Type v} {I : Type w}
    {G : Semigroup A} {H : Semigroup B}
    (family : I -> Hom G H)
    (separates :
      forall x y,
        (forall i, (family i).toFun x = (family i).toFun y) ->
          x = y) :
    Embedding G (H.pi I) := by
  refine
    { toFun := fun x i => (family i).toFun x
      map_mul := ?_
      injective := ?_ }
  · intro x y
    funext i
    exact (family i).map_mul x y
  · intro x y hxy
    apply separates x y
    intro i
    exact congrFun hxy i

end Embedding

end SemigroupBasis

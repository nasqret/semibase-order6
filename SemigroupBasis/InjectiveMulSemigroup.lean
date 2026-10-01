import SemigroupBasis.Transfer

namespace SemigroupBasis

/-- Data showing that a binary operation embeds multiplicatively and injectively
into a semigroup. -/
structure InjectiveMulSemigroup {A : Type u} {B : Type v}
    (mulA : A -> A -> A) (target : Semigroup B) where
  toFun : A -> B
  injective : Function.Injective toFun
  map_mul : forall a b, toFun (mulA a b) = target.mul (toFun a) (toFun b)

namespace InjectiveMulSemigroup

/-- Pull associativity back from the target along the injective map. -/
def semigroup {A : Type u} {B : Type v} {mulA : A -> A -> A}
    {target : Semigroup B}
    (certificate : InjectiveMulSemigroup mulA target) : Semigroup A where
  mul := mulA
  assoc := by
    intro a b c
    apply certificate.injective
    calc
      certificate.toFun (mulA (mulA a b) c) =
          target.mul (certificate.toFun (mulA a b)) (certificate.toFun c) :=
        certificate.map_mul _ _
      _ = target.mul
          (target.mul (certificate.toFun a) (certificate.toFun b))
          (certificate.toFun c) := by
        rw [certificate.map_mul]
      _ = target.mul (certificate.toFun a)
          (target.mul (certificate.toFun b) (certificate.toFun c)) :=
        target.assoc _ _ _
      _ = target.mul (certificate.toFun a)
          (certificate.toFun (mulA b c)) := by
        rw [certificate.map_mul]
      _ = certificate.toFun (mulA a (mulA b c)) :=
        (certificate.map_mul _ _).symm

@[simp]
theorem semigroup_mul {A : Type u} {B : Type v} {mulA : A -> A -> A}
    {target : Semigroup B}
    (certificate : InjectiveMulSemigroup mulA target) (a b : A) :
    certificate.semigroup.mul a b = mulA a b :=
  rfl

/-- The embedding supplied by the same certificate used to build the source. -/
def embedding {A : Type u} {B : Type v} {mulA : A -> A -> A}
    {target : Semigroup B}
    (certificate : InjectiveMulSemigroup mulA target) :
    Embedding certificate.semigroup target where
  toFun := certificate.toFun
  map_mul := certificate.map_mul
  injective := certificate.injective

end InjectiveMulSemigroup

end SemigroupBasis

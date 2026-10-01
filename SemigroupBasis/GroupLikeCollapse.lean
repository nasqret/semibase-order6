import SemigroupBasis.BrandtLaws

namespace SemigroupBasis
namespace Semigroup

/-- The pointwise semigroup law `x^2 = x^3`. -/
def SquareEqualsCube (G : Semigroup S) : Prop :=
  ∀ x, G.mul x x = G.mul (G.mul x x) x

/-- Group data on an explicitly supplied semigroup. This deliberately avoids
the external algebra hierarchy so it can also describe an abstract structure
subsemigroup represented by an `Embedding`. -/
structure GroupLike (G : Semigroup S) where
  one : S
  inv : S → S
  one_mul : ∀ x, G.mul one x = x
  mul_one : ∀ x, G.mul x one = x
  inv_mul : ∀ x, G.mul (inv x) x = one
  mul_inv : ∀ x, G.mul x (inv x) = one

theorem BrandtLaws.squareEqualsCube {G : Semigroup S}
    (laws : G.BrandtLaws) : G.SquareEqualsCube :=
  laws.square_eq_cube

namespace GroupLike

theorem mul_left_cancel {G : Semigroup S} (K : G.GroupLike)
    {a b c : S} (h : G.mul a b = G.mul a c) : b = c := by
  calc
    b = G.mul K.one b := (K.one_mul b).symm
    _ = G.mul (G.mul (K.inv a) a) b := by
      rw [K.inv_mul]
    _ = G.mul (K.inv a) (G.mul a b) := G.assoc _ _ _
    _ = G.mul (K.inv a) (G.mul a c) :=
      congrArg (fun product => G.mul (K.inv a) product) h
    _ = G.mul (G.mul (K.inv a) a) c := (G.assoc _ _ _).symm
    _ = G.mul K.one c := by
      rw [K.inv_mul]
    _ = c := K.one_mul c

theorem mul_right_cancel {G : Semigroup S} (K : G.GroupLike)
    {a b c : S} (h : G.mul b a = G.mul c a) : b = c := by
  calc
    b = G.mul b K.one := (K.mul_one b).symm
    _ = G.mul b (G.mul a (K.inv a)) := by
      rw [K.mul_inv]
    _ = G.mul (G.mul b a) (K.inv a) := (G.assoc _ _ _).symm
    _ = G.mul (G.mul c a) (K.inv a) :=
      congrArg (fun product => G.mul product (K.inv a)) h
    _ = G.mul c (G.mul a (K.inv a)) := G.assoc _ _ _
    _ = G.mul c K.one := by
      rw [K.mul_inv]
    _ = c := K.mul_one c

/-- In a group-like semigroup, `x^2 = x^3` first makes every element
idempotent and cancellation then identifies it with the identity. -/
theorem eq_one_of_square_eq_cube {G : Semigroup S} (K : G.GroupLike)
    (law : G.SquareEqualsCube) (x : S) : x = K.one := by
  have idempotent : x = G.mul x x :=
    K.mul_left_cancel (a := x) <| by
      calc
        G.mul x x = G.mul (G.mul x x) x := law x
        _ = G.mul x (G.mul x x) := G.assoc x x x
  exact K.mul_left_cancel (a := x) <| by
    calc
      G.mul x x = x := idempotent.symm
      _ = G.mul x K.one := (K.mul_one x).symm

theorem subsingleton_of_square_eq_cube {G : Semigroup S}
    (K : G.GroupLike) (law : G.SquareEqualsCube) : Subsingleton S :=
  ⟨fun a b =>
    (K.eq_one_of_square_eq_cube law a).trans
      (K.eq_one_of_square_eq_cube law b).symm⟩

/-- Cancellation remains valid after applying any semigroup homomorphism out
of a group-like semigroup, even when that homomorphism is not injective. -/
theorem hom_mul_left_cancel {G : Semigroup A} {H : Semigroup B}
    (K : G.GroupLike) (f : Hom G H) {a b c : A}
    (h : H.mul (f.toFun a) (f.toFun b) =
      H.mul (f.toFun a) (f.toFun c)) :
    f.toFun b = f.toFun c := by
  calc
    f.toFun b = H.mul (f.toFun K.one) (f.toFun b) := by
      rw [← f.map_mul K.one b, K.one_mul]
    _ = H.mul
        (H.mul (f.toFun (K.inv a)) (f.toFun a))
        (f.toFun b) := by
      rw [← f.map_mul (K.inv a) a, K.inv_mul]
    _ = H.mul (f.toFun (K.inv a))
        (H.mul (f.toFun a) (f.toFun b)) := H.assoc _ _ _
    _ = H.mul (f.toFun (K.inv a))
        (H.mul (f.toFun a) (f.toFun c)) :=
      congrArg (fun product => H.mul (f.toFun (K.inv a)) product) h
    _ = H.mul
        (H.mul (f.toFun (K.inv a)) (f.toFun a))
        (f.toFun c) := (H.assoc _ _ _).symm
    _ = H.mul (f.toFun K.one) (f.toFun c) := by
      rw [← f.map_mul (K.inv a) a, K.inv_mul]
    _ = f.toFun c := by
      rw [← f.map_mul K.one c, K.one_mul]

/-- Every homomorphism from a group-like semigroup into an `x^2 = x^3`
semigroup sends each element to the image of the identity. -/
theorem hom_eq_map_one_of_square_eq_cube
    {G : Semigroup A} {H : Semigroup B}
    (K : G.GroupLike) (f : Hom G H) (law : H.SquareEqualsCube) (x : A) :
    f.toFun x = f.toFun K.one := by
  have imageIdempotent : f.toFun x = f.toFun (G.mul x x) :=
    K.hom_mul_left_cancel f (a := x) <| by
      calc
        H.mul (f.toFun x) (f.toFun x) =
            H.mul
              (H.mul (f.toFun x) (f.toFun x))
              (f.toFun x) := law (f.toFun x)
        _ = H.mul (f.toFun x)
            (H.mul (f.toFun x) (f.toFun x)) :=
          H.assoc _ _ _
        _ = H.mul (f.toFun x) (f.toFun (G.mul x x)) :=
          congrArg (fun product => H.mul (f.toFun x) product)
            (f.map_mul x x).symm
  exact K.hom_mul_left_cancel f (a := x) <| by
    calc
      H.mul (f.toFun x) (f.toFun x) = f.toFun (G.mul x x) :=
        (f.map_mul x x).symm
      _ = f.toFun x := imageIdempotent.symm
      _ = f.toFun (G.mul x K.one) :=
        congrArg f.toFun (K.mul_one x).symm
      _ = H.mul (f.toFun x) (f.toFun K.one) :=
        f.map_mul x K.one

theorem hom_apply_eq_apply_of_square_eq_cube
    {G : Semigroup A} {H : Semigroup B}
    (K : G.GroupLike) (f : Hom G H) (law : H.SquareEqualsCube)
    (a b : A) : f.toFun a = f.toFun b :=
  (K.hom_eq_map_one_of_square_eq_cube f law a).trans
    (K.hom_eq_map_one_of_square_eq_cube f law b).symm

theorem subsingleton_of_injective_hom
    {G : Semigroup A} {H : Semigroup B}
    (K : G.GroupLike) (f : Hom G H) (injective : Function.Injective f.toFun)
    (law : H.SquareEqualsCube) : Subsingleton A := by
  refine ⟨?_⟩
  intro a b
  apply injective
  exact K.hom_apply_eq_apply_of_square_eq_cube f law a b

/-- Subsemigroup-facing form: if a group-like semigroup embeds into an
`x^2 = x^3` semigroup, its carrier is a subsingleton. -/
theorem subsingleton_of_subsemigroup_embedding
    {G : Semigroup A} {H : Semigroup B}
    (K : G.GroupLike) (inclusion : Embedding G H)
    (law : H.SquareEqualsCube) : Subsingleton A :=
  K.subsingleton_of_injective_hom inclusion.toHom inclusion.injective law

theorem eq_one_of_brandtLaws {G : Semigroup S} (K : G.GroupLike)
    (laws : G.BrandtLaws) (x : S) : x = K.one :=
  K.eq_one_of_square_eq_cube laws.squareEqualsCube x

theorem subsingleton_of_brandtLaws {G : Semigroup S} (K : G.GroupLike)
    (laws : G.BrandtLaws) : Subsingleton S :=
  K.subsingleton_of_square_eq_cube laws.squareEqualsCube

theorem hom_eq_map_one_of_brandtLaws
    {G : Semigroup A} {H : Semigroup B}
    (K : G.GroupLike) (f : Hom G H) (laws : H.BrandtLaws) (x : A) :
    f.toFun x = f.toFun K.one :=
  K.hom_eq_map_one_of_square_eq_cube f laws.squareEqualsCube x

theorem hom_apply_eq_apply_of_brandtLaws
    {G : Semigroup A} {H : Semigroup B}
    (K : G.GroupLike) (f : Hom G H) (laws : H.BrandtLaws) (a b : A) :
    f.toFun a = f.toFun b :=
  K.hom_apply_eq_apply_of_square_eq_cube f laws.squareEqualsCube a b

/-- Structure-group reduction specialized to the laws available in the
`S5_415` term model and its quotients. -/
theorem subsingleton_of_subsemigroup_brandtLaws
    {G : Semigroup A} {H : Semigroup B}
    (K : G.GroupLike) (inclusion : Embedding G H)
    (laws : H.BrandtLaws) : Subsingleton A :=
  K.subsingleton_of_subsemigroup_embedding
    inclusion laws.squareEqualsCube

end GroupLike
end Semigroup

namespace Embedding

/-- The square-cube law restricts along a semigroup embedding. -/
theorem pullback_squareEqualsCube
    {G : Semigroup A} {H : Semigroup B}
    (f : Embedding G H) (law : H.SquareEqualsCube) : G.SquareEqualsCube := by
  intro x
  apply f.injective
  calc
    f.toFun (G.mul x x) = H.mul (f.toFun x) (f.toFun x) :=
      f.map_mul x x
    _ = H.mul (H.mul (f.toFun x) (f.toFun x)) (f.toFun x) :=
      law (f.toFun x)
    _ = H.mul (f.toFun (G.mul x x)) (f.toFun x) :=
      congrArg (fun product => H.mul product (f.toFun x))
        (f.map_mul x x).symm
    _ = f.toFun (G.mul (G.mul x x) x) :=
      (f.map_mul (G.mul x x) x).symm

end Embedding
end SemigroupBasis

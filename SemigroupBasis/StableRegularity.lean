import SemigroupBasis.GroupLikeCollapse
import SemigroupBasis.Ideal

namespace SemigroupBasis
namespace Semigroup

/-- In an `x^2 = x^3` semigroup, an element cannot be a proper two-sided
contraction of itself: if `a = p * a * q`, then both outside factors already
stabilize `a` on their respective sides. -/
theorem SquareEqualsCube.absorb_factors_of_eq_sandwich
    {G : Semigroup S} (law : G.SquareEqualsCube) {a p q : S}
    (sandwich : a = G.mul (G.mul p a) q) :
    G.mul p a = a ∧ G.mul a q = a := by
  have iterated :
      a = G.mul (G.mul (G.mul p p) a) (G.mul q q) := by
    calc
      a = G.mul (G.mul p a) q := sandwich
      _ = G.mul (G.mul p (G.mul (G.mul p a) q)) q :=
        congrArg (fun x => G.mul (G.mul p x) q) sandwich
      _ = G.mul (G.mul (G.mul p p) a) (G.mul q q) := by
        simp only [G.assoc]
  constructor
  · calc
      G.mul p a =
          G.mul p (G.mul (G.mul (G.mul p p) a) (G.mul q q)) :=
        congrArg (fun x => G.mul p x) iterated
      _ = G.mul
          (G.mul (G.mul (G.mul p p) p) a) (G.mul q q) := by
        simp only [G.assoc]
      _ = G.mul (G.mul (G.mul p p) a) (G.mul q q) := by
        rw [← law p]
      _ = a := iterated.symm
  · calc
      G.mul a q =
          G.mul (G.mul (G.mul (G.mul p p) a) (G.mul q q)) q :=
        congrArg (fun x => G.mul x q) iterated
      _ = G.mul (G.mul (G.mul p p) a)
          (G.mul (G.mul q q) q) := by
        simp only [G.assoc]
      _ = G.mul (G.mul (G.mul p p) a) (G.mul q q) := by
        rw [← law q]
      _ = a := iterated.symm

/-- Explicit inverse transfer across a stable `L`/`R` bridge.

The chosen factorizations make `b = p * z` into a bridge: stability gives
`b = a * s` and `z = r * b`. If `zInv` is an inverse of `z`, then
`zInv * r` is an inverse of `b`, and `s * (zInv * r)` is an inverse of `a`. -/
theorem SquareEqualsCube.isInverse_of_mutual_sandwich_witnesses
    {G : Semigroup S} (law : G.SquareEqualsCube)
    {a z p q r s zInv : S}
    (a_factor : a = G.mul (G.mul p z) q)
    (z_factor : z = G.mul (G.mul r a) s)
    (z_inverse : G.IsInverse z zInv) :
    G.IsInverse a (G.mul s (G.mul zInv r)) := by
  have a_self_sandwich :
      a = G.mul (G.mul (G.mul p r) a) (G.mul s q) := by
    calc
      a = G.mul (G.mul p z) q := a_factor
      _ = G.mul (G.mul p (G.mul (G.mul r a) s)) q := by
        rw [z_factor]
      _ = G.mul (G.mul (G.mul p r) a) (G.mul s q) := by
        simp only [G.assoc]
  have z_self_sandwich :
      z = G.mul (G.mul (G.mul r p) z) (G.mul q s) := by
    calc
      z = G.mul (G.mul r a) s := z_factor
      _ = G.mul (G.mul r (G.mul (G.mul p z) q)) s := by
        rw [a_factor]
      _ = G.mul (G.mul (G.mul r p) z) (G.mul q s) := by
        simp only [G.assoc]
  have left_stabilizes_a : G.mul (G.mul p r) a = a :=
    (law.absorb_factors_of_eq_sandwich a_self_sandwich).1
  have left_stabilizes_z : G.mul (G.mul r p) z = z :=
    (law.absorb_factors_of_eq_sandwich z_self_sandwich).1
  have bridge_from_a : G.mul p z = G.mul a s := by
    calc
      G.mul p z = G.mul p (G.mul (G.mul r a) s) := by
        rw [z_factor]
      _ = G.mul (G.mul (G.mul p r) a) s := by
        simp only [G.assoc]
      _ = G.mul a s :=
        congrArg (fun x => G.mul x s) left_stabilizes_a
  have z_from_bridge : z = G.mul r (G.mul p z) := by
    calc
      z = G.mul (G.mul r p) z := left_stabilizes_z.symm
      _ = G.mul r (G.mul p z) := G.assoc r p z
  have bridge_inverse :
      G.IsInverse (G.mul p z) (G.mul zInv r) := by
    constructor
    · calc
        G.mul
            (G.mul (G.mul p z) (G.mul zInv r))
            (G.mul p z) =
            G.mul p
              (G.mul (G.mul z zInv) (G.mul r (G.mul p z))) := by
          simp only [G.assoc]
        _ = G.mul p (G.mul (G.mul z zInv) z) := by
          rw [← z_from_bridge]
        _ = G.mul p z := by
          rw [z_inverse.1]
    · calc
        G.mul
            (G.mul (G.mul zInv r) (G.mul p z))
            (G.mul zInv r) =
            G.mul
              (G.mul
                (G.mul zInv (G.mul r (G.mul p z))) zInv)
              r := by
          simp only [G.assoc]
        _ = G.mul (G.mul (G.mul zInv z) zInv) r := by
          rw [← z_from_bridge]
        _ = G.mul zInv r := by
          rw [z_inverse.2]
  constructor
  · calc
      G.mul (G.mul a (G.mul s (G.mul zInv r))) a =
          G.mul (G.mul (G.mul a s) (G.mul zInv r)) a := by
        simp only [G.assoc]
      _ = G.mul
          (G.mul (G.mul p z) (G.mul zInv r)) a := by
        rw [← bridge_from_a]
      _ = G.mul
          (G.mul
            (G.mul (G.mul p z) (G.mul zInv r))
            (G.mul p z)) q := by
        rw [a_factor]
        simp only [G.assoc]
      _ = G.mul (G.mul p z) q := by
        rw [bridge_inverse.1]
      _ = a := a_factor.symm
  · calc
      G.mul
          (G.mul (G.mul s (G.mul zInv r)) a)
          (G.mul s (G.mul zInv r)) =
          G.mul s
            (G.mul
              (G.mul (G.mul zInv r) (G.mul a s))
              (G.mul zInv r)) := by
        simp only [G.assoc]
      _ = G.mul s
          (G.mul
            (G.mul (G.mul zInv r) (G.mul p z))
            (G.mul zInv r)) := by
        rw [← bridge_from_a]
      _ = G.mul s (G.mul zInv r) := by
        rw [bridge_inverse.2]

/-- Regularity is constant on a mutual principal-sandwich class in every
semigroup satisfying `x^2 = x^3`. -/
theorem SquareEqualsCube.isRegular_of_mutual_principalSandwichMem
    {G : Semigroup S} (law : G.SquareEqualsCube) {a z : S}
    (a_mem : G.PrincipalSandwichMem z a)
    (z_mem : G.PrincipalSandwichMem a z)
    (z_regular : G.IsRegular z) :
    G.IsRegular a := by
  rcases a_mem with ⟨p, q, a_factor⟩
  rcases z_mem with ⟨r, s, z_factor⟩
  rcases z_regular with ⟨zInv, z_inverse⟩
  exact ⟨G.mul s (G.mul zInv r),
    law.isInverse_of_mutual_sandwich_witnesses
      a_factor z_factor z_inverse⟩

end Semigroup
end SemigroupBasis

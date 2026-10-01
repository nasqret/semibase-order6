import SemigroupBasis.Transfer

namespace SemigroupBasis
namespace Semigroup

/-- An element is idempotent when multiplying it by itself does not change it. -/
def IsIdempotent (G : Semigroup S) (a : S) : Prop :=
  G.mul a a = a

/-- `b` is an inverse of `a` when both sandwich identities hold. -/
def IsInverse (G : Semigroup S) (a b : S) : Prop :=
  G.mul (G.mul a b) a = a ∧
    G.mul (G.mul b a) b = b

/-- An element is regular when it has an inverse witness. -/
def IsRegular (G : Semigroup S) (a : S) : Prop :=
  ∃ aInv, G.IsInverse a aInv

/-- Every element of the semigroup is regular. -/
def RegularSemigroup (G : Semigroup S) : Prop :=
  ∀ a, G.IsRegular a

/-- Every pair of idempotents commutes. -/
def IdempotentsCommute (G : Semigroup S) : Prop :=
  ∀ {a b}, G.IsIdempotent a → G.IsIdempotent b →
    G.mul a b = G.mul b a

theorem IsInverse.symm {G : Semigroup S} {a b : S}
    (h : G.IsInverse a b) : G.IsInverse b a :=
  ⟨h.2, h.1⟩

theorem IsInverse.mul_idempotent {G : Semigroup S} {a b : S}
    (h : G.IsInverse a b) : G.IsIdempotent (G.mul a b) := by
  unfold IsIdempotent
  rw [← G.assoc (G.mul a b) a b, h.1]

theorem IsInverse.reverse_mul_idempotent
    {G : Semigroup S} {a b : S} (h : G.IsInverse a b) :
    G.IsIdempotent (G.mul b a) :=
  IsInverse.mul_idempotent h.symm

/-- With commuting idempotents, chosen inverses multiply in reverse order. -/
theorem IdempotentsCommute.mul_inverse
    {G : Semigroup S} {a aInv b bInv : S}
    (commute : G.IdempotentsCommute)
    (ha : G.IsInverse a aInv) (hb : G.IsInverse b bInv) :
    G.IsInverse (G.mul a b) (G.mul bInv aInv) := by
  have commuteMiddle :
      G.mul (G.mul b bInv) (G.mul aInv a) =
        G.mul (G.mul aInv a) (G.mul b bInv) :=
    commute hb.mul_idempotent ha.reverse_mul_idempotent
  constructor
  · calc
      G.mul (G.mul (G.mul a b) (G.mul bInv aInv)) (G.mul a b) =
          G.mul a
            (G.mul (G.mul (G.mul b bInv) (G.mul aInv a)) b) := by
        simp only [G.assoc]
      _ = G.mul a
            (G.mul (G.mul (G.mul aInv a) (G.mul b bInv)) b) := by
        exact congrArg (fun middle => G.mul a (G.mul middle b)) commuteMiddle
      _ = G.mul (G.mul (G.mul a aInv) a)
            (G.mul (G.mul b bInv) b) := by
        simp only [G.assoc]
      _ = G.mul a b := by rw [ha.1, hb.1]
  · calc
      G.mul (G.mul (G.mul bInv aInv) (G.mul a b))
          (G.mul bInv aInv) =
          G.mul bInv
            (G.mul (G.mul (G.mul aInv a) (G.mul b bInv)) aInv) := by
        simp only [G.assoc]
      _ = G.mul bInv
            (G.mul (G.mul (G.mul b bInv) (G.mul aInv a)) aInv) := by
        exact congrArg (fun middle => G.mul bInv (G.mul middle aInv))
          commuteMiddle.symm
      _ = G.mul (G.mul (G.mul bInv b) bInv)
            (G.mul (G.mul aInv a) aInv) := by
        simp only [G.assoc]
      _ = G.mul bInv aInv := by rw [hb.2, ha.2]

end Semigroup

namespace Hom

theorem map_isIdempotent {G : Semigroup A} {H : Semigroup B}
    (f : Hom G H) {a : A} (ha : G.IsIdempotent a) :
    H.IsIdempotent (f.toFun a) := by
  calc
    H.mul (f.toFun a) (f.toFun a) = f.toFun (G.mul a a) :=
      (f.map_mul a a).symm
    _ = f.toFun a := congrArg f.toFun ha

theorem map_isInverse {G : Semigroup A} {H : Semigroup B}
    (f : Hom G H) {a aInv : A} (ha : G.IsInverse a aInv) :
    H.IsInverse (f.toFun a) (f.toFun aInv) := by
  constructor
  · calc
      H.mul (H.mul (f.toFun a) (f.toFun aInv)) (f.toFun a) =
          H.mul (f.toFun (G.mul a aInv)) (f.toFun a) :=
        congrArg (fun x => H.mul x (f.toFun a)) (f.map_mul a aInv).symm
      _ = f.toFun (G.mul (G.mul a aInv) a) :=
        (f.map_mul (G.mul a aInv) a).symm
      _ = f.toFun a := congrArg f.toFun ha.1
  · calc
      H.mul (H.mul (f.toFun aInv) (f.toFun a)) (f.toFun aInv) =
          H.mul (f.toFun (G.mul aInv a)) (f.toFun aInv) :=
        congrArg (fun x => H.mul x (f.toFun aInv))
          (f.map_mul aInv a).symm
      _ = f.toFun (G.mul (G.mul aInv a) aInv) :=
        (f.map_mul (G.mul aInv a) aInv).symm
      _ = f.toFun aInv := congrArg f.toFun ha.2

theorem map_isRegular {G : Semigroup A} {H : Semigroup B}
    (f : Hom G H) {a : A} (ha : G.IsRegular a) :
    H.IsRegular (f.toFun a) := by
  rcases ha with ⟨aInv, inverse⟩
  exact ⟨f.toFun aInv, f.map_isInverse inverse⟩

end Hom
end SemigroupBasis

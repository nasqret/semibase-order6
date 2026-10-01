import SemigroupBasis.Regular

namespace SemigroupBasis
namespace Semigroup

/-- A regular semigroup whose idempotents commute. -/
def IsInverseSemigroup (G : Semigroup S) : Prop :=
  G.RegularSemigroup ∧ G.IdempotentsCommute

theorem IsInverseSemigroup.regularSemigroup {G : Semigroup S}
    (inverseSemigroup : G.IsInverseSemigroup) : G.RegularSemigroup :=
  inverseSemigroup.1

theorem IsInverseSemigroup.idempotentsCommute {G : Semigroup S}
    (inverseSemigroup : G.IsInverseSemigroup) : G.IdempotentsCommute :=
  inverseSemigroup.2

/-- In a semigroup with commuting idempotents, an element has at most one
inverse witness. -/
theorem IdempotentsCommute.inverse_unique
    {G : Semigroup S} (commute : G.IdempotentsCommute)
    {a b c : S} (hb : G.IsInverse a b) (hc : G.IsInverse a c) :
    b = c := by
  have b_eq_cab : b = G.mul (G.mul c a) b := by
    calc
      b = G.mul (G.mul b a) b := hb.2.symm
      _ = G.mul (G.mul b (G.mul (G.mul a c) a)) b := by
        rw [hc.1]
      _ = G.mul (G.mul (G.mul b a) (G.mul c a)) b := by
        simp only [G.assoc]
      _ = G.mul (G.mul (G.mul c a) (G.mul b a)) b :=
        congrArg (fun product => G.mul product b)
          (commute hb.reverse_mul_idempotent hc.reverse_mul_idempotent)
      _ = G.mul (G.mul c a) (G.mul (G.mul b a) b) :=
        G.assoc (G.mul c a) (G.mul b a) b
      _ = G.mul (G.mul c a) b :=
        congrArg (fun product => G.mul (G.mul c a) product) hb.2
  have c_eq_bac : c = G.mul (G.mul b a) c := by
    calc
      c = G.mul (G.mul c a) c := hc.2.symm
      _ = G.mul (G.mul c (G.mul (G.mul a b) a)) c := by
        rw [hb.1]
      _ = G.mul (G.mul (G.mul c a) (G.mul b a)) c := by
        simp only [G.assoc]
      _ = G.mul (G.mul (G.mul b a) (G.mul c a)) c :=
        congrArg (fun product => G.mul product c)
          (commute hc.reverse_mul_idempotent hb.reverse_mul_idempotent)
      _ = G.mul (G.mul b a) (G.mul (G.mul c a) c) :=
        G.assoc (G.mul b a) (G.mul c a) c
      _ = G.mul (G.mul b a) c :=
        congrArg (fun product => G.mul (G.mul b a) product) hc.2
  calc
    b = G.mul (G.mul c a) b := b_eq_cab
    _ = G.mul (G.mul (G.mul (G.mul b a) c) a) b :=
      congrArg (fun candidate => G.mul (G.mul candidate a) b) c_eq_bac
    _ = G.mul b (G.mul (G.mul a c) (G.mul a b)) := by
      simp only [G.assoc]
    _ = G.mul b (G.mul (G.mul a b) (G.mul a c)) :=
      congrArg (fun product => G.mul b product)
        (commute hc.mul_idempotent hb.mul_idempotent)
    _ = G.mul (G.mul (G.mul b a) b) (G.mul a c) := by
      simp only [G.assoc]
    _ = G.mul b (G.mul a c) :=
      congrArg (fun product => G.mul product (G.mul a c)) hb.2
    _ = G.mul (G.mul b a) c := (G.assoc b a c).symm
    _ = c := c_eq_bac.symm

/-- Inverse witnesses are unique in an inverse semigroup. -/
theorem IsInverseSemigroup.inverse_unique
    {G : Semigroup S} (inverseSemigroup : G.IsInverseSemigroup)
    {a b c : S} (hb : G.IsInverse a b) (hc : G.IsInverse a c) :
    b = c :=
  IdempotentsCommute.inverse_unique
    (IsInverseSemigroup.idempotentsCommute inverseSemigroup) hb hc

/-- The unique inverse selected from regularity. -/
noncomputable def IsInverseSemigroup.inverse
    {G : Semigroup S} (inverseSemigroup : G.IsInverseSemigroup) (a : S) : S :=
  Classical.choose (inverseSemigroup.regularSemigroup a)

theorem IsInverseSemigroup.inverse_isInverse
    {G : Semigroup S} (inverseSemigroup : G.IsInverseSemigroup) (a : S) :
    G.IsInverse a (inverseSemigroup.inverse a) :=
  Classical.choose_spec (inverseSemigroup.regularSemigroup a)

/-- Taking the chosen inverse twice returns the original element. -/
theorem IsInverseSemigroup.inverse_inverse
    {G : Semigroup S} (inverseSemigroup : G.IsInverseSemigroup) (a : S) :
    inverseSemigroup.inverse (inverseSemigroup.inverse a) = a :=
  inverseSemigroup.inverse_unique
    (inverseSemigroup.inverse_isInverse (inverseSemigroup.inverse a))
    (inverseSemigroup.inverse_isInverse a).symm

/-- The chosen inverse reverses products. -/
theorem IsInverseSemigroup.inverse_mul
    {G : Semigroup S} (inverseSemigroup : G.IsInverseSemigroup) (a b : S) :
    inverseSemigroup.inverse (G.mul a b) =
      G.mul (inverseSemigroup.inverse b) (inverseSemigroup.inverse a) :=
  inverseSemigroup.inverse_unique
    (inverseSemigroup.inverse_isInverse (G.mul a b))
    (IdempotentsCommute.mul_inverse
      (IsInverseSemigroup.idempotentsCommute inverseSemigroup)
      (inverseSemigroup.inverse_isInverse a)
      (inverseSemigroup.inverse_isInverse b))

/-- The chosen inverse fixes every idempotent. -/
theorem IsInverseSemigroup.inverse_eq_self_of_isIdempotent
    {G : Semigroup S} (inverseSemigroup : G.IsInverseSemigroup)
    {e : S} (he : G.IsIdempotent e) :
    inverseSemigroup.inverse e = e := by
  change G.mul e e = e at he
  have sandwich : G.mul (G.mul e e) e = e := by
    calc
      G.mul (G.mul e e) e = G.mul e e :=
        congrArg (fun product => G.mul product e) he
      _ = e := he
  have selfInverse : G.IsInverse e e := ⟨sandwich, sandwich⟩
  exact inverseSemigroup.inverse_unique
    (inverseSemigroup.inverse_isInverse e) selfInverse

/-- The range idempotent `a a^-1`. -/
noncomputable def IsInverseSemigroup.range
    {G : Semigroup S} (inverseSemigroup : G.IsInverseSemigroup) (a : S) : S :=
  G.mul a (inverseSemigroup.inverse a)

/-- The source idempotent `a^-1 a`. -/
noncomputable def IsInverseSemigroup.source
    {G : Semigroup S} (inverseSemigroup : G.IsInverseSemigroup) (a : S) : S :=
  G.mul (inverseSemigroup.inverse a) a

theorem IsInverseSemigroup.range_isIdempotent
    {G : Semigroup S} (inverseSemigroup : G.IsInverseSemigroup) (a : S) :
    G.IsIdempotent (inverseSemigroup.range a) := by
  change G.IsIdempotent (G.mul a (inverseSemigroup.inverse a))
  exact (inverseSemigroup.inverse_isInverse a).mul_idempotent

theorem IsInverseSemigroup.source_isIdempotent
    {G : Semigroup S} (inverseSemigroup : G.IsInverseSemigroup) (a : S) :
    G.IsIdempotent (inverseSemigroup.source a) := by
  change G.IsIdempotent (G.mul (inverseSemigroup.inverse a) a)
  exact (inverseSemigroup.inverse_isInverse a).reverse_mul_idempotent

/-- The range idempotent acts as a left identity on its element. -/
theorem IsInverseSemigroup.range_mul_eq
    {G : Semigroup S} (inverseSemigroup : G.IsInverseSemigroup) (a : S) :
    G.mul (inverseSemigroup.range a) a = a := by
  change G.mul (G.mul a (inverseSemigroup.inverse a)) a = a
  exact (inverseSemigroup.inverse_isInverse a).1

/-- The source idempotent acts as a right identity on its element. -/
theorem IsInverseSemigroup.mul_source_eq
    {G : Semigroup S} (inverseSemigroup : G.IsInverseSemigroup) (a : S) :
    G.mul a (inverseSemigroup.source a) = a := by
  change G.mul a (G.mul (inverseSemigroup.inverse a) a) = a
  calc
    G.mul a (G.mul (inverseSemigroup.inverse a) a) =
        G.mul (G.mul a (inverseSemigroup.inverse a)) a :=
      (G.assoc a (inverseSemigroup.inverse a) a).symm
    _ = a := (inverseSemigroup.inverse_isInverse a).1

end Semigroup
end SemigroupBasis

import SemigroupBasis.StableRegularity
import SemigroupBasis.MatrixUnitEmbedding

namespace SemigroupBasis
namespace Semigroup

/-- Every nonzero element generates the whole semigroup as a two-sided
principal sandwich. -/
def ZeroSimple (G : Semigroup S) : Prop :=
  ∀ {a : S}, ¬ G.IsZero a → ∀ x, G.PrincipalSandwichMem a x

namespace IsZero

/-- A zero element is its own inverse, hence is regular. -/
theorem isRegular {G : Semigroup S} {z : S} (zero : G.IsZero z) :
    G.IsRegular z := by
  refine ⟨z, ?_, ?_⟩
  · rw [zero.1 z, zero.1 z]
  · rw [zero.1 z, zero.1 z]

end IsZero

namespace ZeroSimple

/-- In an `x^2 = x^3` zero-simple semigroup, one regular nonzero element
transfers regularity to every nonzero element; zero elements are regular
directly. -/
theorem regularSemigroup_of_regular_nonzero
    {G : Semigroup S} (zeroSimple : G.ZeroSimple)
    (law : G.SquareEqualsCube) {z : S}
    (z_nonzero : ¬ G.IsZero z) (z_regular : G.IsRegular z) :
    G.RegularSemigroup := by
  intro a
  by_cases a_zero : G.IsZero a
  · exact a_zero.isRegular
  · exact law.isRegular_of_mutual_principalSandwichMem
      (zeroSimple z_nonzero a) (zeroSimple a_zero z) z_regular

/-- Zero-simplicity turns commuting idempotents into orthogonal idempotents
under `x^2 = x^3`. -/
theorem idempotentsOrthogonal
    {G : Semigroup S} (zeroSimple : G.ZeroSimple)
    (law : G.SquareEqualsCube) (commute : G.IdempotentsCommute) :
    G.IdempotentsOrthogonal := by
  intro e f e_idempotent f_idempotent e_ne_f
  let g := G.mul e f
  change G.IsZero g
  apply Classical.byContradiction
  intro g_nonzero
  have e_mul_g : G.mul e g = g := by
    change G.mul e (G.mul e f) = G.mul e f
    calc
      G.mul e (G.mul e f) = G.mul (G.mul e e) f :=
        (G.assoc e e f).symm
      _ = G.mul e f := congrArg (fun x => G.mul x f) e_idempotent
  have g_mul_f : G.mul g f = g := by
    change G.mul (G.mul e f) f = G.mul e f
    calc
      G.mul (G.mul e f) f = G.mul e (G.mul f f) := G.assoc e f f
      _ = G.mul e f := congrArg (fun x => G.mul e x) f_idempotent
  have g_idempotent : G.IsIdempotent g := by
    change G.mul (G.mul e f) (G.mul e f) = G.mul e f
    calc
      G.mul (G.mul e f) (G.mul e f) =
          G.mul e (G.mul (G.mul f e) f) := by
        simp only [G.assoc]
      _ = G.mul e (G.mul (G.mul e f) f) := by
        rw [commute f_idempotent e_idempotent]
      _ = G.mul (G.mul e e) (G.mul f f) := by
        simp only [G.assoc]
      _ = G.mul e f := by rw [e_idempotent, f_idempotent]
  rcases zeroSimple g_nonzero e with ⟨p, q, e_factor⟩
  have e_self_sandwich :
      e = G.mul (G.mul p e) (G.mul g q) := by
    calc
      e = G.mul (G.mul p g) q := e_factor
      _ = G.mul (G.mul p (G.mul e g)) q := by rw [e_mul_g]
      _ = G.mul (G.mul p e) (G.mul g q) := by
        simp only [G.assoc]
  have e_absorbs_right : G.mul e (G.mul g q) = e :=
    (law.absorb_factors_of_eq_sandwich e_self_sandwich).2
  have e_eq_g_mul_q : e = G.mul g q := by
    calc
      e = G.mul e (G.mul g q) := e_absorbs_right.symm
      _ = G.mul (G.mul e g) q := (G.assoc e g q).symm
      _ = G.mul g q := congrArg (fun x => G.mul x q) e_mul_g
  have g_mul_e : G.mul g e = e := by
    calc
      G.mul g e = G.mul g (G.mul g q) :=
        congrArg (fun x => G.mul g x) e_eq_g_mul_q
      _ = G.mul (G.mul g g) q := (G.assoc g g q).symm
      _ = G.mul g q := congrArg (fun x => G.mul x q) g_idempotent
      _ = e := e_eq_g_mul_q.symm
  have e_eq_g : e = g := by
    calc
      e = G.mul g e := g_mul_e.symm
      _ = G.mul e g := (commute e_idempotent g_idempotent).symm
      _ = g := e_mul_g
  rcases zeroSimple g_nonzero f with ⟨r, s, f_factor⟩
  have f_self_sandwich :
      f = G.mul (G.mul (G.mul r g) f) s := by
    calc
      f = G.mul (G.mul r g) s := f_factor
      _ = G.mul (G.mul r (G.mul g f)) s := by rw [g_mul_f]
      _ = G.mul (G.mul (G.mul r g) f) s := by
        simp only [G.assoc]
  have left_absorbs_f : G.mul (G.mul r g) f = f :=
    (law.absorb_factors_of_eq_sandwich f_self_sandwich).1
  have f_eq_r_mul_g : f = G.mul r g := by
    calc
      f = G.mul (G.mul r g) f := left_absorbs_f.symm
      _ = G.mul r (G.mul g f) := G.assoc r g f
      _ = G.mul r g := congrArg (fun x => G.mul r x) g_mul_f
  have f_mul_g : G.mul f g = f := by
    calc
      G.mul f g = G.mul (G.mul r g) g :=
        congrArg (fun x => G.mul x g) f_eq_r_mul_g
      _ = G.mul r (G.mul g g) := G.assoc r g g
      _ = G.mul r g := congrArg (fun x => G.mul r x) g_idempotent
      _ = f := f_eq_r_mul_g.symm
  have f_eq_g : f = g := by
    calc
      f = G.mul f g := f_mul_g.symm
      _ = G.mul g f := commute f_idempotent g_idempotent
      _ = g := g_mul_f
  exact e_ne_f (e_eq_g.trans f_eq_g.symm)

/-- In a square-cube zero-simple semigroup, regular elements with a common
left factor are equal when every left translation agrees. -/
theorem eq_of_commonLeftFactor_of_leftActionEq
    {G : Semigroup S} (zeroSimple : G.ZeroSimple)
    (law : G.SquareEqualsCube)
    {a b common p r : S}
    (aRegular : G.IsRegular a)
    (bRegular : G.IsRegular b)
    (aFactor : a = G.mul common p)
    (bFactor : b = G.mul common r)
    (leftAction : ∀ e, G.mul e a = G.mul e b) :
    a = b := by
  by_cases aZero : G.IsZero a
  · rcases bRegular with ⟨bInv, bInverse⟩
    calc
      a = G.mul (G.mul b bInv) a :=
        (aZero.2 (G.mul b bInv)).symm
      _ = G.mul (G.mul b bInv) b :=
        leftAction (G.mul b bInv)
      _ = b := bInverse.1
  · rcases aRegular with ⟨aInv, aInverse⟩
    let e := G.mul a aInv
    have eMulB : G.mul e b = a := by
      calc
        G.mul e b = G.mul e a := (leftAction e).symm
        _ = a := by
          simpa only [e] using aInverse.1
    rcases zeroSimple aZero common with
      ⟨front, suffix, commonFactor⟩
    have commonSelfSandwich :
        common =
          G.mul (G.mul (G.mul front e) common)
            (G.mul r suffix) := by
      calc
        common = G.mul (G.mul front a) suffix :=
          commonFactor
        _ = G.mul (G.mul front (G.mul e b)) suffix := by
          rw [← eMulB]
        _ =
            G.mul (G.mul (G.mul front e) common)
              (G.mul r suffix) := by
          rw [bFactor]
          simp only [G.assoc]
    have stabilizesCommon :
        G.mul (G.mul front e) common = common :=
      (law.absorb_factors_of_eq_sandwich
        commonSelfSandwich).1
    calc
      a = G.mul common p := aFactor
      _ = G.mul (G.mul (G.mul front e) common) p := by
        rw [stabilizesCommon]
      _ = G.mul (G.mul front e) (G.mul common p) :=
        G.assoc _ _ _
      _ = G.mul (G.mul front e) a := by
        rw [← aFactor]
      _ = G.mul (G.mul front e) b :=
        leftAction _
      _ = G.mul (G.mul front e) (G.mul common r) := by
        rw [bFactor]
      _ = G.mul (G.mul (G.mul front e) common) r :=
        (G.assoc _ _ _).symm
      _ = G.mul common r :=
        congrArg (fun value => G.mul value r)
          stabilizesCommon
      _ = b := bFactor.symm

end ZeroSimple
end Semigroup
end SemigroupBasis

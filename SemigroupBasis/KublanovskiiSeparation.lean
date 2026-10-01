import SemigroupBasis.Regular
import SemigroupBasis.Schutzenberger

namespace SemigroupBasis
namespace Semigroup

private theorem mul_reverse_mul_eq_self_of_isInverse
    {G : Semigroup S} {a aInv : S} (h : G.IsInverse a aInv) :
    G.mul a (G.mul aInv a) = a := by
  calc
    G.mul a (G.mul aInv a) = G.mul (G.mul a aInv) a :=
      (G.assoc a aInv a).symm
    _ = a := h.1

private theorem self_principalSandwichMem_of_isInverse
    {G : Semigroup S} {a aInv : S} (h : G.IsInverse a aInv) :
    G.PrincipalSandwichMem a a := by
  refine ⟨G.mul a aInv, G.mul aInv a, ?_⟩
  calc
    a = G.mul (G.mul a aInv) a := h.1.symm
    _ = G.mul a (G.mul aInv a) := G.assoc a aInv a
    _ = G.mul (G.mul (G.mul a aInv) a) (G.mul aInv a) := by
      rw [h.1]

private theorem reverse_mul_principalSandwichMem_of_isInverse
    {G : Semigroup S} {a aInv : S} (h : G.IsInverse a aInv) :
    G.PrincipalSandwichMem a (G.mul aInv a) := by
  refine ⟨aInv, G.mul aInv a, ?_⟩
  exact h.reverse_mul_idempotent.symm

private theorem principalSandwichMem_trans
    {G : Semigroup S} {x y z : S}
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

/-- The final separation step in Volkov's Lemma 5.

If `a` and `b` are distinct regular elements and idempotents commute, then
one of the right Schutzenberger congruences `rho_a` and `rho_b` has an
explicit right-translate witness separating them.
-/
theorem distinct_regular_rightSchutzenberger_separation
    {G : Semigroup S} {a b : S}
    (commute : G.IdempotentsCommute)
    (ha : G.IsRegular a) (hb : G.IsRegular b) (hne : a ≠ b) :
    G.RightSchutzenbergerSeparates a a b ∨
      G.RightSchutzenbergerSeparates b a b := by
  classical
  rcases ha with ⟨aInv, haInv⟩
  rcases hb with ⟨bInv, hbInv⟩
  have hae : G.mul a (G.mul aInv a) = a :=
    mul_reverse_mul_eq_self_of_isInverse haInv
  have hbf : G.mul b (G.mul bInv b) = b :=
    mul_reverse_mul_eq_self_of_isInverse hbInv
  have haaSandwich : G.PrincipalSandwichMem a a :=
    self_principalSandwichMem_of_isInverse haInv
  have hbbSandwich : G.PrincipalSandwichMem b b :=
    self_principalSandwichMem_of_isInverse hbInv
  have heSandwichA :
      G.PrincipalSandwichMem a (G.mul aInv a) :=
    reverse_mul_principalSandwichMem_of_isInverse haInv
  have hfSandwichB :
      G.PrincipalSandwichMem b (G.mul bInv b) :=
    reverse_mul_principalSandwichMem_of_isInverse hbInv
  have heIdempotent : G.IsIdempotent (G.mul aInv a) :=
    haInv.reverse_mul_idempotent
  have hfIdempotent : G.IsIdempotent (G.mul bInv b) :=
    hbInv.reverse_mul_idempotent

  by_cases haOutside : ¬ G.PrincipalSandwichMem b a
  · -- `a ∉ S b S`: `aInv * a` witnesses separation by `rho_a`.
    have hbMemIa : b ∈ I_z G a := by
      change ¬ G.PrincipalSandwichMem b a
      exact haOutside
    have haNotMemIa : ¬ (a ∈ I_z G a) := by
      intro haMem
      change ¬ G.PrincipalSandwichMem a a at haMem
      exact haMem haaSandwich
    have hbeMemIa : G.mul b (G.mul aInv a) ∈ I_z G a :=
      (I_z G a).mul_mem_right hbMemIa (G.mul aInv a)
    have haeNotMemIa : ¬ (G.mul a (G.mul aInv a) ∈ I_z G a) := by
      intro haeMem
      rw [hae] at haeMem
      exact haNotMemIa haeMem
    refine Or.inl ⟨G.mul aInv a, heSandwichA, ?_⟩
    intro hRees
    rcases hRees with heq | hboth
    · apply haeNotMemIa
      rw [heq]
      exact hbeMemIa
    · exact haeNotMemIa hboth.1
  · have haInside : G.PrincipalSandwichMem b a := by
      apply Classical.byContradiction
      intro h
      exact haOutside h
    by_cases hbOutside : ¬ G.PrincipalSandwichMem a b
    · -- `b ∉ S a S`: `bInv * b` witnesses separation by `rho_b`.
      have haMemIb : a ∈ I_z G b := by
        change ¬ G.PrincipalSandwichMem a b
        exact hbOutside
      have hbNotMemIb : ¬ (b ∈ I_z G b) := by
        intro hbMem
        change ¬ G.PrincipalSandwichMem b b at hbMem
        exact hbMem hbbSandwich
      have hafMemIb : G.mul a (G.mul bInv b) ∈ I_z G b :=
        (I_z G b).mul_mem_right haMemIb (G.mul bInv b)
      have hbfNotMemIb : ¬ (G.mul b (G.mul bInv b) ∈ I_z G b) := by
        intro hbfMem
        rw [hbf] at hbfMem
        exact hbNotMemIb hbfMem
      refine Or.inr ⟨G.mul bInv b, hfSandwichB, ?_⟩
      intro hRees
      rcases hRees with heq | hboth
      · apply hbfNotMemIb
        rw [← heq]
        exact hafMemIb
      · exact hbfNotMemIb hboth.2
    · have hbInside : G.PrincipalSandwichMem a b := by
        apply Classical.byContradiction
        intro h
        exact hbOutside h
      -- The two inclusions make the principal sandwiches `S a S` and
      -- `S b S` equal. The proof records the composed factors explicitly.
      have principalSandwich_eq (x : S) :
          G.PrincipalSandwichMem a x ↔
            G.PrincipalSandwichMem b x := by
        constructor
        · intro hx
          exact principalSandwichMem_trans hx haInside
        · intro hx
          exact principalSandwichMem_trans hx hbInside
      have hfSandwichA :
          G.PrincipalSandwichMem a (G.mul bInv b) :=
        (principalSandwich_eq (G.mul bInv b)).2 hfSandwichB
      have haNotMemIa : ¬ (a ∈ I_z G a) := by
        intro haMem
        change ¬ G.PrincipalSandwichMem a a at haMem
        exact haMem haaSandwich
      have hbNotMemIa : ¬ (b ∈ I_z G a) := by
        intro hbMem
        change ¬ G.PrincipalSandwichMem b a at hbMem
        exact hbMem haInside
      have haeNotMemIa : ¬ (G.mul a (G.mul aInv a) ∈ I_z G a) := by
        intro haeMem
        rw [hae] at haeMem
        exact haNotMemIa haeMem
      have hbfNotMemIa : ¬ (G.mul b (G.mul bInv b) ∈ I_z G a) := by
        intro hbfMem
        rw [hbf] at hbfMem
        exact hbNotMemIa hbfMem

      by_cases hReesE :
          (I_z G a).ReesRel
            (G.mul a (G.mul aInv a)) (G.mul b (G.mul aInv a))
      · have haeEq :
            G.mul a (G.mul aInv a) = G.mul b (G.mul aInv a) := by
          rcases hReesE with heq | hboth
          · exact heq
          · exact (haeNotMemIa hboth.1).elim
        by_cases hReesF :
            (I_z G a).ReesRel
              (G.mul a (G.mul bInv b)) (G.mul b (G.mul bInv b))
        · have hafEq :
              G.mul a (G.mul bInv b) = G.mul b (G.mul bInv b) := by
            rcases hReesF with heq | hboth
            · exact heq
            · exact (hbfNotMemIa hboth.2).elim
          have hab : a = b := by
            calc
              a = G.mul a (G.mul aInv a) := hae.symm
              _ = G.mul b (G.mul aInv a) := haeEq
              _ = G.mul (G.mul b (G.mul bInv b)) (G.mul aInv a) :=
                congrArg (fun x => G.mul x (G.mul aInv a)) hbf.symm
              _ = G.mul (G.mul a (G.mul bInv b)) (G.mul aInv a) :=
                congrArg (fun x => G.mul x (G.mul aInv a)) hafEq.symm
              _ = G.mul (G.mul a (G.mul aInv a)) (G.mul bInv b) := by
                calc
                  G.mul (G.mul a (G.mul bInv b)) (G.mul aInv a) =
                      G.mul a (G.mul (G.mul bInv b) (G.mul aInv a)) :=
                    G.assoc a (G.mul bInv b) (G.mul aInv a)
                  _ = G.mul a (G.mul (G.mul aInv a) (G.mul bInv b)) :=
                    congrArg (fun x => G.mul a x)
                      (commute hfIdempotent heIdempotent)
                  _ = G.mul (G.mul a (G.mul aInv a)) (G.mul bInv b) :=
                    (G.assoc a (G.mul aInv a) (G.mul bInv b)).symm
              _ = G.mul a (G.mul bInv b) :=
                congrArg (fun x => G.mul x (G.mul bInv b)) hae
              _ = G.mul b (G.mul bInv b) := hafEq
              _ = b := hbf
          exact False.elim (hne hab)
        · exact Or.inl ⟨G.mul bInv b, hfSandwichA, hReesF⟩
      · exact Or.inl ⟨G.mul aInv a, heSandwichA, hReesE⟩

/-- Canonical quotient projections give the equivalent separation statement. -/
theorem distinct_regular_rightSchutzenberger_projection_separation
    {G : Semigroup S} {a b : S}
    (commute : G.IdempotentsCommute)
    (ha : G.IsRegular a) (hb : G.IsRegular b) (hne : a ≠ b) :
    (rightSchutzenbergerCongruence G a).projection.toFun a ≠
        (rightSchutzenbergerCongruence G a).projection.toFun b ∨
      (rightSchutzenbergerCongruence G b).projection.toFun a ≠
        (rightSchutzenbergerCongruence G b).projection.toFun b := by
  rcases distinct_regular_rightSchutzenberger_separation commute ha hb hne with
    h | h
  · exact Or.inl
      ((rightSchutzenberger_projection_ne_iff_exists_separator G a).2 h)
  · exact Or.inr
      ((rightSchutzenberger_projection_ne_iff_exists_separator G b).2 h)

end Semigroup
end SemigroupBasis

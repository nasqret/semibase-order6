import SemigroupBasis.Congruence

namespace SemigroupBasis
namespace Semigroup

/-- An empty-permitting two-sided ideal of an explicitly supplied semigroup. -/
structure Ideal (G : Semigroup S) where
  carrier : S → Prop
  mul_mem_left : ∀ a {x}, carrier x → carrier (G.mul a x)
  mul_mem_right : ∀ {x}, carrier x → ∀ a, carrier (G.mul x a)

namespace Ideal

instance {G : Semigroup S} : Membership S (Ideal G) where
  mem I x := I.carrier x

@[simp]
theorem mem_carrier {G : Semigroup S} (I : Ideal G) (x : S) :
    x ∈ I ↔ I.carrier x :=
  Iff.rfl

/-- The empty set is a two-sided ideal; ideals are not required to be nonempty. -/
def empty (G : Semigroup S) : Ideal G where
  carrier := fun _ => False
  mul_mem_left := by
    intro _ _ h
    exact h.elim
  mul_mem_right := by
    intro _ h _
    exact h.elim

@[simp]
theorem not_mem_empty (G : Semigroup S) (x : S) :
    ¬ (x ∈ empty G) := by
  intro h
  exact h

end Ideal

/-- Membership in the principal sandwich `S * z * S`, with explicit witnesses. -/
def PrincipalSandwichMem (G : Semigroup S) (z x : S) : Prop :=
  ∃ p q, x = G.mul (G.mul p z) q

/-- The elements whose principal sandwiches do not contain `z`. -/
def I_z (G : Semigroup S) (z : S) : Ideal G where
  carrier := fun u => ¬ G.PrincipalSandwichMem u z
  mul_mem_left := by
    intro a u hu huz
    apply hu
    rcases huz with ⟨p, q, hz⟩
    refine ⟨G.mul p a, q, ?_⟩
    calc
      z = G.mul (G.mul p (G.mul a u)) q := hz
      _ = G.mul (G.mul (G.mul p a) u) q :=
        congrArg (fun t => G.mul t q) (G.assoc p a u).symm
  mul_mem_right := by
    intro u hu a huz
    apply hu
    rcases huz with ⟨p, q, hz⟩
    refine ⟨p, G.mul a q, ?_⟩
    calc
      z = G.mul (G.mul p (G.mul u a)) q := hz
      _ = G.mul (G.mul (G.mul p u) a) q :=
        congrArg (fun t => G.mul t q) (G.assoc p u a).symm
      _ = G.mul (G.mul p u) (G.mul a q) :=
        G.assoc (G.mul p u) a q

@[simp]
theorem mem_I_z_iff (G : Semigroup S) (z u : S) :
    u ∈ I_z G z ↔ ¬ G.PrincipalSandwichMem u z :=
  Iff.rfl

namespace Ideal

/-- The Rees relation: equality outside the ideal and one collapsed ideal class. -/
def ReesRel {G : Semigroup S} (I : Ideal G) (a b : S) : Prop :=
  a = b ∨ (a ∈ I ∧ b ∈ I)

theorem reesRel_refl {G : Semigroup S} (I : Ideal G) (a : S) :
    I.ReesRel a a :=
  Or.inl rfl

theorem reesRel_symm {G : Semigroup S} (I : Ideal G) {a b : S}
    (h : I.ReesRel a b) : I.ReesRel b a := by
  rcases h with hab | hab
  · exact Or.inl hab.symm
  · exact Or.inr ⟨hab.2, hab.1⟩

theorem reesRel_trans {G : Semigroup S} (I : Ideal G) {a b c : S}
    (hab : I.ReesRel a b) (hbc : I.ReesRel b c) : I.ReesRel a c := by
  rcases hab with hab | hab
  · subst b
    exact hbc
  · rcases hbc with hbc | hbc
    · subst c
      exact Or.inr hab
    · exact Or.inr ⟨hab.1, hbc.2⟩

theorem reesRel_equivalence {G : Semigroup S} (I : Ideal G) :
    Equivalence I.ReesRel where
  refl := reesRel_refl I
  symm := reesRel_symm I
  trans := reesRel_trans I

/-- The Rees relation of a two-sided ideal, packaged as a semigroup congruence. -/
def reesCongruence {G : Semigroup S} (I : Ideal G) : Congruence G where
  r := I.ReesRel
  iseqv := reesRel_equivalence I
  mul_compat := by
    intro a₁ a₂ b₁ b₂ ha hb
    change I.ReesRel a₁ a₂ at ha
    change I.ReesRel b₁ b₂ at hb
    change I.ReesRel (G.mul a₁ b₁) (G.mul a₂ b₂)
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · subst a₂
        subst b₂
        exact Or.inl rfl
      · subst a₂
        exact Or.inr
          ⟨I.mul_mem_left a₁ hb.1, I.mul_mem_left a₁ hb.2⟩
    · rcases hb with hb | hb
      · subst b₂
        exact Or.inr
          ⟨I.mul_mem_right ha.1 b₁, I.mul_mem_right ha.2 b₁⟩
      · exact Or.inr
          ⟨I.mul_mem_right ha.1 b₁, I.mul_mem_right ha.2 b₂⟩

@[simp]
theorem reesCongruence_rel_iff {G : Semigroup S} (I : Ideal G) (a b : S) :
    I.reesCongruence.r a b ↔ I.ReesRel a b :=
  Iff.rfl

end Ideal
end Semigroup
end SemigroupBasis

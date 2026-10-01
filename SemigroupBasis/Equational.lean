import SemigroupBasis.Word

namespace SemigroupBasis

structure Identity (α : Type u) where
  lhs : Word α
  rhs : Word α
deriving Repr, DecidableEq

namespace Identity

def SatisfiedBy (e : Identity α) (G : Semigroup S) : Prop :=
  ∀ valuation : α → S, G.eval valuation e.lhs = G.eval valuation e.rhs

/-- A single valuation witnessing failure of an identity. -/
def FailsAt (e : Identity α) (G : Semigroup S) (valuation : α → S) : Prop :=
  G.eval valuation e.lhs ≠ G.eval valuation e.rhs

theorem not_satisfiedBy_of_failsAt {e : Identity α} {G : Semigroup S}
    {valuation : α → S} (h : e.FailsAt G valuation) :
    ¬ e.SatisfiedBy G := by
  intro valid
  exact h (valid valuation)

end Identity

def Models (G : Semigroup S) (basis : List (Identity α)) : Prop :=
  ∀ e, e ∈ basis → e.SatisfiedBy G

/-- Equational derivability for semigroup words over one infinite variable type. -/
inductive Derives (basis : List (Identity α)) : Word α → Word α → Prop
  | fromBasis {e : Identity α} : e ∈ basis → Derives basis e.lhs e.rhs
  | refl (u : Word α) : Derives basis u u
  | symm {u v : Word α} : Derives basis u v → Derives basis v u
  | trans {u v w : Word α} :
      Derives basis u v → Derives basis v w → Derives basis u w
  | prepend (p : Word α) {u v : Word α} :
      Derives basis u v → Derives basis (p ++ u) (p ++ v)
  | appendRight {u v : Word α} :
      Derives basis u v → (q : Word α) → Derives basis (u ++ q) (v ++ q)
  | subst {u v : Word α} :
      Derives basis u v → (σ : α → Word α) →
        Derives basis (u.bind σ) (v.bind σ)

/-- A finite list is a basis when it is sound and derives every valid identity. -/
def BasisFor (G : Semigroup S) (basis : List (Identity α)) : Prop :=
  Models G basis ∧
    ∀ e : Identity α, e.SatisfiedBy G → Derives basis e.lhs e.rhs

theorem Derives.sound {α : Type u} {S : Type v} {G : Semigroup S}
    {basis : List (Identity α)} {u v : Word α}
    (hmodels : Models G basis) (h : Derives basis u v) (valuation : α → S) :
    G.eval valuation u = G.eval valuation v := by
  induction h generalizing valuation with
  | fromBasis hmem => exact hmodels _ hmem valuation
  | refl => rfl
  | symm _ ih => exact (ih valuation).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ valuation).trans (ih₂ valuation)
  | prepend p _ ih =>
      simp only [Semigroup.eval_append]
      exact congrArg (G.mul (G.eval valuation p)) (ih valuation)
  | appendRight _ q ih =>
      simp only [Semigroup.eval_append]
      exact congrArg (fun x => G.mul x (G.eval valuation q)) (ih valuation)
  | subst h σ ih =>
      rw [Semigroup.eval_bind, Semigroup.eval_bind]
      exact ih (fun x => G.eval valuation (σ x))

theorem Derives.transport {source target : List (Identity α)} {u v : Word α}
    (axiomDerives :
      ∀ e : Identity α, e ∈ source → Derives target e.lhs e.rhs)
    (h : Derives source u v) : Derives target u v := by
  induction h with
  | fromBasis hmem => exact axiomDerives _ hmem
  | refl => exact Derives.refl _
  | symm _ ih => exact Derives.symm ih
  | trans _ _ ih₁ ih₂ => exact Derives.trans ih₁ ih₂
  | prepend p _ ih => exact Derives.prepend p ih
  | appendRight _ q ih => exact Derives.appendRight ih q
  | subst _ σ ih => exact Derives.subst ih σ

theorem BasisFor.replace {G : Semigroup S} {source target : List (Identity α)}
    (sourceBasis : BasisFor G source) (targetModels : Models G target)
    (sourceAxiomsDerive :
      ∀ e : Identity α, e ∈ source → Derives target e.lhs e.rhs) :
    BasisFor G target := by
  refine ⟨targetModels, ?_⟩
  intro e valid
  exact (sourceBasis.2 e valid).transport sourceAxiomsDerive

end SemigroupBasis

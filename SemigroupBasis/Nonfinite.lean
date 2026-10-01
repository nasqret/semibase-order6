import SemigroupBasis.Equational

namespace SemigroupBasis

/-- Finite basability relative to a chosen variable type. The intended use is
with an infinite variable type, such as `Nat`. -/
def FinitelyBasedOver (G : Semigroup S) (α : Type u) : Prop :=
  ∃ basis : List (Identity α), BasisFor G basis

/-- Failure of finite basability relative to a chosen variable type. -/
def NonfinitelyBasedOver (G : Semigroup S) (α : Type u) : Prop :=
  ¬FinitelyBasedOver G α

/-- The standard finite-basis predicate, using `Nat` as the infinite variable
type already used by the unrestricted completeness results in this project. -/
def FinitelyBased (G : Semigroup S) : Prop :=
  FinitelyBasedOver G Nat

/-- The standard nonfinite-basis predicate, using `Nat` variables. -/
def NonfinitelyBased (G : Semigroup S) : Prop :=
  NonfinitelyBasedOver G Nat

theorem finitelyBasedOver_iff_exists_list_basisFor :
    FinitelyBasedOver G α ↔
      ∃ basis : List (Identity α), BasisFor G basis :=
  Iff.rfl

theorem finitelyBased_iff_exists_list_basisFor :
    FinitelyBased G ↔
      ∃ basis : List (Identity Nat), BasisFor G basis :=
  Iff.rfl

theorem nonfinitelyBasedOver_iff_not :
    NonfinitelyBasedOver G α ↔ ¬FinitelyBasedOver G α :=
  Iff.rfl

theorem nonfinitelyBased_iff_not :
    NonfinitelyBased G ↔ ¬FinitelyBased G :=
  Iff.rfl

theorem BasisFor.finitelyBasedOver
    {α : Type u} {basis : List (Identity α)}
    (h : BasisFor G basis) :
    FinitelyBasedOver G α :=
  ⟨basis, h⟩

theorem BasisFor.finitelyBased
    {basis : List (Identity Nat)}
    (h : BasisFor G basis) :
    FinitelyBased G :=
  h.finitelyBasedOver

theorem FinitelyBasedOver.not_nonfinitelyBasedOver
    (h : FinitelyBasedOver G α) :
    ¬NonfinitelyBasedOver G α :=
  fun hnfb => hnfb h

theorem NonfinitelyBasedOver.not_finitelyBasedOver
    (h : NonfinitelyBasedOver G α) :
    ¬FinitelyBasedOver G α :=
  h

theorem FinitelyBased.not_nonfinitelyBased (h : FinitelyBased G) :
    ¬NonfinitelyBased G :=
  fun hnfb => hnfb h

theorem NonfinitelyBased.not_finitelyBased (h : NonfinitelyBased G) :
    ¬FinitelyBased G :=
  h

theorem not_finitelyBasedOver_and_nonfinitelyBasedOver :
    ¬(FinitelyBasedOver G α ∧ NonfinitelyBasedOver G α) := by
  rintro ⟨hFinite, hNonfinite⟩
  exact hNonfinite hFinite

theorem not_finitelyBased_and_nonfinitelyBased :
    ¬(FinitelyBased G ∧ NonfinitelyBased G) := by
  rintro ⟨hFinite, hNonfinite⟩
  exact hNonfinite hFinite

/-- Exact agreement of two semigroups' identity theories over `α`. -/
def SameIdentityTheoryOver (G : Semigroup S) (H : Semigroup T)
    (α : Type u) : Prop :=
  ∀ e : Identity α, e.SatisfiedBy G ↔ e.SatisfiedBy H

/-- Exact agreement of identity theories over the standard variable type. -/
def SameIdentityTheory (G : Semigroup S) (H : Semigroup T) : Prop :=
  SameIdentityTheoryOver G H Nat

theorem Models.transportIdentityTheory
    {α : Type u} {basis : List (Identity α)}
    (hTheory : SameIdentityTheoryOver G H α)
    (hModels : Models G basis) :
    Models H basis := by
  intro e he
  exact (hTheory e).mp (hModels e he)

theorem basisFor_iff_of_sameIdentityTheoryOver
    {α : Type u} {basis : List (Identity α)}
    (hTheory : SameIdentityTheoryOver G H α) :
    BasisFor G basis ↔ BasisFor H basis := by
  constructor
  · intro hBasis
    refine ⟨hBasis.1.transportIdentityTheory hTheory, ?_⟩
    intro e hValid
    exact hBasis.2 e ((hTheory e).mpr hValid)
  · intro hBasis
    refine ⟨?_, ?_⟩
    · intro e he
      exact (hTheory e).mpr (hBasis.1 e he)
    · intro e hValid
      exact hBasis.2 e ((hTheory e).mp hValid)

theorem finitelyBasedOver_iff_of_sameIdentityTheoryOver
    (hTheory : SameIdentityTheoryOver G H α) :
    FinitelyBasedOver G α ↔ FinitelyBasedOver H α := by
  constructor
  · rintro ⟨basis, hBasis⟩
    exact ⟨basis, (basisFor_iff_of_sameIdentityTheoryOver hTheory).mp hBasis⟩
  · rintro ⟨basis, hBasis⟩
    exact ⟨basis, (basisFor_iff_of_sameIdentityTheoryOver hTheory).mpr hBasis⟩

theorem nonfinitelyBasedOver_iff_of_sameIdentityTheoryOver
    (hTheory : SameIdentityTheoryOver G H α) :
    NonfinitelyBasedOver G α ↔ NonfinitelyBasedOver H α := by
  have hFinite :=
    finitelyBasedOver_iff_of_sameIdentityTheoryOver hTheory
  constructor
  · intro hG hH
    exact hG (hFinite.mpr hH)
  · intro hH hG
    exact hH (hFinite.mp hG)

theorem finitelyBased_iff_of_sameIdentityTheory
    (hTheory : SameIdentityTheory G H) :
    FinitelyBased G ↔ FinitelyBased H :=
  finitelyBasedOver_iff_of_sameIdentityTheoryOver hTheory

theorem nonfinitelyBased_iff_of_sameIdentityTheory
    (hTheory : SameIdentityTheory G H) :
    NonfinitelyBased G ↔ NonfinitelyBased H :=
  nonfinitelyBasedOver_iff_of_sameIdentityTheoryOver hTheory

namespace Word

/-- Every variable occurring in `w` belongs to `variables`. -/
def UsesOnly (w : Word α) (variables : List α) : Prop :=
  ∀ x, x ∈ w.toList → x ∈ variables

theorem UsesOnly.mono {w : Word α} {source target : List α}
    (h : w.UsesOnly source)
    (hsub : ∀ x, x ∈ source → x ∈ target) :
    w.UsesOnly target := by
  intro x hx
  exact hsub x (h x hx)

end Word

namespace Identity

/-- Both sides of an identity use only variables from `variables`. -/
def UsesOnly (e : Identity α) (variables : List α) : Prop :=
  e.lhs.UsesOnly variables ∧ e.rhs.UsesOnly variables

/-- The variables of an identity can be covered by a list of length at most
`bound`. Repetitions are allowed in the witness list, but never help satisfy
the length bound. -/
def UsesAtMost (e : Identity α) (bound : Nat) : Prop :=
  ∃ variables : List α,
    variables.length ≤ bound ∧ e.UsesOnly variables

theorem UsesOnly.usesAtMost {e : Identity α} {variables : List α}
    (h : e.UsesOnly variables) :
    e.UsesAtMost variables.length :=
  ⟨variables, Nat.le_refl _, h⟩

end Identity

/-- A concrete list containing every variable occurring in every identity of
`basis`. -/
def basisVariables (basis : List (Identity α)) : List α :=
  basis.flatMap fun e => e.lhs.toList ++ e.rhs.toList

def BasisUsesOnly (basis : List (Identity α))
    (variables : List α) : Prop :=
  ∀ e, e ∈ basis → e.UsesOnly variables

def BasisUsesAtMost (basis : List (Identity α)) (bound : Nat) : Prop :=
  ∀ e, e ∈ basis → e.UsesAtMost bound

theorem basis_usesOnly_basisVariables (basis : List (Identity α)) :
    BasisUsesOnly basis (basisVariables basis) := by
  intro e he
  constructor
  · intro x hx
    exact List.mem_flatMap.mpr
      ⟨e, he, List.mem_append.mpr (Or.inl hx)⟩
  · intro x hx
    exact List.mem_flatMap.mpr
      ⟨e, he, List.mem_append.mpr (Or.inr hx)⟩

theorem basis_usesAtMost_basisVariables (basis : List (Identity α)) :
    BasisUsesAtMost basis (basisVariables basis).length := by
  intro e he
  exact (basis_usesOnly_basisVariables basis e he).usesAtMost

/-- Every finite list of identities has a uniform finite variable bound. -/
theorem basis_has_variable_bound (basis : List (Identity α)) :
    ∃ bound : Nat, BasisUsesAtMost basis bound :=
  ⟨(basisVariables basis).length, basis_usesAtMost_basisVariables basis⟩

/-- Generic infinite-obstruction criterion.

For every variable bound, provide a valid identity that cannot be derived from
any sound basis whose individual identities use at most that many variables.
Then no finite basis can present the identity theory. -/
theorem nonfinitelyBasedOver_of_variable_bound_obstructions
    (obstruction : Nat → Identity α)
    (valid : ∀ bound, (obstruction bound).SatisfiedBy G)
    (underivable :
      ∀ bound basis,
        Models G basis →
        BasisUsesAtMost basis bound →
        ¬Derives basis (obstruction bound).lhs (obstruction bound).rhs) :
    NonfinitelyBasedOver G α := by
  rintro ⟨basis, hBasis⟩
  rcases basis_has_variable_bound basis with ⟨bound, hBound⟩
  exact underivable bound basis hBasis.1 hBound
    (hBasis.2 (obstruction bound) (valid bound))

theorem nonfinitelyBased_of_variable_bound_obstructions
    (obstruction : Nat → Identity Nat)
    (valid : ∀ bound, (obstruction bound).SatisfiedBy G)
    (underivable :
      ∀ bound basis,
        Models G basis →
        BasisUsesAtMost basis bound →
        ¬Derives basis (obstruction bound).lhs (obstruction bound).rhs) :
    NonfinitelyBased G :=
  nonfinitelyBasedOver_of_variable_bound_obstructions
    obstruction valid underivable

end SemigroupBasis

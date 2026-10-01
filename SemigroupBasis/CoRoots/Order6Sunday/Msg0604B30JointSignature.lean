import SemigroupBasis.CoRoots.Order6Sunday.Msg0521RepairedThirtyLawFinite
import SemigroupBasis.CoRoots.S5_402SignatureBridge
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.TransferPower

/-!
The unrestricted semantic interface for the repaired B30 siblings.
Both literal tables have exactly the intersection theory of S5_402 and C2.
This establishes exact signature sufficiency, NOT B30 derivational
completeness. The remaining derivational obligation is stated as an iff,
not supplied as an axiom, instance, or completed class endpoint.
-/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0604B30JointSignature

open SemigroupBasis

def quotient4091 : SplitSurjection Msg0521RepairedThirtyLawFinite.S6_4091.table.semigroup S5_402.table.semigroup where
  toFun := fun (a : Fin 6) =>
    (if a.val = 0 then 0 else if a.val = 1 then 1 else
    if a.val = 2 then 2 else if a.val = 3 then 0 else
    if a.val = 4 then 3 else 4 : Fin 5)
  map_mul := by decide
  preimage := fun (a : Fin 5) =>
    (if a.val = 0 then 0 else if a.val = 1 then 1 else
    if a.val = 2 then 2 else if a.val = 3 then 4 else 5 : Fin 6)
  right_inverse := by decide

def quotient4297 : SplitSurjection Msg0521RepairedThirtyLawFinite.S6_4297.table.semigroup S5_402.table.semigroup where
  toFun := fun (a : Fin 6) =>
    (if a.val = 0 then 0 else if a.val = 1 then 0 else
    if a.val = 2 then 1 else if a.val = 3 then 2 else
    if a.val = 4 then 3 else 4 : Fin 5)
  map_mul := by decide
  preimage := fun (a : Fin 5) =>
    (if a.val = 0 then 0 else if a.val = 1 then 2 else
    if a.val = 2 then 3 else if a.val = 3 then 4 else 5 : Fin 6)
  right_inverse := by decide

def parity4091 : Hom Msg0521RepairedThirtyLawFinite.S6_4091.table.semigroup Examples.cyclicTwo.semigroup where
  toFun := fun (a : Fin 6) => (if a.val = 3 then 1 else 0 : Fin 2)
  map_mul := by decide

def parity4297 : Hom Msg0521RepairedThirtyLawFinite.S6_4297.table.semigroup Examples.cyclicTwo.semigroup where
  toFun := fun (a : Fin 6) =>
    (if a.val = 1 then 1 else if a.val = 2 then 1 else
    if a.val = 3 then 1 else 0 : Fin 2)
  map_mul := by decide

def cyclicEmbedding4091 :
    Embedding Examples.cyclicTwo.semigroup Msg0521RepairedThirtyLawFinite.S6_4091.table.semigroup where
  toFun := fun (a : Fin 2) => (if a.val = 0 then 0 else 3 : Fin 6)
  map_mul := by decide
  injective := by intro a b; revert a b; decide

def cyclicEmbedding4297 :
    Embedding Examples.cyclicTwo.semigroup Msg0521RepairedThirtyLawFinite.S6_4297.table.semigroup where
  toFun := fun (a : Fin 2) => (if a.val = 0 then 0 else 1 : Fin 6)
  map_mul := by decide
  injective := by intro a b; revert a b; decide

theorem joint_injective4091 (a b : Fin 6)
    (ha : quotient4091.toFun a = quotient4091.toFun b)
    (hp : parity4091.toFun a = parity4091.toFun b) : a = b := by
  revert a b
  decide

theorem joint_injective4297 (a b : Fin 6)
    (ha : quotient4297.toFun a = quotient4297.toFun b)
    (hp : parity4297.toFun a = parity4297.toFun b) : a = b := by
  revert a b
  decide

/-- Pointwise separation lifts to arbitrary identities, with no word bound. -/
theorem valid_iff_joint_factors {S : Type u} {T : Type v} {U : Type w}
    {α : Type z} {G : Semigroup S} {H : Semigroup T} {K : Semigroup U}
    (q : SplitSurjection G H) (p : Hom G K) (i : Embedding K G)
    (separates : ∀ a b, q.toFun a = q.toFun b → p.toFun a = p.toFun b → a = b)
    (e : Identity α) :
    e.SatisfiedBy G ↔ e.SatisfiedBy H ∧ e.SatisfiedBy K := by
  constructor
  · intro valid
    exact ⟨q.pushforwardIdentity e valid, i.pullback_identity e valid⟩
  · rintro ⟨leftValid, rightValid⟩ valuation
    apply separates
    · exact (q.toHom.map_eval valuation e.lhs).trans
        ((leftValid _).trans (q.toHom.map_eval valuation e.rhs).symm)
    · exact (p.map_eval valuation e.lhs).trans
        ((rightValid _).trans (p.map_eval valuation e.rhs).symm)

theorem S6_4091_valid_iff_factors (e : Identity α) :
    e.SatisfiedBy Msg0521RepairedThirtyLawFinite.S6_4091.table.semigroup ↔
      e.SatisfiedBy S5_402.table.semigroup ∧ e.SatisfiedBy Examples.cyclicTwo.semigroup :=
  valid_iff_joint_factors quotient4091 parity4091 cyclicEmbedding4091
    joint_injective4091 e

theorem S6_4297_valid_iff_factors (e : Identity α) :
    e.SatisfiedBy Msg0521RepairedThirtyLawFinite.S6_4297.table.semigroup ↔
      e.SatisfiedBy S5_402.table.semigroup ∧ e.SatisfiedBy Examples.cyclicTwo.semigroup :=
  valid_iff_joint_factors quotient4297 parity4297 cyclicEmbedding4297
    joint_injective4297 e

theorem siblings_same_theory (e : Identity α) :
    e.SatisfiedBy Msg0521RepairedThirtyLawFinite.S6_4091.table.semigroup ↔
      e.SatisfiedBy Msg0521RepairedThirtyLawFinite.S6_4297.table.semigroup :=
  (S6_4091_valid_iff_factors e).trans (S6_4297_valid_iff_factors e).symm

/-- Reuse the existing arbitrary-word C2 normal forms, without a new screen
or any assumption of validity in either B30 sibling. -/
theorem cyclic_valid_of_parity (e : Identity Nat)
    (same : ∀ x, e.lhs.toList.count x % 2 = e.rhs.toList.count x % 2) :
    e.SatisfiedBy Examples.cyclicTwo.semigroup := by
  have reducedPerm := Examples.parityReduce_perm_of_parity_eq same
  have lhsNormal := Examples.cyclicDerivesNormal e.lhs
  have rhsNormal := Examples.cyclicDerivesNormal e.rhs
  have derivation : Derives Examples.cyclicTwoBasis e.lhs e.rhs := by
    cases hl : Examples.parityReduce e.lhs.toList with
    | nil =>
        rw [hl] at reducedPerm
        have hr : Examples.parityReduce e.rhs.toList = [] := reducedPerm.nil_eq.symm
        rw [hl] at lhsNormal
        rw [hr] at rhsNormal
        exact lhsNormal.trans <| (Examples.cyclicDerivesCommonSquare
          (Word.singleton e.lhs.head) (Word.singleton e.rhs.head)).trans rhsNormal.symm
    | cons x xs =>
        cases hr : Examples.parityReduce e.rhs.toList with
        | nil =>
            rw [hl, hr] at reducedPerm
            exact False.elim (List.not_perm_cons_nil reducedPerm)
        | cons y ys =>
            rw [hl] at lhsNormal
            rw [hr] at rhsNormal
            rw [hl, hr] at reducedPerm
            exact lhsNormal.trans <|
              (Examples.cyclicDerivesPermutation ⟨x, xs⟩ ⟨y, ys⟩ reducedPerm).trans
                rhsNormal.symm
  exact fun valuation => derivation.sound Examples.cyclicTwoBasis_models valuation

/-- The established S5_402 signature plus the exact count parity vector. -/
structure JointSignature (left right : Word Nat) : Prop where
  quotient : S5_402.SameSimpleSuccessorSignature left right
  parity : ∀ x, left.toList.count x % 2 = right.toList.count x % 2

theorem factors_iff_signature (e : Identity Nat) :
    (e.SatisfiedBy S5_402.table.semigroup ∧ e.SatisfiedBy Examples.cyclicTwo.semigroup) ↔
      JointSignature e.lhs e.rhs := by
  constructor
  · rintro ⟨ha, hp⟩
    exact ⟨S5_402.sameSignature_of_valid e ha, Examples.cyclicValid_parity_eq e hp⟩
  · intro same
    exact ⟨fun valuation => (S5_402.derivesOfSameSimpleSuccessorSignature same.quotient).sound
      S5_402.models valuation, cyclic_valid_of_parity e same.parity⟩

theorem S6_4091_valid_iff_signature (e : Identity Nat) :
    e.SatisfiedBy Msg0521RepairedThirtyLawFinite.S6_4091.table.semigroup ↔ JointSignature e.lhs e.rhs :=
  (S6_4091_valid_iff_factors e).trans (factors_iff_signature e)

theorem S6_4297_valid_iff_signature (e : Identity Nat) :
    e.SatisfiedBy Msg0521RepairedThirtyLawFinite.S6_4297.table.semigroup ↔ JointSignature e.lhs e.rhs :=
  (S6_4297_valid_iff_factors e).trans (factors_iff_signature e)

/-- Exact reduction of the OPEN B30 completeness problem. This theorem
does not prove the right-hand side. -/
theorem S6_4091_basisFor_iff_signature_derivable :
    BasisFor Msg0521RepairedThirtyLawFinite.S6_4091.table.semigroup Msg0521RepairedThirtyLawFinite.basis ↔
      ∀ left right : Word Nat, JointSignature left right → Derives Msg0521RepairedThirtyLawFinite.basis left right := by
  constructor
  · intro complete left right same
    exact complete.2 ⟨left, right⟩ ((S6_4091_valid_iff_signature ⟨left, right⟩).mpr same)
  · intro complete
    exact ⟨Msg0521RepairedThirtyLawFinite.S6_4091.tableModels, fun e valid =>
      complete e.lhs e.rhs ((S6_4091_valid_iff_signature e).mp valid)⟩

theorem S6_4297_basisFor_iff_signature_derivable :
    BasisFor Msg0521RepairedThirtyLawFinite.S6_4297.table.semigroup Msg0521RepairedThirtyLawFinite.basis ↔
      ∀ left right : Word Nat, JointSignature left right → Derives Msg0521RepairedThirtyLawFinite.basis left right := by
  constructor
  · intro complete left right same
    exact complete.2 ⟨left, right⟩ ((S6_4297_valid_iff_signature ⟨left, right⟩).mpr same)
  · intro complete
    exact ⟨Msg0521RepairedThirtyLawFinite.S6_4297.tableModels, fun e valid =>
      complete e.lhs e.rhs ((S6_4297_valid_iff_signature e).mp valid)⟩

end SemigroupBasis.CoRoots.Order6Sunday.Msg0604B30JointSignature

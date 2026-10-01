import SemigroupBasis.Normalization.JointCompleteness

/-!
# Shared exact-Sigma normalization for the one-local Ford/last family

The proof-reduction DAG groups these obligations by a bounded one-local
descriptor.  That descriptor is useful for synthesis, but it is not itself a
necessity theorem: some displayed axioms change the raw first-occurrence
sequence or final letter.  Consequently this module does not identify the DAG
label with a semantic invariant.

Instead, a `ReachPlan` is indexed by an arbitrary key whose necessity is proved
from the two factor theories.  This is the strongest sound common interface:

* staged lower-order normalizers produce a plan with `ofStages`;
* plans transport when the exact target Sigma derives the source axioms;
* reversing every word transports a plan to the anti-isomorphic system;
* a completed plan packages directly as an `IntersectionBasis`.

The generated family modules instantiate this interface with the exact 23
displayed systems and expose every displayed axiom as a reusable derivation.
-/

namespace SemigroupBasis
namespace OneLocalFordLast

universe u v w x y

open JointCompleteness

/-- A named law together with its derivation from one exact displayed system. -/
structure DerivedLaw (basis : List (Identity Nat)) where
  identity : Identity Nat
  derives : Derives basis identity.lhs identity.rhs

namespace DerivedLaw

/-- Apply an arbitrary word substitution to a recorded exact-Sigma law. -/
theorem instantiate {basis : List (Identity Nat)}
    (law : DerivedLaw basis) (substitution : Nat → Word Nat) :
    Derives basis
      (law.identity.lhs.bind substitution)
      (law.identity.rhs.bind substitution) :=
  Derives.subst law.derives substitution

/-- Reverse a recorded law and its derivation. -/
def reversed {basis : List (Identity Nat)}
    (law : DerivedLaw basis) :
    DerivedLaw (reversedBasis basis) where
  identity := law.identity.reversed
  derives := law.derives.reverse

end DerivedLaw

/-- A complete exact-Sigma reach witness indexed by a proven semantic key. -/
structure ReachPlan (basis : List (Identity Nat)) (Key : Type w) where
  key : Word Nat → Key
  render : Key → Word Nat
  reach : ∀ word, Derives basis word (render (key word))

namespace ReachPlan

/-- Package an existing normalizer as a one-step reach plan. -/
def ofNormalizer {basis : List (Identity Nat)} {Key : Type w}
    (key : Word Nat → Key) (render : Key → Word Nat)
    (reach : ∀ word, Derives basis word (render (key word))) :
    ReachPlan basis Key where
  key := key
  render := render
  reach := reach

/-- Package a derivable staged normalization pipeline as a reach plan. -/
def ofStages {basis : List (Identity Nat)} {Key : Type w}
    (stages : List (Normalization.Stage
      (Normalization.derivesSystem basis) (Word Nat) id))
    (key : Word Nat → Key) (render : Key → Word Nat)
    (normalized :
      ∀ word, Normalization.runStages stages word = render (key word)) :
    ReachPlan basis Key where
  key := key
  render := render
  reach := fun word =>
    (normalized word) ▸ Normalization.runStages_sound stages word

/-- Reuse a reach plan in any exact target system deriving all source axioms. -/
def retarget {source target : List (Identity Nat)} {Key : Type w}
    (plan : ReachPlan source Key)
    (sourceAxiomsDerive :
      ∀ identity : Identity Nat, identity ∈ source →
        Derives target identity.lhs identity.rhs) :
    ReachPlan target Key where
  key := plan.key
  render := plan.render
  reach := fun word =>
    Derives.transport sourceAxiomsDerive (plan.reach word)

/-- Conjugate a reach plan by word reversal. -/
def reversed {basis : List (Identity Nat)} {Key : Type w}
    (plan : ReachPlan basis Key) :
    ReachPlan (reversedBasis basis) Key where
  key := fun word => plan.key word.reverse
  render := fun key => (plan.render key).reverse
  reach := fun word => by
    have reversedReach := (plan.reach word.reverse).reverse
    simpa using reversedReach

end ReachPlan

/-- Joint completeness when the two factor theories determine a plan's key. -/
theorem obligation_of_key
    {A : Type u} {B : Type v}
    {G : Semigroup A} {H : Semigroup B}
    {basis : List (Identity Nat)} {Key : Type w}
    (plan : ReachPlan basis Key)
    (keyNecessary :
      ∀ left right : Word Nat,
        (∀ valuation : Nat → A,
          G.eval valuation left = G.eval valuation right) →
        (∀ valuation : Nat → B,
          H.eval valuation left = H.eval valuation right) →
        plan.key left = plan.key right) :
    DerivationalObligation G H basis :=
  obligation_of_normalizer
    (fun word => plan.render (plan.key word))
    (fun left right leftValid rightValid =>
      congrArg plan.render
        (keyNecessary left right leftValid rightValid))
    plan.reach

/-- Production form using the necessity halves of two sealed factor profiles. -/
theorem obligation_of_merged_factor_plan
    {A : Type u} {B : Type v}
    {G : Semigroup A} {H : Semigroup B}
    {basis : List (Identity Nat)} {Key : Type w}
    {PG : Type x} {PH : Type y}
    (leftProfile : FactorProfile G PG)
    (rightProfile : FactorProfile H PH)
    (merge : PG × PH → Key)
    (plan : ReachPlan basis Key)
    (key_eq :
      ∀ word,
        plan.key word =
          merge (leftProfile.φ word, rightProfile.φ word)) :
    DerivationalObligation G H basis :=
  obligation_of_key plan
    (fun left right leftValid rightValid => by
      calc
        plan.key left =
            merge (leftProfile.φ left, rightProfile.φ left) :=
          key_eq left
        _ = merge (leftProfile.φ right, rightProfile.φ right) := by
          rw [leftProfile.nec left right leftValid,
            rightProfile.nec left right rightValid]
        _ = plan.key right := (key_eq right).symm)

/-- Package a merged factor plan as the intersection basis used by endpoints. -/
def intersectionBasis_of_merged_factor_plan
    {A : Type u} {B : Type v}
    {G : Semigroup A} {H : Semigroup B}
    {basis : List (Identity Nat)} {Key : Type w}
    {PG : Type x} {PH : Type y}
    (leftModels : Models G basis)
    (rightModels : Models H basis)
    (leftProfile : FactorProfile G PG)
    (rightProfile : FactorProfile H PH)
    (merge : PG × PH → Key)
    (plan : ReachPlan basis Key)
    (key_eq :
      ∀ word,
        plan.key word =
          merge (leftProfile.φ word, rightProfile.φ word)) :
    IntersectionBasis G H basis where
  leftModels := leftModels
  rightModels := rightModels
  complete :=
    obligation_of_merged_factor_plan
      leftProfile rightProfile merge plan key_eq

/-- Retarget a complete factor intersection to an exact system deriving every
source axiom.  Soundness of the target system remains explicit. -/
def retargetIntersectionBasis
    {A : Type u} {B : Type v}
    {G : Semigroup A} {H : Semigroup B}
    {source target : List (Identity Nat)}
    (intersection : IntersectionBasis G H source)
    (leftModels : Models G target)
    (rightModels : Models H target)
    (sourceAxiomsDerive :
      ∀ identity : Identity Nat, identity ∈ source →
        Derives target identity.lhs identity.rhs) :
    IntersectionBasis G H target where
  leftModels := leftModels
  rightModels := rightModels
  complete := fun identity leftValid rightValid =>
    Derives.transport sourceAxiomsDerive
      (intersection.complete identity leftValid rightValid)

end OneLocalFordLast
end SemigroupBasis

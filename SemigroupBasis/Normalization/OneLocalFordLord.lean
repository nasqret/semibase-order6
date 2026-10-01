import SemigroupBasis.CoRoots.S5_1089Normalization
import SemigroupBasis.Normalization.JointCompleteness

/-!
# Shared staged normalization for the one-local Ford/Lord family

The order-six proof-reduction DAG labels a joint obligation
`one-local-ford-lord` when equality in its two factors determines:

* first-occurrence order (`ford`);
* last-occurrence order (`lord`);
* each letter count modulo the common index/period law.

This file contains the proof architecture shared by every such obligation.
The factor-specific input is only a pair of sealed `FactorProfile`s and a
proof that their merged profile is the one-local profile below.  The
displayed-system-specific input is only a `ReachPlan`: a sequence of
derivable normalization stages reaching a word rendered from that profile.

In particular, this file does not assume that either factor basis is
derivable from the displayed intersection basis.  Factor normalizers are
used for semantic determinacy; all syntactic rewriting remains inside the
exact displayed system.
-/

namespace SemigroupBasis
namespace OneLocalFordLord

open SemigroupBasis.Examples

universe u v w x

/-- The joint invariant recorded by the `one-local-ford-lord` descriptor. -/
structure Profile (t p : Nat) where
  ford : List Nat
  lord : List Nat
  cappedCounts : Nat → Nat

/-- Compute the joint invariant of a nonempty `Nat`-word. -/
def profile (t p : Nat) (word : Word Nat) : Profile t p where
  ford := firstOccurrenceSequence word.toList
  lord := SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence word.toList
  cappedCounts := fun letter =>
    JointCompleteness.capped t p (word.toList.count letter)

/-- The exact derivational input still required from one displayed Sigma.

Every stage must be sound for `Derives basis`; `normalized` is the purely
computational assertion that the completed pipeline depends only on the
Ford/Lord/count profile.
-/
structure ReachPlan (basis : List (Identity Nat)) (t p : Nat) where
  stages : List (Normalization.Stage
    (Normalization.derivesSystem basis) (Word Nat) id)
  render : Profile t p → Word Nat
  normalized :
    ∀ word,
      Normalization.runStages stages word = render (profile t p word)

/-- Joint completeness when factor semantics directly determine the shared
one-local profile. -/
theorem obligation_of_profile_stages
    {A : Type u} {B : Type v}
    {G : Semigroup A} {H : Semigroup B}
    {basis : List (Identity Nat)} {t p : Nat}
    (profileNecessary :
      ∀ left right : Word Nat,
        (∀ valuation : Nat → A,
          G.eval valuation left = G.eval valuation right) →
        (∀ valuation : Nat → B,
          H.eval valuation left = H.eval valuation right) →
        profile t p left = profile t p right)
    (plan : ReachPlan basis t p) :
    JointCompleteness.DerivationalObligation G H basis :=
  JointCompleteness.obligation_of_normalizer
    (fun word => plan.render (profile t p word))
    (fun left right hG hH =>
      congrArg plan.render (profileNecessary left right hG hH))
    (fun word => by
      have reach := Normalization.runStages_sound plan.stages word
      rw [plan.normalized word] at reach
      exact reach)

/-- Production form: reuse the necessity halves of two sealed factor
normalizers, merge their profiles, and supply only the exact-Sigma reach plan.
-/
theorem obligation_of_merged_factor_stages
    {A : Type u} {B : Type v}
    {G : Semigroup A} {H : Semigroup B}
    {basis : List (Identity Nat)} {t p : Nat}
    {PG : Type w} {PH : Type x}
    (leftProfile : JointCompleteness.FactorProfile G PG)
    (rightProfile : JointCompleteness.FactorProfile H PH)
    (merge : PG × PH → Profile t p)
    (merge_profile :
      ∀ word,
        merge (leftProfile.φ word, rightProfile.φ word) =
          profile t p word)
    (plan : ReachPlan basis t p) :
    JointCompleteness.DerivationalObligation G H basis :=
  JointCompleteness.obligation_of_stages
    leftProfile rightProfile plan.stages
    (fun pair => plan.render (merge pair))
    (fun word =>
      (plan.normalized word).trans
        (congrArg plan.render (merge_profile word).symm))

/-- Package the shared theorem as the intersection basis consumed by every
subdirect endpoint wrapper. -/
def intersectionBasis_of_merged_factor_stages
    {A : Type u} {B : Type v}
    {G : Semigroup A} {H : Semigroup B}
    {basis : List (Identity Nat)} {t p : Nat}
    {PG : Type w} {PH : Type x}
    (leftModels : Models G basis)
    (rightModels : Models H basis)
    (leftProfile : JointCompleteness.FactorProfile G PG)
    (rightProfile : JointCompleteness.FactorProfile H PH)
    (merge : PG × PH → Profile t p)
    (merge_profile :
      ∀ word,
        merge (leftProfile.φ word, rightProfile.φ word) =
          profile t p word)
    (plan : ReachPlan basis t p) :
    IntersectionBasis G H basis where
  leftModels := leftModels
  rightModels := rightModels
  complete :=
    obligation_of_merged_factor_stages
      leftProfile rightProfile merge merge_profile plan

/-- Reuse a complete factor intersection in an exact target system that
derives every source law.  Target soundness remains explicit; the source
normalizer is transported only through recorded `Derives` proofs. -/
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

end OneLocalFordLord
end SemigroupBasis

import SemigroupBasis.TransferPower
import SemigroupBasis.Opposite

namespace SemigroupBasis

/-- A semigroup represented subdirectly by two factors: both coordinate maps
are surjective homomorphisms, and together they separate source elements. -/
structure SubdirectPair {A : Type u} {B : Type v} {C : Type w}
    (G : Semigroup A) (H : Semigroup B) (K : Semigroup C) where
  left : SplitSurjection G H
  right : SplitSurjection G K
  jointlyInjective :
    Function.Injective fun value =>
      (left.toFun value, right.toFun value)

namespace SubdirectPair

/-- An identity holds in a subdirect product exactly when it holds in both
factors. -/
theorem satisfiedBy_iff
    {A : Type u} {B : Type v} {C : Type w} {α : Type z}
    {G : Semigroup A} {H : Semigroup B} {K : Semigroup C}
    (pair : SubdirectPair G H K) (identity : Identity α) :
    identity.SatisfiedBy G ↔
      identity.SatisfiedBy H ∧ identity.SatisfiedBy K := by
  constructor
  · intro valid
    exact
      ⟨pair.left.pushforwardIdentity identity valid,
        pair.right.pushforwardIdentity identity valid⟩
  · rintro ⟨leftValid, rightValid⟩
    intro valuation
    apply pair.jointlyInjective
    apply Prod.ext
    · change
        pair.left.toFun (G.eval valuation identity.lhs) =
          pair.left.toFun (G.eval valuation identity.rhs)
      rw [pair.left.toHom.map_eval, pair.left.toHom.map_eval]
      exact leftValid (fun name => pair.left.toFun (valuation name))
    · change
        pair.right.toFun (G.eval valuation identity.lhs) =
          pair.right.toFun (G.eval valuation identity.rhs)
      rw [pair.right.toHom.map_eval, pair.right.toHom.map_eval]
      exact rightValid (fun name => pair.right.toFun (valuation name))

/-- A subdirect representation reduces completeness to a common normal form:
the basis normalizes both sides, while the two factors jointly determine that
the normal forms of every valid identity coincide. -/
theorem basisFor_of_normalForm
    {A : Type u} {B : Type v} {C : Type w} {α : Type z}
    {G : Semigroup A} {H : Semigroup B} {K : Semigroup C}
    {basis : List (Identity α)} {normal : Word α → Word α}
    (pair : SubdirectPair G H K)
    (models : Models G basis)
    (normalizes : ∀ word, Derives basis word (normal word))
    (separates :
      ∀ identity : Identity α,
        identity.SatisfiedBy H →
          identity.SatisfiedBy K →
            normal identity.lhs = normal identity.rhs) :
    BasisFor G basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  have factorValid := (pair.satisfiedBy_iff identity).mp valid
  have sameNormal := separates identity factorValid.1 factorValid.2
  apply Derives.trans (normalizes identity.lhs)
  simpa only [sameNormal] using Derives.symm (normalizes identity.rhs)

end SubdirectPair

/-- Transport a complete basis between two semigroups whose two subdirect
factor theories agree coordinatewise. -/
theorem BasisFor.transferAcrossSubdirectPairs
    {A : Type u} {B : Type v} {C : Type w}
    {A' : Type q} {B' : Type r} {C' : Type s} {α : Type z}
    {G : Semigroup A} {H : Semigroup B} {K : Semigroup C}
    {G' : Semigroup A'} {H' : Semigroup B'} {K' : Semigroup C'}
    {basis : List (Identity α)}
    (sourceBasis : BasisFor G basis)
    (sourcePair : SubdirectPair G H K)
    (targetPair : SubdirectPair G' H' K')
    (leftTheory :
      ∀ identity : Identity α,
        identity.SatisfiedBy H ↔ identity.SatisfiedBy H')
    (rightTheory :
      ∀ identity : Identity α,
        identity.SatisfiedBy K ↔ identity.SatisfiedBy K') :
    BasisFor G' basis := by
  refine ⟨?_, ?_⟩
  · intro identity member
    have sourceValid := sourceBasis.1 identity member
    have factorValid := (sourcePair.satisfiedBy_iff identity).mp sourceValid
    apply (targetPair.satisfiedBy_iff identity).mpr
    exact
      ⟨(leftTheory identity).mp factorValid.1,
        (rightTheory identity).mp factorValid.2⟩
  · intro identity targetValid
    have targetFactorValid :=
      (targetPair.satisfiedBy_iff identity).mp targetValid
    have sourceValid : identity.SatisfiedBy G :=
      (sourcePair.satisfiedBy_iff identity).mpr
        ⟨(leftTheory identity).mpr targetFactorValid.1,
          (rightTheory identity).mpr targetFactorValid.2⟩
    exact sourceBasis.2 identity sourceValid

/-- A basis for the intersection of two factor identity theories. -/
structure IntersectionBasis {B : Type v} {C : Type w} {α : Type z}
    (H : Semigroup B) (K : Semigroup C)
    (basis : List (Identity α)) : Prop where
  leftModels : Models H basis
  rightModels : Models K basis
  complete :
    ∀ identity : Identity α,
      identity.SatisfiedBy H →
        identity.SatisfiedBy K →
          Derives basis identity.lhs identity.rhs

namespace IntersectionBasis

/-- An intersection basis is a basis for every semigroup subdirectly
represented by its two factors. -/
theorem basisFor
    {A : Type u} {B : Type v} {C : Type w} {α : Type z}
    {G : Semigroup A} {H : Semigroup B} {K : Semigroup C}
    {basis : List (Identity α)}
    (intersection : IntersectionBasis H K basis)
    (pair : SubdirectPair G H K) :
    BasisFor G basis := by
  refine ⟨?_, ?_⟩
  · intro identity member
    apply (pair.satisfiedBy_iff identity).2
    exact
      ⟨intersection.leftModels identity member,
        intersection.rightModels identity member⟩
  · intro identity valid
    have factorValid := (pair.satisfiedBy_iff identity).1 valid
    exact intersection.complete identity factorValid.1 factorValid.2

/-- Reversing every word dualizes a complete factor-theory intersection. -/
theorem oppositeReversed
    {B : Type v} {C : Type w} {α : Type z}
    {H : Semigroup B} {K : Semigroup C}
    {basis : List (Identity α)}
    (intersection : IntersectionBasis H K basis) :
    IntersectionBasis H.opposite K.opposite (reversedBasis basis) where
  leftModels := intersection.leftModels.oppositeReversed
  rightModels := intersection.rightModels.oppositeReversed
  complete := by
    intro identity leftValid rightValid
    have leftReversed : identity.reversed.SatisfiedBy H :=
      (Identity.satisfiedBy_opposite_iff_reversed identity H).mp leftValid
    have rightReversed : identity.reversed.SatisfiedBy K :=
      (Identity.satisfiedBy_opposite_iff_reversed identity K).mp rightValid
    have derivation :=
      (intersection.complete identity.reversed leftReversed rightReversed).reverse
    cases identity
    simpa [Identity.reversed] using derivation

/-- Dualize the left factor when the source intersection already uses the
opposite of the right factor. -/
theorem oppositeLeftOfOppositeRight
    {B : Type v} {C : Type w} {α : Type z}
    {H : Semigroup B} {K : Semigroup C}
    {basis : List (Identity α)}
    (intersection : IntersectionBasis H K.opposite basis) :
    IntersectionBasis H.opposite K (reversedBasis basis) where
  leftModels := intersection.leftModels.oppositeReversed
  rightModels := by
    intro reversedIdentity member
    obtain ⟨identity, identityMember, rfl⟩ := List.mem_map.mp member
    exact
      (Identity.satisfiedBy_opposite_iff_reversed identity K).mp
        (intersection.rightModels identity identityMember)
  complete := by
    intro identity leftValid rightValid
    have leftReversed : identity.reversed.SatisfiedBy H :=
      (Identity.satisfiedBy_opposite_iff_reversed identity H).mp leftValid
    have rightReversed :
        identity.reversed.SatisfiedBy K.opposite := by
      apply
        (Identity.satisfiedBy_opposite_iff_reversed identity.reversed K).mpr
      simpa using rightValid
    have derivation :=
      (intersection.complete identity.reversed leftReversed rightReversed).reverse
    cases identity
    simpa [Identity.reversed] using derivation

/-- Replace either factor by a semigroup with the same identity theory. -/
theorem transferTheories
    {B : Type v} {C : Type w} {B' : Type q} {C' : Type r}
    {α : Type z}
    {H : Semigroup B} {K : Semigroup C}
    {H' : Semigroup B'} {K' : Semigroup C'}
    {basis : List (Identity α)}
    (intersection : IntersectionBasis H K basis)
    (leftTheory :
      ∀ identity : Identity α,
        identity.SatisfiedBy H ↔ identity.SatisfiedBy H')
    (rightTheory :
      ∀ identity : Identity α,
        identity.SatisfiedBy K ↔ identity.SatisfiedBy K') :
    IntersectionBasis H' K' basis where
  leftModels := by
    intro identity member
    exact (leftTheory identity).mp
      (intersection.leftModels identity member)
  rightModels := by
    intro identity member
    exact (rightTheory identity).mp
      (intersection.rightModels identity member)
  complete := by
    intro identity leftValid rightValid
    exact intersection.complete identity
      ((leftTheory identity).mpr leftValid)
      ((rightTheory identity).mpr rightValid)

end IntersectionBasis

namespace FactorPair

/-- A pair of split factor maps with jointly injective coordinates inherits a
complete basis for the intersection of the two factor theories. -/
theorem basisFor_of_split_factor_pair
    {A : Type u} {B : Type v} {C : Type w} {alpha : Type z}
    {G : Semigroup A} {H : Semigroup B} {K : Semigroup C}
    {basis : List (Identity alpha)}
    (left : SplitSurjection G H)
    (right : SplitSurjection G K)
    (joint :
      Function.Injective fun value =>
        (left.toFun value, right.toFun value))
    (leftModels : Models H basis)
    (rightModels : Models K basis)
    (jointComplete :
      forall e : Identity alpha,
        e.SatisfiedBy H ->
        e.SatisfiedBy K ->
        Derives basis e.lhs e.rhs) :
    BasisFor G basis := by
  refine' ⟨_, fun e he => _⟩
  · intro e he
    intro valuation
    refine' joint _
    simp +decide [Hom.map_eval]
    exact ⟨leftModels e he _, rightModels e he _⟩
  · apply jointComplete e
    · exact SplitSurjection.pushforwardIdentity left e he
    · exact SplitSurjection.pushforwardIdentity right e he

end FactorPair

end SemigroupBasis

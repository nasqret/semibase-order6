import SemigroupBasis.CoRoots.Order6FactorPairS4_116opS5_841
import SemigroupBasis.CoRoots.S5_841
import SemigroupBasis.Generated.S3_16
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Transfer

/-!
# Reusing the `S4_116^op`/`S5_841` intersection

Dualizing the existing intersection basis gives a basis for `S4_116` and
`S5_841^op`. The explicit involutive anti-automorphism of `S5_841` restores
the right factor. Finally, `S4_116` and `S3_16` have the same identity
theory because both have the same complete left-regular-band basis.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS5_841Reuse

open SemigroupBasis
open SemigroupBasis.Examples

private def reverseInvolutiveEmbedding
    {A : Type u} {G H : Semigroup A}
    (embedding : Embedding G H)
    (involution :
      forall value, embedding.toFun (embedding.toFun value) = value) :
    Embedding H G where
  toFun := embedding.toFun
  map_mul := by
    intro left right
    apply embedding.injective
    rw [involution, embedding.map_mul, involution, involution]
  injective := embedding.injective

private theorem sameIdentityTheoryOverOfMutualEmbeddings
    {A : Type u} {B : Type v} {X : Type w}
    {G : Semigroup A} {H : Semigroup B}
    (intoH : Embedding G H) (intoG : Embedding H G) :
    SameIdentityTheoryOver G H X := by
  intro identity
  exact
    Iff.intro
      (fun validInG => intoG.pullback_identity identity validInG)
      (fun validInH => intoH.pullback_identity identity validInH)

private theorem sameIdentityTheoryOverOfCommonBasis
    {A : Type u} {B : Type v} {X : Type w}
    {G : Semigroup A} {H : Semigroup B}
    {basis : List (Identity X)}
    (basisForG : BasisFor G basis) (basisForH : BasisFor H basis) :
    SameIdentityTheoryOver G H X := by
  intro identity
  constructor
  · intro validInG valuation
    exact Derives.sound basisForH.1
      (basisForG.2 identity validInG) valuation
  · intro validInH valuation
    exact Derives.sound basisForG.1
      (basisForH.2 identity validInH) valuation

private def s3_16IntoS4_116 :
    Embedding
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup where
  toFun := fun value : Fin 3 =>
    if value = 0 then (1 : Fin 4)
    else if value = 1 then (2 : Fin 4)
    else (3 : Fin 4)
  map_mul := by decide
  injective := by
    intro left right
    exact by decide +revert

private def s4_116FiniteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

private def s4_116FiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

private theorem s4_116FiniteLaw0Map :
    s4_116FiniteLaw0.map Fin.val = lrbIdempotenceLaw := rfl

private theorem s4_116FiniteLaw1Map :
    s4_116FiniteLaw1.map Fin.val = lrbRegularLaw := rfl

private theorem s4_116Models :
    Models
      SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup
      leftRegularBandThreeBasis := by
  intro identity member
  simp only [
    leftRegularBandThreeBasis,
    List.mem_cons,
    List.not_mem_nil,
    or_false,
  ] at member
  rcases member with member | member
  · subst identity
    rw [← s4_116FiniteLaw0Map]
    exact
      SemigroupBasis.Generated.Catalogue.S4_116.table.checkIdentityNat_sound
        s4_116FiniteLaw0 (by decide)
  · subst identity
    rw [← s4_116FiniteLaw1Map]
    exact
      SemigroupBasis.Generated.Catalogue.S4_116.table.checkIdentityNat_sound
        s4_116FiniteLaw1 (by decide)

private theorem s4_116Basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup
      leftRegularBandThreeBasis :=
  SemigroupBasis.Generated.S3_16.representative_basis.inheritAlongEmbedding
    s3_16IntoS4_116 s4_116Models

/-- The involutive self-duality also supplies the reverse embedding. -/
def s5_841IntoOpposite :
    Embedding
      SemigroupBasis.CoRoots.S5_841.table.semigroup
      SemigroupBasis.CoRoots.S5_841.table.semigroup.opposite :=
  reverseInvolutiveEmbedding
    SemigroupBasis.CoRoots.S5_841.selfDuality
    SemigroupBasis.CoRoots.S5_841.antiAutomorphism_involutive

/-- `S5_841` and its opposite have the same unrestricted identity theory. -/
theorem sameTheoryS5_841Opposite :
    SameIdentityTheoryOver
      SemigroupBasis.CoRoots.S5_841.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_841.table.semigroup
      Nat :=
  sameIdentityTheoryOverOfMutualEmbeddings
    SemigroupBasis.CoRoots.S5_841.selfDuality
    s5_841IntoOpposite

/-- `S4_116` and `S3_16` share the complete left-regular-band basis. -/
theorem sameTheoryS4_116S3_16 :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup
      SemigroupBasis.Generated.S3_16.table.semigroup
      Nat :=
  sameIdentityTheoryOverOfCommonBasis
    s4_116Basis
    SemigroupBasis.Generated.S3_16.representative_basis

/-- Alternative reversed basis for `S4_116` and `S5_841`. -/
def s4_116S5_841IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup
      SemigroupBasis.CoRoots.S5_841.table.semigroup
      (reversedBasis
        SemigroupBasis.CoRoots.Order6FactorPairS4_116opS5_841.basis) :=
  (SemigroupBasis.IntersectionBasis.oppositeReversed
    SemigroupBasis.CoRoots.Order6FactorPairS4_116opS5_841.intersectionBasis
  ).transferTheories
    (fun _ => Iff.rfl)
    sameTheoryS5_841Opposite

/-- The same alternative basis after replacing `S4_116` by `S3_16`. -/
def s3_16S5_841IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.CoRoots.S5_841.table.semigroup
      (reversedBasis
        SemigroupBasis.CoRoots.Order6FactorPairS4_116opS5_841.basis) :=
  s4_116S5_841IntersectionBasis.transferTheories
    sameTheoryS4_116S3_16
    (fun _ => Iff.rfl)

end SemigroupBasis.CoRoots.Order6FactorPairS5_841Reuse

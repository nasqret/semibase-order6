import SemigroupBasis.CoRoots.Order6S5_107InitialIntersectionFamilies
import SemigroupBasis.CoRoots.S5_107Basis

/-!
# The `S2_4 x S5_108^op` initial intersection

The order-five semigroup `S5_107` is self-dual, while its reversed complete
basis is also complete for `S5_108^op`.  Consequently `S5_107` and
`S5_108^op` have the same unrestricted identity theory.  This transfers the
existing `S2_4 x S5_107` intersection basis without another normal-form proof.
-/

namespace SemigroupBasis.CoRoots.Order6S5_108OppositeInitialIntersection

open SemigroupBasis

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6S5_107InitialIntersectionFamilies.basis

private theorem sameIdentityTheoryOverOfCommonBasis
    {A : Type u} {B : Type v} {X : Type w}
    {G : Semigroup A} {H : Semigroup B}
    {commonBasis : List (Identity X)}
    (basisForG : BasisFor G commonBasis)
    (basisForH : BasisFor H commonBasis) :
    SameIdentityTheoryOver G H X := by
  intro identity
  constructor
  · intro validInG valuation
    exact Derives.sound basisForH.1
      (basisForG.2 identity validInG) valuation
  · intro validInH valuation
    exact Derives.sound basisForG.1
      (basisForH.2 identity validInH) valuation

private theorem s5_107SelfDual :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup.opposite Nat := by
  let onto :
      SplitSurjection
        SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup.opposite
        SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup :=
    { toFun :=
        SemigroupBasis.CoRoots.S5_107Family.S5_107.selfDualEmbedding.toFun
      map_mul :=
        SemigroupBasis.CoRoots.S5_107Family.S5_107.selfDualEmbedding.map_mul
      preimage :=
        SemigroupBasis.CoRoots.S5_107Family.S5_107.selfDualEmbedding.toFun
      right_inverse :=
        SemigroupBasis.CoRoots.S5_107Family.S5_107.selfDualInvolution }
  intro identity
  constructor
  · exact
      SemigroupBasis.CoRoots.S5_107Family.S5_107.selfDualEmbedding.pullback_identity
        identity
  · exact onto.pushforwardIdentity identity

private theorem oppositeFamily :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup.opposite Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.CoRoots.S5_107Family.S5_107.basisFor.oppositeReversed
    SemigroupBasis.CoRoots.S5_107Family.S5_108.oppositeBasisFor

theorem s5_107_s5_108Opposite_sameTheory :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup.opposite Nat := by
  intro identity
  exact (s5_107SelfDual identity).trans (oppositeFamily identity)

theorem modelsS5_108Opposite :
    Models
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup.opposite basis := by
  intro identity member
  exact
    (s5_107_s5_108Opposite_sameTheory identity).mp
      (SemigroupBasis.CoRoots.Order6S5_107InitialIntersectionFamilies.modelsS5_107
        identity member)

def intersectionS2_4S5_108Opposite :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup.opposite basis where
  leftModels :=
    SemigroupBasis.CoRoots.Order6S5_107InitialIntersectionFamilies.modelsS2_4
  rightModels := modelsS5_108Opposite
  complete := by
    intro identity initialValid oppositeValid
    exact
      SemigroupBasis.CoRoots.Order6S5_107InitialIntersectionFamilies.intersectionS2_4S5_107.complete
        identity initialValid
        ((s5_107_s5_108Opposite_sameTheory identity).mpr oppositeValid)

end SemigroupBasis.CoRoots.Order6S5_108OppositeInitialIntersection

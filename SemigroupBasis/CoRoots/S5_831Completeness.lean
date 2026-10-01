import SemigroupBasis.CoRoots.S5_831Semantics

namespace SemigroupBasis.CoRoots.S5_831

open SemigroupBasis

/-- Generic completeness bridge for the phase occupancy canonical form. -/
theorem basis_complete_of_signature
    {S : Type}
    (semigroup : Semigroup S)
    (modelsSemigroup : Models semigroup basis)
    (validSignature :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy semigroup →
          SamePhaseOccupancySignature
            identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨modelsSemigroup, ?_⟩
  intro identity valid
  have leftNormal := derivesCanonical identity.lhs
  have rightNormal := derivesCanonical identity.rhs
  have canonicalEqual :=
    (validSignature identity valid).canonicalWord_eq
  exact leftNormal.trans <| by
    rw [canonicalEqual]
    exact rightNormal.symm

/-- Unconditional representative endpoint for `S5_831`. -/
theorem basis_complete :
    BasisFor Generated.Catalogue.S5_831.table.semigroup basis :=
  basis_complete_of_signature
    Generated.Catalogue.S5_831.table.semigroup
    models valid_samePhaseOccupancySignature

/-- Unconditional opposite endpoint with the exact reversed basis
`xx = xxx; xyx = yyx`. -/
theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_831.table.semigroup.opposite
      expectedOppositeBasis := by
  rw [← reversedBasis_eq_expected]
  exact basis_complete.oppositeReversed

/-- The generated congruence is exactly equality of first-occurrence phase
profiles. -/
theorem derives_iff_samePhaseOccupancySignature
    {left right : Word Nat} :
    Derives basis left right ↔
      SamePhaseOccupancySignature left right := by
  constructor
  · intro derivation
    have valid :
        (Identity.mk left right).SatisfiedBy
          Generated.Catalogue.S5_831.table.semigroup :=
      fun valuation => derivation.sound models valuation
    exact valid_samePhaseOccupancySignature
      (Identity.mk left right) valid
  · intro same
    have leftNormal := derivesCanonical left
    have rightNormal := derivesCanonical right
    exact leftNormal.trans <| by
      rw [same.canonicalWord_eq]
      exact rightNormal.symm

end SemigroupBasis.CoRoots.S5_831

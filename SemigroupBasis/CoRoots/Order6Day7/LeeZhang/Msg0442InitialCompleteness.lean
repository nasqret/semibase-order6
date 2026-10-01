import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442InitialRules

/-! The shared initial-marker argument is instantiated with the actual
S5_83/S5_84/S5_240 lower bases and closed left-reductivity proofs. All five
literal classes receive unconditional representative and reverse endpoints. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Initial

open SemigroupBasis

namespace Group1040

theorem complete83 (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy markerTable.semigroup)
    (rightValid : identity.SatisfiedBy right83.semigroup) : Derives basis identity.lhs identity.rhs :=
  rules.complete right83.semigroup right83Models S5_83Family.S5_83.basis_complete
    right83LeftReductive identity markerValid rightValid

def intersection83 : IntersectionBasis markerTable.semigroup right83.semigroup basis where
  leftModels := markerModels
  rightModels := right83Models
  complete := complete83

noncomputable def normalizer83 : IntersectionNormalizer markerTable.semigroup right83.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer intersection83

theorem right84To83 (identity : Identity Nat) (valid : identity.SatisfiedBy right84.semigroup) :
    identity.SatisfiedBy right83.semigroup :=
  Derives.sound S5_83Family.S5_83.models (S5_83Family.S5_84.basis_complete.2 identity valid)

/-- The actual independently complete lower theories justify the transport;
the distinct S5_83 and S5_84 literal tables are not identified. -/
noncomputable def normalizer84 : IntersectionNormalizer markerTable.semigroup right84.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer normalizer83
    (fun _ member => Derives.fromBasis member) (fun _ valid => valid) right84To83

noncomputable def intersection84 : IntersectionBasis markerTable.semigroup right84.semigroup basis :=
  normalizer84.toIntersectionBasis markerModels right84Models

theorem complete84 (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy markerTable.semigroup)
    (rightValid : identity.SatisfiedBy right84.semigroup) : Derives basis identity.lhs identity.rhs :=
  intersection84.complete identity markerValid rightValid

noncomputable def oppositeNormalizer83 :
    IntersectionNormalizer markerTable.semigroup.opposite right83.semigroup.opposite (reversedBasis basis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer intersection83.oppositeReversed
noncomputable def oppositeNormalizer84 :
    IntersectionNormalizer markerTable.semigroup.opposite right84.semigroup.opposite (reversedBasis basis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer intersection84.oppositeReversed

theorem representative_basis1040 : BasisFor table1040.semigroup basis :=
  normalizer83.basisFor markerModels right83Models subdirect1040
theorem representative_basis1042 : BasisFor table1042.semigroup basis :=
  normalizer84.basisFor markerModels right84Models subdirect1042
theorem representative_basis1098 : BasisFor table1098.semigroup basis :=
  normalizer83.basisFor markerModels right83Models subdirect1098
theorem representative_basis1099 : BasisFor table1099.semigroup basis :=
  normalizer84.basisFor markerModels right84Models subdirect1099
theorem opposite_basis1040 : BasisFor table1040.semigroup.opposite (reversedBasis basis) :=
  representative_basis1040.oppositeReversed
theorem opposite_basis1042 : BasisFor table1042.semigroup.opposite (reversedBasis basis) :=
  representative_basis1042.oppositeReversed
theorem opposite_basis1098 : BasisFor table1098.semigroup.opposite (reversedBasis basis) :=
  representative_basis1098.oppositeReversed
theorem opposite_basis1099 : BasisFor table1099.semigroup.opposite (reversedBasis basis) :=
  representative_basis1099.oppositeReversed

theorem complete1040 (identity : Identity Nat) (valid : identity.SatisfiedBy table1040.semigroup) :
    Derives basis identity.lhs identity.rhs := representative_basis1040.2 identity valid
theorem complete1042 (identity : Identity Nat) (valid : identity.SatisfiedBy table1042.semigroup) :
    Derives basis identity.lhs identity.rhs := representative_basis1042.2 identity valid
theorem complete1098 (identity : Identity Nat) (valid : identity.SatisfiedBy table1098.semigroup) :
    Derives basis identity.lhs identity.rhs := representative_basis1098.2 identity valid
theorem complete1099 (identity : Identity Nat) (valid : identity.SatisfiedBy table1099.semigroup) :
    Derives basis identity.lhs identity.rhs := representative_basis1099.2 identity valid
theorem opposite_complete1040 (identity : Identity Nat) (valid : identity.SatisfiedBy table1040.semigroup.opposite) :
    Derives (reversedBasis basis) identity.lhs identity.rhs := opposite_basis1040.2 identity valid
theorem opposite_complete1042 (identity : Identity Nat) (valid : identity.SatisfiedBy table1042.semigroup.opposite) :
    Derives (reversedBasis basis) identity.lhs identity.rhs := opposite_basis1042.2 identity valid
theorem opposite_complete1098 (identity : Identity Nat) (valid : identity.SatisfiedBy table1098.semigroup.opposite) :
    Derives (reversedBasis basis) identity.lhs identity.rhs := opposite_basis1098.2 identity valid
theorem opposite_complete1099 (identity : Identity Nat) (valid : identity.SatisfiedBy table1099.semigroup.opposite) :
    Derives (reversedBasis basis) identity.lhs identity.rhs := opposite_basis1099.2 identity valid

end Group1040

namespace Single2979

theorem complete (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy markerTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) : Derives basis identity.lhs identity.rhs :=
  rules.complete rightTable.semigroup rightModels S5_240.basis_complete
    rightLeftReductive identity markerValid rightValid

def intersection : IntersectionBasis markerTable.semigroup rightTable.semigroup basis where
  leftModels := markerModels
  rightModels := rightModels
  complete := complete

noncomputable def quotientNormalizer : IntersectionNormalizer markerTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer intersection

noncomputable def normalizer : IntersectionNormalizer markerTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer quotientNormalizer
    (fun _ member => Derives.fromBasis member) (fun _ valid => valid) (fun _ valid => valid)

noncomputable def oppositeNormalizer :
    IntersectionNormalizer markerTable.semigroup.opposite rightTable.semigroup.opposite (reversedBasis basis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer intersection.oppositeReversed

theorem representative_basis : BasisFor table2979.semigroup basis :=
  normalizer.basisFor markerModels rightModels subdirect2979
theorem opposite_basis : BasisFor table2979.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed
theorem representative_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table2979.semigroup) :
    Derives basis identity.lhs identity.rhs := representative_basis.2 identity valid
theorem opposite_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table2979.semigroup.opposite) :
    Derives (reversedBasis basis) identity.lhs identity.rhs := opposite_basis.2 identity valid

end Single2979
end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Initial

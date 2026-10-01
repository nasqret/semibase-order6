import SemigroupBasis.CoRoots.Order6S5_107InitialIntersection
import SemigroupBasis.CoRoots.S5_107Basis
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.S3_15
import SemigroupBasis.Subdirect

namespace SemigroupBasis.CoRoots.Order6S5_107InitialIntersectionFamilies

open SemigroupBasis

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6S5_107InitialIntersection.basis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem modelsOfFiniteChecks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinThree).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp basisRoundTripChecked) identity member
  rw [restored] at finiteValid
  exact finiteValid

theorem modelsS2_4 :
    Models SemigroupBasis.Generated.S2_4.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S2_4.table (by decide)

theorem modelsS3_15 :
    Models SemigroupBasis.Generated.S3_15.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S3_15.table (by decide)

set_option maxHeartbeats 1000000 in
theorem modelsS5_107 :
    Models SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup basis :=
  modelsOfFiniteChecks
    SemigroupBasis.Generated.Catalogue.S5_107.table (by decide)

set_option maxHeartbeats 1000000 in
theorem modelsS5_108 :
    Models SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup basis :=
  modelsOfFiniteChecks
    SemigroupBasis.Generated.Catalogue.S5_108.table (by decide)

set_option maxHeartbeats 1000000 in
theorem modelsS5_109 :
    Models SemigroupBasis.Generated.Catalogue.S5_109.table.semigroup basis :=
  modelsOfFiniteChecks
    SemigroupBasis.Generated.Catalogue.S5_109.table (by decide)

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

private theorem s5_107_s5_108_sameTheory :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.CoRoots.S5_107Family.S5_107.basisFor
    SemigroupBasis.CoRoots.S5_107Family.S5_108.basisFor

private theorem s5_107_s5_109_sameTheory :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_109.table.semigroup Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.CoRoots.S5_107Family.S5_107.basisFor
    SemigroupBasis.CoRoots.S5_107Family.S5_109.basisFor

def leftZeroIntoLeftNormalBand (value : Fin 2) : Fin 3 :=
  if value = 0 then 1 else 2

/-- The two nonzero elements of `S3_15` form a copy of `S2_4`. -/
def leftZeroEmbedding :
    Embedding SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.S3_15.table.semigroup where
  toFun := leftZeroIntoLeftNormalBand
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    revert left right
    decide

def intersectionS2_4S5_107 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup basis where
  leftModels := modelsS2_4
  rightModels := modelsS5_107
  complete :=
    SemigroupBasis.CoRoots.Order6S5_107InitialIntersection.intersection_complete_aristotle

def intersectionS2_4S5_108 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup basis where
  leftModels := modelsS2_4
  rightModels := modelsS5_108
  complete := by
    intro identity initialValid s5Valid
    exact
      SemigroupBasis.CoRoots.Order6S5_107InitialIntersection.intersection_complete_aristotle
        identity initialValid ((s5_107_s5_108_sameTheory identity).mpr s5Valid)

def intersectionS2_4S5_109 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_109.table.semigroup basis where
  leftModels := modelsS2_4
  rightModels := modelsS5_109
  complete := by
    intro identity initialValid s5Valid
    exact
      SemigroupBasis.CoRoots.Order6S5_107InitialIntersection.intersection_complete_aristotle
        identity initialValid ((s5_107_s5_109_sameTheory identity).mpr s5Valid)

def intersectionS3_15S5_107 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup basis where
  leftModels := modelsS3_15
  rightModels := modelsS5_107
  complete := by
    intro identity initialValid s5Valid
    exact
      SemigroupBasis.CoRoots.Order6S5_107InitialIntersection.intersection_complete_aristotle
        identity (leftZeroEmbedding.pullback_identity identity initialValid) s5Valid

def intersectionS3_15S5_108 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup basis where
  leftModels := modelsS3_15
  rightModels := modelsS5_108
  complete := by
    intro identity initialValid s5Valid
    exact
      SemigroupBasis.CoRoots.Order6S5_107InitialIntersection.intersection_complete_aristotle
        identity (leftZeroEmbedding.pullback_identity identity initialValid)
        ((s5_107_s5_108_sameTheory identity).mpr s5Valid)

def intersectionS3_15S5_109 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_109.table.semigroup basis where
  leftModels := modelsS3_15
  rightModels := modelsS5_109
  complete := by
    intro identity initialValid s5Valid
    exact
      SemigroupBasis.CoRoots.Order6S5_107InitialIntersection.intersection_complete_aristotle
        identity (leftZeroEmbedding.pullback_identity identity initialValid)
        ((s5_107_s5_109_sameTheory identity).mpr s5Valid)

end SemigroupBasis.CoRoots.Order6S5_107InitialIntersectionFamilies

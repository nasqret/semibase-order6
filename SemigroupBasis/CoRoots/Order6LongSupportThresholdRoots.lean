import SemigroupBasis.CoRoots.Order6LongSupportThresholdCompleteness
import SemigroupBasis.CoRoots.S5_55Family
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S2_3
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LongSupportThresholdRoots

open SemigroupBasis
open SemigroupBasis.Examples

abbrev basis : List (Identity Nat) :=
  Order6LongSupportThreshold.longSupportThresholdBasis

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private theorem supportFactorModels :
    Models SemigroupBasis.Generated.S2_3.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S2_3.table basis toFinFour (by decide)

set_option maxHeartbeats 1000000 in
private theorem s5_55Models :
    Models SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_55.table basis toFinFour (by decide)

set_option maxHeartbeats 1000000 in
private theorem s5_192Models :
    Models SemigroupBasis.Generated.Catalogue.S5_192.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_192.table basis toFinFour (by decide)

private def s5_55OppositeTable : FiniteTable where
  order := SemigroupBasis.Generated.Catalogue.S5_55.table.order
  mul := fun left right =>
    SemigroupBasis.Generated.Catalogue.S5_55.table.mul right left
  assoc := fun left middle right =>
    (SemigroupBasis.Generated.Catalogue.S5_55.table.assoc
      right middle left).symm

private theorem s5_55OppositeTable_semigroup :
    s5_55OppositeTable.semigroup =
      SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup.opposite :=
  rfl

set_option maxHeartbeats 1000000 in
private theorem s5_55OppositeModels :
    Models
      SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup.opposite
      basis := by
  have checked :=
    FiniteCertificate.checkModels_sound
      s5_55OppositeTable basis toFinFour (by decide)
  rw [s5_55OppositeTable_semigroup] at checked
  exact checked

private theorem sameSupportOfSupportFactorValid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_3.table.semigroup) :
    S5_55.SameSupport identity.lhs identity.rhs := by
  rw [SemigroupBasis.Generated.S2_3.table_eq_catalogue_model] at valid
  exact semilatticeValid_support_eq identity valid

private theorem exactBasisClass_of_reverse
    {left right : Word Nat}
    (sameClass :
      S5_55.ExactBasisClass left.reverse right.reverse) :
    S5_55.ExactBasisClass left right := by
  rcases sameClass with equal | tripleOrLong
  · exact Or.inl <| by
      have reversedEqual := congrArg Word.reverse equal
      simpa using reversedEqual
  · rcases tripleOrLong with triple | long
    · rcases triple with ⟨leftThree, rightThree, support⟩
      exact Or.inr <| Or.inl ⟨
        by
          simpa only [Word.toList_reverse, List.length_reverse] using
            leftThree,
        by
          simpa only [Word.toList_reverse, List.length_reverse] using
            rightThree,
        by
          intro letter
          simpa only [Word.toList_reverse, List.mem_reverse] using
            support letter⟩
    · rcases long with ⟨leftLong, rightLong⟩
      exact Or.inr <| Or.inr ⟨
        by
          simpa only [Word.toList_reverse, List.length_reverse] using
            leftLong,
        by
          simpa only [Word.toList_reverse, List.length_reverse] using
            rightLong⟩

private theorem s5_55OppositeValid_exactBasisClass
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup.opposite) :
    S5_55.ExactBasisClass identity.lhs identity.rhs := by
  have reversedValid :
      identity.reversed.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup).mp valid
  apply exactBasisClass_of_reverse
  simpa only [Identity.reversed] using
    SemigroupBasis.CoRoots.S5_55Family.S5_55.valid_exactBasisClass
      identity.reversed reversedValid

def intersectionS2_3S5_55 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup basis where
  leftModels := supportFactorModels
  rightModels := s5_55Models
  complete := by
    intro identity supportValid thresholdValid
    exact
      Order6LongSupportThreshold.derivesOfThresholdClassAndSupport
        identity
        (SemigroupBasis.CoRoots.S5_55Family.S5_55.valid_exactBasisClass
          identity thresholdValid)
        (sameSupportOfSupportFactorValid identity supportValid)

def intersectionS2_3S5_192 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_192.table.semigroup basis where
  leftModels := supportFactorModels
  rightModels := s5_192Models
  complete := by
    intro identity supportValid thresholdValid
    exact
      Order6LongSupportThreshold.derivesOfThresholdClassAndSupport
        identity
        (SemigroupBasis.CoRoots.S5_55Family.S5_192.valid_exactBasisClass
          identity thresholdValid)
        (sameSupportOfSupportFactorValid identity supportValid)

def intersectionS2_3S5_55Opposite :
    IntersectionBasis
      SemigroupBasis.Generated.S2_3.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup.opposite
      basis where
  leftModels := supportFactorModels
  rightModels := s5_55OppositeModels
  complete := by
    intro identity supportValid thresholdValid
    exact
      Order6LongSupportThreshold.derivesOfThresholdClassAndSupport
        identity
        (s5_55OppositeValid_exactBasisClass identity thresholdValid)
        (sameSupportOfSupportFactorValid identity supportValid)

namespace S6_2800

/-- Zero-based Smallsemi multiplication table for `S6_2800`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then 0
  else if left = 1 then if right = 4 then 2 else 0
  else if left = 2 then 0
  else if left = 3 then 0
  else if left = 4 then
    if right = 1 then 2
    else if right = 3 then 2
    else if right = 4 then 1
    else 0
  else if right = 5 then 5
  else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 2, 0],
   [0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0],
   [0, 2, 0, 2, 1, 0],
   [0, 0, 0, 0, 0, 5]]

theorem mul_matches_published :
    ((List.finRange 6).map fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
        publishedRows := by
  decide

def supportMap (value : Fin 6) : Fin 2 :=
  if value = 5 then 1 else 0

def supportPreimage (value : Fin 2) : Fin 6 :=
  if value = 0 then 0 else 5

def supportQuotient : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S2_3.table.semigroup where
  toFun := supportMap
  map_mul := by decide
  preimage := supportPreimage
  right_inverse := by
    intro value
    exact by decide +revert

def thresholdMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else if value = 4 then 4
  else 0

def thresholdPreimage (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else 4

def thresholdQuotient : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup where
  toFun := thresholdMap
  map_mul := by decide
  preimage := thresholdPreimage
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S2_3.table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup where
  left := supportQuotient
  right := thresholdQuotient
  jointlyInjective := by
    intro left right
    exact by decide +revert

theorem representative_basis :
    BasisFor table.semigroup basis :=
  intersectionS2_3S5_55.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end S6_2800

namespace S6_5346

/-- Zero-based Smallsemi multiplication table for `S6_5346`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then 0
  else if left = 1 then 0
  else if left = 2 then if right = 4 then 1 else 0
  else if left = 3 then if right = 3 then 1 else 0
  else if left = 4 then
    if right = 2 then 1
    else if right = 3 then 1
    else if right = 4 then 2
    else 0
  else if right = 5 then 5
  else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0],
   [0, 0, 0, 1, 0, 0],
   [0, 0, 1, 1, 2, 0],
   [0, 0, 0, 0, 0, 5]]

theorem mul_matches_published :
    ((List.finRange 6).map fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
        publishedRows := by
  decide

def supportMap (value : Fin 6) : Fin 2 :=
  if value = 5 then 1 else 0

def supportPreimage (value : Fin 2) : Fin 6 :=
  if value = 0 then 0 else 5

def supportQuotient : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S2_3.table.semigroup where
  toFun := supportMap
  map_mul := by decide
  preimage := supportPreimage
  right_inverse := by
    intro value
    exact by decide +revert

def thresholdMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else if value = 4 then 4
  else 0

def thresholdPreimage (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else 4

def thresholdQuotient : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_192.table.semigroup where
  toFun := thresholdMap
  map_mul := by decide
  preimage := thresholdPreimage
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S2_3.table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_192.table.semigroup where
  left := supportQuotient
  right := thresholdQuotient
  jointlyInjective := by
    intro left right
    exact by decide +revert

theorem representative_basis :
    BasisFor table.semigroup basis :=
  intersectionS2_3S5_192.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end S6_5346

namespace S6_5465

/-- Zero-based Smallsemi multiplication table for `S6_5465`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then 0
  else if left = 1 then if right = 3 then 2 else 0
  else if left = 2 then 0
  else if left = 3 then
    if right = 1 then 2
    else if right = 3 then 1
    else 0
  else if left = 4 then
    if right = 4 then 4
    else if right = 5 then 4
    else 0
  else if right = 3 then 2
  else if right = 4 then 4
  else if right = 5 then 4
  else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0],
   [0, 0, 0, 2, 0, 0],
   [0, 0, 0, 0, 0, 0],
   [0, 2, 0, 1, 0, 0],
   [0, 0, 0, 0, 4, 4],
   [0, 0, 0, 2, 4, 4]]

theorem mul_matches_published :
    ((List.finRange 6).map fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
        publishedRows := by
  decide

def supportMap (value : Fin 6) : Fin 2 :=
  if value = 0 then 0
  else if value = 1 then 0
  else if value = 2 then 0
  else if value = 3 then 0
  else 1

def supportPreimage (value : Fin 2) : Fin 6 :=
  if value = 0 then 0 else 4

def supportQuotient : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S2_3.table.semigroup where
  toFun := supportMap
  map_mul := by decide
  preimage := supportPreimage
  right_inverse := by
    intro value
    exact by decide +revert

/-- The threshold quotient lands in the opposite of the stored `S5_55`
table; this orientation is forced by the exact catalogue multiplication. -/
def thresholdMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 4
  else if value = 4 then 0
  else 3

def thresholdPreimage (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 5
  else 3

def thresholdQuotient : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup.opposite where
  toFun := thresholdMap
  map_mul := by decide
  preimage := thresholdPreimage
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S2_3.table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup.opposite where
  left := supportQuotient
  right := thresholdQuotient
  jointlyInjective := by
    intro left right
    exact by decide +revert

theorem representative_basis :
    BasisFor table.semigroup basis :=
  intersectionS2_3S5_55Opposite.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end S6_5465

end SemigroupBasis.CoRoots.Order6LongSupportThresholdRoots

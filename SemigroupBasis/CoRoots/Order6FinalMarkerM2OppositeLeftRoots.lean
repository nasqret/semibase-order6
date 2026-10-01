import SemigroupBasis.CoRoots.Order6FinalMarkerM2OppositeLeft

namespace SemigroupBasis.CoRoots.Order6FinalMarkerM2OppositeLeftRoots

open SemigroupBasis

private def valuesZeroBased {n m : Nat} (map : Fin n -> Fin m) : List Nat :=
  List.ofFn fun value => (map value).val

namespace S6_2764

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FinalMarkerM2OppositeLeft.basis

def oppositeBasis : List (Identity Nat) := reversedBasis basis

def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 1, 5 => 1
  | 2, 5 => 2
  | 3, 5 => 3
  | 4, 2 => 1
  | 4, 3 => 1
  | 4, 4 => 1
  | 4, 5 => 4
  | 5, 1 => 1
  | 5, 2 => 2
  | 5, 3 => 2
  | 5, 4 => 4
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c0162976b6309813561d2e494336c370be1b8f8efb9c8fe746fd37907388728b"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1],
       [1, 1, 1, 1, 1, 2],
       [1, 1, 1, 1, 1, 3],
       [1, 1, 1, 1, 1, 4],
       [1, 1, 2, 2, 2, 5],
       [1, 2, 3, 3, 5, 6]] := by
  decide

def s3Map (value : Fin 6) : Fin 3 :=
  match value.val with
  | 3 => 1
  | 5 => 2
  | _ => 0

def s3Section (value : Fin 3) : Fin 6 :=
  match value.val with
  | 1 => 3
  | 2 => 5
  | _ => 0

def ontoS3 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite where
  toFun := s3Map
  map_mul := by decide
  preimage := s3Section
  right_inverse := by decide

def s5Map (value : Fin 6) : Fin 5 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | _ => 0

def s5Section (value : Fin 5) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 5
  | _ => 0

def ontoS5 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup where
  toFun := s5Map
  map_mul := by decide
  preimage := s5Section
  right_inverse := by decide

theorem factorMaps_certificate :
    valuesZeroBased s3Map = [0, 0, 0, 1, 0, 2] /\
    valuesZeroBased s3Section = [0, 3, 5] /\
    valuesZeroBased s5Map = [0, 1, 2, 2, 3, 4] /\
    valuesZeroBased s5Section = [0, 1, 2, 4, 5] := by
  decide

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.IntersectionBasis.basisFor
    SemigroupBasis.CoRoots.Order6FinalMarkerM2OppositeLeft.s3_6OppositeS5_213IntersectionBasis
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end S6_2764

namespace S6_5248

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FinalMarkerM2OppositeLeft.basis

def oppositeBasis : List (Identity Nat) := reversedBasis basis

def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 1, 5 => 1
  | 2, 5 => 2
  | 3, 2 => 1
  | 3, 3 => 1
  | 3, 4 => 1
  | 3, 5 => 3
  | 4, 2 => 1
  | 4, 3 => 1
  | 4, 4 => 1
  | 4, 5 => 4
  | 5, 1 => 1
  | 5, 2 => 2
  | 5, 3 => 3
  | 5, 4 => 3
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b5c388f4a8d56fe323888da0039c2e96d2e1d26e2469f41384feecb6d2ec44bd"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1],
       [1, 1, 1, 1, 1, 2],
       [1, 1, 1, 1, 1, 3],
       [1, 1, 2, 2, 2, 4],
       [1, 1, 2, 2, 2, 5],
       [1, 2, 3, 4, 4, 6]] := by
  decide

def s3Map (value : Fin 6) : Fin 3 :=
  match value.val with
  | 4 => 1
  | 5 => 2
  | _ => 0

def s3Section (value : Fin 3) : Fin 6 :=
  match value.val with
  | 1 => 4
  | 2 => 5
  | _ => 0

def ontoS3 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite where
  toFun := s3Map
  map_mul := by decide
  preimage := s3Section
  right_inverse := by decide

def s5Map (value : Fin 6) : Fin 5 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 4
  | _ => 0

def s5Section (value : Fin 5) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | _ => 0

def ontoS5 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup where
  toFun := s5Map
  map_mul := by decide
  preimage := s5Section
  right_inverse := by decide

theorem factorMaps_certificate :
    valuesZeroBased s3Map = [0, 0, 0, 0, 1, 2] /\
    valuesZeroBased s3Section = [0, 4, 5] /\
    valuesZeroBased s5Map = [0, 1, 2, 3, 3, 4] /\
    valuesZeroBased s5Section = [0, 1, 2, 3, 5] := by
  decide

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.IntersectionBasis.basisFor
    SemigroupBasis.CoRoots.Order6FinalMarkerM2OppositeLeft.s3_6OppositeS5_213IntersectionBasis
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end S6_5248

namespace S6_9307

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FinalMarkerM2OppositeLeft.basis

def oppositeBasis : List (Identity Nat) := reversedBasis basis

def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 1, 5 => 1
  | 2, 2 => 1
  | 2, 5 => 2
  | 3, 2 => 1
  | 3, 3 => 1
  | 3, 4 => 1
  | 3, 5 => 3
  | 4, 2 => 1
  | 4, 3 => 1
  | 4, 4 => 1
  | 4, 5 => 4
  | 5, 1 => 1
  | 5, 2 => 2
  | 5, 3 => 3
  | 5, 4 => 3
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e1190ef4a6a409b0e2923e3145c3139a40255b43741c1c79a37ac9fe600b20c5"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1],
       [1, 1, 1, 1, 1, 2],
       [1, 1, 2, 1, 1, 3],
       [1, 1, 2, 2, 2, 4],
       [1, 1, 2, 2, 2, 5],
       [1, 2, 3, 4, 4, 6]] := by
  decide

def s3Map (value : Fin 6) : Fin 3 :=
  match value.val with
  | 4 => 1
  | 5 => 2
  | _ => 0

def s3Section (value : Fin 3) : Fin 6 :=
  match value.val with
  | 1 => 4
  | 2 => 5
  | _ => 0

def ontoS3 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite where
  toFun := s3Map
  map_mul := by decide
  preimage := s3Section
  right_inverse := by decide

def s5Map (value : Fin 6) : Fin 5 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 4
  | _ => 0

def s5Section (value : Fin 5) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | _ => 0

def ontoS5 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_498.table.semigroup where
  toFun := s5Map
  map_mul := by decide
  preimage := s5Section
  right_inverse := by decide

theorem factorMaps_certificate :
    valuesZeroBased s3Map = [0, 0, 0, 0, 1, 2] /\
    valuesZeroBased s3Section = [0, 4, 5] /\
    valuesZeroBased s5Map = [0, 1, 2, 3, 3, 4] /\
    valuesZeroBased s5Section = [0, 1, 2, 3, 5] := by
  decide

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_498.table.semigroup where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.IntersectionBasis.basisFor
    SemigroupBasis.CoRoots.Order6FinalMarkerM2OppositeLeft.s3_6OppositeS5_498IntersectionBasis
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end S6_9307

end SemigroupBasis.CoRoots.Order6FinalMarkerM2OppositeLeftRoots

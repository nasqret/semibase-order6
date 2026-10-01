import SemigroupBasis.CoRoots.Order6ParityLengthThreshold

/-!
# Exact parity/length-threshold endpoints

The three catalogue representatives below are subdirect products of the
cyclic group `S2_2` and one of the threshold semigroups `S5_55` or `S5_192`.
They therefore share the eight-law basis proved complete in
`Order6ParityLengthThreshold`.
-/

namespace SemigroupBasis.Order6

open SemigroupBasis

private def valuesZeroBased {n m : Nat} (map : Fin n -> Fin m) : List Nat :=
  List.ofFn fun value => (map value).val

namespace S6_910

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6ParityLengthThreshold.basis

def oppositeBasis : List (Identity Nat) := reversedBasis basis

def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 4 => 4
  | 1, 4 => 4
  | 1, 5 => 2
  | 2, 4 => 4
  | 3, 4 => 4
  | 4, 0 => 4
  | 4, 1 => 4
  | 4, 2 => 4
  | 4, 3 => 4
  | 4, 5 => 4
  | 5, 1 => 2
  | 5, 3 => 2
  | 5, 4 => 4
  | 5, 5 => 1
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cf80014e53ae2d0a327e664226ca40cf88cb1ab576630fd85ea2440de545bf03"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem mul_matches_published :
    tableRowsOneBased =
      [[1, 1, 1, 1, 5, 1],
       [1, 1, 1, 1, 5, 3],
       [1, 1, 1, 1, 5, 1],
       [1, 1, 1, 1, 5, 1],
       [5, 5, 5, 5, 1, 5],
       [1, 3, 1, 3, 5, 2]] := by
  decide

def parityMap (value : Fin 6) : Fin 2 :=
  match value.val with
  | 4 => 1
  | _ => 0

def paritySection (value : Fin 2) : Fin 6 :=
  match value.val with
  | 1 => 4
  | _ => 0

def ontoParity :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S2_2.table.semigroup where
  toFun := parityMap
  map_mul := by decide
  preimage := paritySection
  right_inverse := by decide

def thresholdMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 5 => 4
  | _ => 0

def thresholdSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | _ => 0

def ontoThreshold :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup where
  toFun := thresholdMap
  map_mul := by decide
  preimage := thresholdSection
  right_inverse := by decide

theorem factor_binding_certificate :
    valuesZeroBased parityMap = [0, 0, 0, 0, 1, 0] /\
    valuesZeroBased paritySection = [0, 4] /\
    valuesZeroBased thresholdMap = [0, 1, 2, 3, 0, 4] /\
    valuesZeroBased thresholdSection = [0, 1, 2, 3, 5] := by
  decide

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup where
  left := ontoParity
  right := ontoThreshold
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6ParityLengthThreshold.s2_2_s5_55_intersectionBasis.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end S6_910

namespace S6_928

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6ParityLengthThreshold.basis

def oppositeBasis : List (Identity Nat) := reversedBasis basis

def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 3 => 3
  | 0, 4 => 3
  | 0, 5 => 3
  | 1, 3 => 3
  | 1, 4 => 3
  | 1, 5 => 4
  | 2, 3 => 3
  | 2, 4 => 3
  | 2, 5 => 3
  | 3, 0 => 3
  | 3, 1 => 3
  | 3, 2 => 3
  | 4, 0 => 3
  | 4, 1 => 3
  | 4, 2 => 3
  | 5, 0 => 3
  | 5, 1 => 4
  | 5, 2 => 4
  | 5, 5 => 1
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c8645a70d306ac3e53bb6fe8ce38b617c38a7fc53306a5a859b33154dc8f60f3"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem mul_matches_published :
    tableRowsOneBased =
      [[1, 1, 1, 4, 4, 4],
       [1, 1, 1, 4, 4, 5],
       [1, 1, 1, 4, 4, 4],
       [4, 4, 4, 1, 1, 1],
       [4, 4, 4, 1, 1, 1],
       [4, 5, 5, 1, 1, 2]] := by
  decide

def parityMap (value : Fin 6) : Fin 2 :=
  match value.val with
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | _ => 0

def paritySection (value : Fin 2) : Fin 6 :=
  match value.val with
  | 1 => 3
  | _ => 0

def ontoParity :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S2_2.table.semigroup where
  toFun := parityMap
  map_mul := by decide
  preimage := paritySection
  right_inverse := by decide

def thresholdMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 1 => 1
  | 2 => 3
  | 4 => 2
  | 5 => 4
  | _ => 0

def thresholdSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 4
  | 3 => 2
  | 4 => 5
  | _ => 0

def ontoThreshold :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup where
  toFun := thresholdMap
  map_mul := by decide
  preimage := thresholdSection
  right_inverse := by decide

theorem factor_binding_certificate :
    valuesZeroBased parityMap = [0, 0, 0, 1, 1, 1] /\
    valuesZeroBased paritySection = [0, 3] /\
    valuesZeroBased thresholdMap = [0, 1, 3, 0, 2, 4] /\
    valuesZeroBased thresholdSection = [0, 1, 4, 2, 5] := by
  decide

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup where
  left := ontoParity
  right := ontoThreshold
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6ParityLengthThreshold.s2_2_s5_55_intersectionBasis.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end S6_928

namespace S6_2570

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6ParityLengthThreshold.basis

def oppositeBasis : List (Identity Nat) := reversedBasis basis

def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 3 => 3
  | 1, 3 => 3
  | 2, 3 => 3
  | 2, 5 => 1
  | 3, 0 => 3
  | 3, 1 => 3
  | 3, 2 => 3
  | 3, 4 => 3
  | 3, 5 => 3
  | 4, 3 => 3
  | 4, 4 => 1
  | 5, 2 => 1
  | 5, 3 => 3
  | 5, 4 => 1
  | 5, 5 => 2
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e460c1f3af1d80ce0103b2f86eb27fd9e3fbcf898f2c96722ba8c8d3e2416a41"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem mul_matches_published :
    tableRowsOneBased =
      [[1, 1, 1, 4, 1, 1],
       [1, 1, 1, 4, 1, 1],
       [1, 1, 1, 4, 1, 2],
       [4, 4, 4, 1, 4, 4],
       [1, 1, 1, 4, 2, 1],
       [1, 1, 2, 4, 2, 3]] := by
  decide

def parityMap (value : Fin 6) : Fin 2 :=
  match value.val with
  | 3 => 1
  | _ => 0

def paritySection (value : Fin 2) : Fin 6 :=
  match value.val with
  | 1 => 3
  | _ => 0

def ontoParity :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S2_2.table.semigroup where
  toFun := parityMap
  map_mul := by decide
  preimage := paritySection
  right_inverse := by decide

def thresholdMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 4 => 3
  | 5 => 4
  | _ => 0

def thresholdSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 5
  | _ => 0

def ontoThreshold :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_192.table.semigroup where
  toFun := thresholdMap
  map_mul := by decide
  preimage := thresholdSection
  right_inverse := by decide

theorem factor_binding_certificate :
    valuesZeroBased parityMap = [0, 0, 0, 1, 0, 0] /\
    valuesZeroBased paritySection = [0, 3] /\
    valuesZeroBased thresholdMap = [0, 1, 2, 0, 3, 4] /\
    valuesZeroBased thresholdSection = [0, 1, 2, 4, 5] := by
  decide

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_192.table.semigroup where
  left := ontoParity
  right := ontoThreshold
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6ParityLengthThreshold.s2_2_s5_192_intersectionBasis.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end S6_2570

end SemigroupBasis.Order6

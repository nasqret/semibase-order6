import SemigroupBasis.CoRoots.Order6FactorPairS4_116opS5_841

namespace SemigroupBasis.Generated.Order6FactorPairS4_116opS5_841.S6_13421

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6FactorPairS4_116opS5_841

/-- Exact zero-based multiplication for the Smallsemi representative
`S6_13421`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 1, 4 => 1
  | 1, 5 => 1
  | 2, 1 => 1
  | 2, 2 => 2
  | 2, 3 => 3
  | 2, 4 => 1
  | 2, 5 => 2
  | 3, 1 => 1
  | 3, 2 => 2
  | 3, 3 => 3
  | 3, 4 => 1
  | 3, 5 => 3
  | 4, 4 => 4
  | 4, 5 => 4
  | 5, _ => right
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableRowsZeroBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val

theorem tableRowsZeroBased_certificate :
    tableRowsZeroBased =
      [[0, 0, 0, 0, 0, 0],
       [0, 0, 0, 0, 1, 1],
       [0, 1, 2, 3, 1, 2],
       [0, 1, 2, 3, 1, 3],
       [0, 0, 0, 0, 4, 4],
       [0, 1, 2, 3, 4, 5]] := by
  decide

def tableSHA256 : String :=
  "ccf97f54028d13a956a2e708980c8ebb12f6142f6e85e4c147d1f6c582749aad"

def componentSHA256 : String :=
  "542d99e34e2ee1a804b0827a2b35ac3a4f4ae8623c0f5b6bb79e158b166e6eac"

def leftFactorID : String := "S4_116"
def leftFactorOrientation : String := "opposite"
def rightFactorID : String := "S5_841"
def rightFactorOrientation : String := "direct"
def basisOrientation : String := "direct"
def memberCount : Nat := 1

/-- Quotient blocks `[1,2,5]`, `[3]`, `[6]`, `[4]`, reordered to
the opposite `S4_116` catalogue representative. -/
def s4Map (value : Fin 6) : Fin 4 :=
  if value = 2 then 1
  else if value = 3 then 3
  else if value = 5 then 2
  else 0

def s4Section (value : Fin 4) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 2
  else if value = 2 then 5
  else 3

def s4MapValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 6 => (s4Map value).val

def s4SectionValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 4 => (s4Section value).val

theorem s4ValuesZeroBased_certificate :
    s4MapValuesZeroBased = [0, 0, 1, 3, 0, 2] ∧
      s4SectionValuesZeroBased = [0, 2, 5, 3] := by
  decide

def ontoS4 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup.opposite where
  toFun := s4Map
  map_mul := by decide
  preimage := s4Section
  right_inverse := by decide

/-- Quotient blocks `[1]`, `[2]`, `[3,4]`, `[5]`, `[6]`. -/
def s5Map (value : Fin 6) : Fin 5 :=
  if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 2
  else if value = 4 then 3
  else if value = 5 then 4
  else 0

def s5Section (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 4
  else 5

def s5MapValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 6 => (s5Map value).val

def s5SectionValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 5 => (s5Section value).val

theorem s5ValuesZeroBased_certificate :
    s5MapValuesZeroBased = [0, 1, 2, 2, 3, 4] ∧
      s5SectionValuesZeroBased = [0, 1, 2, 4, 5] := by
  decide

def ontoS5 : SplitSurjection table.semigroup
    SemigroupBasis.CoRoots.S5_841.table.semigroup where
  toFun := s5Map
  map_mul := by decide
  preimage := s5Section
  right_inverse := by decide

def coordinateSignaturesZeroBased : List (Nat × Nat) :=
  List.ofFn fun value : Fin 6 =>
    ((s4Map value).val, (s5Map value).val)

theorem coordinateSignaturesZeroBased_certificate :
    coordinateSignaturesZeroBased =
      [(0, 0), (0, 1), (1, 2), (3, 2), (0, 3), (2, 4)] := by
  decide

/-- The two quotient kernels have diagonal intersection. -/
def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup.opposite
    SemigroupBasis.CoRoots.S5_841.table.semigroup where
  left := ontoS4
  right := ontoS5
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor subdirectPair

theorem opposite_reversed_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FactorPairS4_116opS5_841.S6_13421

import SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorPairS2S583.S6_1237

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal

/-- Exact zero-based multiplication for the Smallsemi representative
`S6_1237`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 4 => 4
  | 1, 4 => 4
  | 2, 4 => 4
  | 3, 2 => 1
  | 3, 4 => 4
  | 4, 0 => 4
  | 4, 1 => 4
  | 4, 2 => 4
  | 4, 3 => 4
  | 4, 5 => 4
  | 5, 1 => 1
  | 5, 3 => 3
  | 5, 4 => 4
  | 5, 5 => 5
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
      [[0, 0, 0, 0, 4, 0],
       [0, 0, 0, 0, 4, 0],
       [0, 0, 0, 0, 4, 0],
       [0, 0, 1, 0, 4, 0],
       [4, 4, 4, 4, 0, 4],
       [0, 1, 0, 3, 4, 5]] := by
  decide

def tableSHA256 : String :=
  "7199d5a21e65070e4635736c92189b67d6c295cabbbdf7d5ca281164fec3a6de"

def factorPairFamilyID : String := "o6fp-f86c0cf5f9df6673"
def proofRoute : String := "s2-2-s5-83-factor-pair-join-normal-form"
def casPacketSHA256 : String :=
  "cb5752b4bf7b1dd78d75f72cf81b10a89a6c7200c392d6aa974f25937d5182fe"
def casValidationSHA256 : String :=
  "893d75c85aa0f725e007484780ee55f95144c481ff42494c1dc5d40a2952bb58"

/-- Quotient blocks `[1,2,3,4,6]`, `[5]`, identified directly with
`S2_2`. -/
def s2Map (value : Fin 6) : Fin 2 :=
  if value = 4 then 1 else 0

def s2Section (value : Fin 2) : Fin 6 :=
  if value = 0 then 0 else 4

def s2MapValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 6 => (s2Map value).val

def s2SectionValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 2 => (s2Section value).val

theorem s2ValuesZeroBased_certificate :
    s2MapValuesZeroBased = [0, 0, 0, 0, 1, 0] ∧
      s2SectionValuesZeroBased = [0, 4] := by
  decide

def ontoS2 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S2_2.table.semigroup where
  toFun := s2Map
  map_mul := by decide
  preimage := s2Section
  right_inverse := by decide

/-- Quotient blocks `[1,5]`, `[2]`, `[3]`, `[4]`, `[6]`, identified
directly with `S5_83`. -/
def s5Map (value : Fin 6) : Fin 5 :=
  if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else if value = 5 then 4
  else 0

def s5Section (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else 5

def s5MapValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 6 => (s5Map value).val

def s5SectionValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 5 => (s5Section value).val

theorem s5ValuesZeroBased_certificate :
    s5MapValuesZeroBased = [0, 1, 2, 3, 0, 4] ∧
      s5SectionValuesZeroBased = [0, 1, 2, 3, 5] := by
  decide

def ontoS5 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup where
  toFun := s5Map
  map_mul := by decide
  preimage := s5Section
  right_inverse := by decide

def coordinateSignaturesZeroBased : List (Nat × Nat) :=
  List.ofFn fun value : Fin 6 =>
    ((s2Map value).val, (s5Map value).val)

theorem coordinateSignaturesZeroBased_certificate :
    coordinateSignaturesZeroBased =
      [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (0, 4)] := by
  decide

/-- The two recorded quotient kernels separate all 15 unordered pairs;
their diagonal map has image size six. -/
def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S2_2.table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup where
  left := ontoS2
  right := ontoS5
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal.basis

/-- Unconditional order-six endpoint for the direct representative
`S6_1237`. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor subdirectPair

theorem opposite_reversed_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FactorPairS2S583.S6_1237

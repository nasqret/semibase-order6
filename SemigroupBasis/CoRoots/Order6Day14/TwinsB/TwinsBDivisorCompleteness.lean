import SemigroupBasis.CoRoots.Order6Day14.TwinsA.TwinsACompleteness
import SemigroupBasis.CoRoots.Order6Sunday.TwinsBExactTransfers

/-! The opposite completed A anchor is a divisor of a cube of the B anchor.
The ten elements retain a group coordinate, a three-state level coordinate,
and a final coordinate fixed at 4 on the top level. No bounded search is
a premise: all new finite maps are proved against the imported literal tables. -/

namespace SemigroupBasis.CoRoots.Order6Day14.TwinsB

open SemigroupBasis

abbrev basis := Order6Sunday.TwinTwoLawFinite.B.basis
abbrev anchor : FiniteTable := Order6Sunday.LateFinite.Sigma086fa.S6_11897.table
abbrev oppositeA := Order6Sunday.LateFinite.SigmaF137a.S6_14814.table.semigroup.opposite

def divisorMul (a b : Fin 10) : Fin 10 :=
  match a.val, b.val with
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 2
  | 0, 3 => 3
  | 0, 4 => 4
  | 0, 5 => 5
  | 0, 6 => 6
  | 0, 7 => 7
  | 0, 8 => 8
  | 0, 9 => 9
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => 6
  | 1, 3 => 7
  | 1, 4 => 8
  | 1, 5 => 9
  | 1, 6 => 2
  | 1, 7 => 3
  | 1, 8 => 4
  | 1, 9 => 5
  | 2, 0 => 2
  | 2, 1 => 6
  | 2, 2 => 2
  | 2, 3 => 3
  | 2, 4 => 2
  | 2, 5 => 3
  | 2, 6 => 6
  | 2, 7 => 7
  | 2, 8 => 6
  | 2, 9 => 7
  | 3, 0 => 2
  | 3, 1 => 6
  | 3, 2 => 2
  | 3, 3 => 3
  | 3, 4 => 2
  | 3, 5 => 3
  | 3, 6 => 6
  | 3, 7 => 7
  | 3, 8 => 6
  | 3, 9 => 7
  | 4, 0 => 4
  | 4, 1 => 8
  | 4, 2 => 4
  | 4, 3 => 5
  | 4, 4 => 4
  | 4, 5 => 5
  | 4, 6 => 8
  | 4, 7 => 9
  | 4, 8 => 8
  | 4, 9 => 9
  | 5, 0 => 4
  | 5, 1 => 8
  | 5, 2 => 4
  | 5, 3 => 5
  | 5, 4 => 4
  | 5, 5 => 5
  | 5, 6 => 8
  | 5, 7 => 9
  | 5, 8 => 8
  | 5, 9 => 9
  | 6, 0 => 6
  | 6, 1 => 2
  | 6, 2 => 6
  | 6, 3 => 7
  | 6, 4 => 6
  | 6, 5 => 7
  | 6, 6 => 2
  | 6, 7 => 3
  | 6, 8 => 2
  | 6, 9 => 3
  | 7, 0 => 6
  | 7, 1 => 2
  | 7, 2 => 6
  | 7, 3 => 7
  | 7, 4 => 6
  | 7, 5 => 7
  | 7, 6 => 2
  | 7, 7 => 3
  | 7, 8 => 2
  | 7, 9 => 3
  | 8, 0 => 8
  | 8, 1 => 4
  | 8, 2 => 8
  | 8, 3 => 9
  | 8, 4 => 8
  | 8, 5 => 9
  | 8, 6 => 4
  | 8, 7 => 5
  | 8, 8 => 4
  | 8, 9 => 5
  | 9, 0 => 8
  | 9, 1 => 4
  | 9, 2 => 8
  | 9, 3 => 9
  | 9, 4 => 8
  | 9, 5 => 9
  | 9, 6 => 4
  | 9, 7 => 5
  | 9, 8 => 4
  | 9, 9 => 5
  | _, _ => 0

def coordinate (i : Fin 3) (a : Fin 10) : Fin 6 :=
  match i.val, a.val with
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 0, 6 => 1
  | 0, 7 => 1
  | 0, 8 => 1
  | 0, 9 => 1
  | 1, 0 => 4
  | 1, 1 => 4
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 2
  | 1, 5 => 2
  | 1, 6 => 0
  | 1, 7 => 0
  | 1, 8 => 2
  | 1, 9 => 2
  | 2, 0 => 4
  | 2, 1 => 4
  | 2, 2 => 4
  | 2, 3 => 5
  | 2, 4 => 4
  | 2, 5 => 5
  | 2, 6 => 4
  | 2, 7 => 5
  | 2, 8 => 4
  | 2, 9 => 5
  | _, _ => 0

theorem coordinate_mul :
    ∀ (i : Fin 3) (a b : Fin 10),
      coordinate i (divisorMul a b) = anchor.mul (coordinate i a) (coordinate i b) := by
  decide

theorem coordinates_separate :
    ∀ a b : Fin 10, (∀ i : Fin 3, coordinate i a = coordinate i b) → a = b := by
  decide

theorem divisor_assoc (a b c : Fin 10) :
    divisorMul (divisorMul a b) c = divisorMul a (divisorMul b c) := by
  apply coordinates_separate
  intro i
  simp only [coordinate_mul]
  exact anchor.assoc (coordinate i a) (coordinate i b) (coordinate i c)

def divisor : FiniteTable where
  order := 10
  mul := divisorMul
  assoc := divisor_assoc

def coordinateHom (i : Fin 3) : Hom divisor.semigroup anchor.semigroup where
  toFun := coordinate i
  map_mul := coordinate_mul i

def intoCube : Embedding divisor.semigroup (anchor.semigroup.pi (Fin 3)) :=
  Embedding.ofSeparatingHoms coordinateHom coordinates_separate

def quotientMap (a : Fin 10) : Fin 6 :=
  match a.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 2
  | 7 => 3
  | 8 => 4
  | 9 => 5
  | _ => 0

def quotientSection (a : Fin 6) : Fin 10 :=
  match a.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | _ => 0

theorem quotient_mul :
    ∀ a b : Fin 10,
      quotientMap (divisorMul a b) = oppositeA.mul (quotientMap a) (quotientMap b) := by
  decide

theorem quotient_section : ∀ a : Fin 6, quotientMap (quotientSection a) = a := by
  decide

def ontoOppositeA : SplitSurjection divisor.semigroup oppositeA where
  toFun := quotientMap
  map_mul := quotient_mul
  preimage := quotientSection
  right_inverse := quotient_section

namespace S6_11897

theorem complete : BasisFor anchor.semigroup basis := by
  have reversedSource :
      BasisFor oppositeA (reversedBasis Order6Sunday.TwinTwoLawFinite.A.basis) :=
    Order6Day14.TwinsA.S6_14814.opposite_complete
  have sourceBasis : BasisFor oppositeA basis := by
    simpa only [basis, Order6Sunday.TwinTwoLawFinite.basisBIsReversal] using reversedSource
  exact sourceBasis.inheritAlongPowerDivisor intoCube ontoOppositeA
    Order6Sunday.TwinTwoLawFinite.B.S6_11897.models

theorem opposite_complete : BasisFor anchor.semigroup.opposite (reversedBasis basis) :=
  complete.oppositeReversed

end S6_11897

namespace S6_14651

theorem complete :
    BasisFor Order6Sunday.LateFinite.Sigma086fb.S6_14651.table.semigroup basis :=
  S6_11897.complete.inheritAlongPowerEmbedding
    Order6Sunday.TwinsBExactTransfers.powerEmbedding14651
    Order6Sunday.TwinTwoLawFinite.B.S6_14651.models

theorem opposite_complete :
    BasisFor Order6Sunday.LateFinite.Sigma086fb.S6_14651.table.semigroup.opposite
      (reversedBasis basis) :=
  complete.oppositeReversed

end S6_14651

namespace S6_14680

theorem complete :
    BasisFor Order6Sunday.LateFinite.Sigma086fc.S6_14680.table.semigroup basis :=
  S6_11897.complete.inheritAlongPowerEmbedding
    Order6Sunday.TwinsBExactTransfers.powerEmbedding14680
    Order6Sunday.TwinTwoLawFinite.B.S6_14680.models

theorem opposite_complete :
    BasisFor Order6Sunday.LateFinite.Sigma086fc.S6_14680.table.semigroup.opposite
      (reversedBasis basis) :=
  complete.oppositeReversed

end S6_14680

namespace S6_14762

theorem complete :
    BasisFor Order6Sunday.LateFinite.Sigma086fc.S6_14762.table.semigroup basis :=
  S6_11897.complete.inheritAlongPowerEmbedding
    Order6Sunday.TwinsBExactTransfers.powerEmbedding14762
    Order6Sunday.TwinTwoLawFinite.B.S6_14762.models

theorem opposite_complete :
    BasisFor Order6Sunday.LateFinite.Sigma086fc.S6_14762.table.semigroup.opposite
      (reversedBasis basis) :=
  complete.oppositeReversed

end S6_14762

namespace S6_14780

theorem complete :
    BasisFor Order6Sunday.LateFinite.Sigma086fc.S6_14780.table.semigroup basis :=
  S6_11897.complete.inheritAlongPowerEmbedding
    Order6Sunday.TwinsBExactTransfers.powerEmbedding14780
    Order6Sunday.TwinTwoLawFinite.B.S6_14780.models

theorem opposite_complete :
    BasisFor Order6Sunday.LateFinite.Sigma086fc.S6_14780.table.semigroup.opposite
      (reversedBasis basis) :=
  complete.oppositeReversed

end S6_14780

end SemigroupBasis.CoRoots.Order6Day14.TwinsB

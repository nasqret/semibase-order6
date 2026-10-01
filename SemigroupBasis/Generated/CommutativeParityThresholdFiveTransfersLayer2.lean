import SemigroupBasis.Generated.CommutativeParityThresholdFiveTransfersLayer1

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.CommutativeParityThresholdFiveTransfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S5_225
namespace S5_225

def divisorSubMul
    (a b : Fin 8) : Fin 8 :=
  if a = 0 then if b = 0 then (0 : Fin 8) else if b = 1 then (0 : Fin 8) else if b = 2 then (2 : Fin 8) else if b = 3 then (2 : Fin 8) else if b = 4 then (0 : Fin 8) else if b = 5 then (5 : Fin 8) else if b = 6 then (6 : Fin 8) else (5 : Fin 8) else if a = 1 then if b = 0 then (0 : Fin 8) else if b = 1 then (0 : Fin 8) else if b = 2 then (2 : Fin 8) else if b = 3 then (2 : Fin 8) else if b = 4 then (0 : Fin 8) else if b = 5 then (5 : Fin 8) else if b = 6 then (6 : Fin 8) else (5 : Fin 8) else if a = 2 then if b = 0 then (2 : Fin 8) else if b = 1 then (2 : Fin 8) else if b = 2 then (0 : Fin 8) else if b = 3 then (0 : Fin 8) else if b = 4 then (2 : Fin 8) else if b = 5 then (6 : Fin 8) else if b = 6 then (5 : Fin 8) else (6 : Fin 8) else if a = 3 then if b = 0 then (2 : Fin 8) else if b = 1 then (2 : Fin 8) else if b = 2 then (0 : Fin 8) else if b = 3 then (1 : Fin 8) else if b = 4 then (2 : Fin 8) else if b = 5 then (6 : Fin 8) else if b = 6 then (5 : Fin 8) else (6 : Fin 8) else if a = 4 then if b = 0 then (0 : Fin 8) else if b = 1 then (0 : Fin 8) else if b = 2 then (2 : Fin 8) else if b = 3 then (2 : Fin 8) else if b = 4 then (4 : Fin 8) else if b = 5 then (5 : Fin 8) else if b = 6 then (6 : Fin 8) else (7 : Fin 8) else if a = 5 then if b = 0 then (5 : Fin 8) else if b = 1 then (5 : Fin 8) else if b = 2 then (6 : Fin 8) else if b = 3 then (6 : Fin 8) else if b = 4 then (5 : Fin 8) else if b = 5 then (0 : Fin 8) else if b = 6 then (2 : Fin 8) else (0 : Fin 8) else if a = 6 then if b = 0 then (6 : Fin 8) else if b = 1 then (6 : Fin 8) else if b = 2 then (5 : Fin 8) else if b = 3 then (5 : Fin 8) else if b = 4 then (6 : Fin 8) else if b = 5 then (2 : Fin 8) else if b = 6 then (0 : Fin 8) else (2 : Fin 8) else if b = 0 then (5 : Fin 8) else if b = 1 then (5 : Fin 8) else if b = 2 then (6 : Fin 8) else if b = 3 then (6 : Fin 8) else if b = 4 then (7 : Fin 8) else if b = 5 then (0 : Fin 8) else if b = 6 then (2 : Fin 8) else (4 : Fin 8)

def divisorSubTable : FiniteTable where
  order := 8
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_225.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 8) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (0 : Fin 5) else if a = 5 then (2 : Fin 5) else if a = 6 then (2 : Fin 5) else (2 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (4 : Fin 5) else if a = 5 then (0 : Fin 5) else if a = 6 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    funext i
    exact by decide +revert
  injective := by
    intro a b h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    clear h
    exact by decide +revert

def divisorQuotient :
    SplitSurjection divisorSubTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_509.table.semigroup where
  toFun := fun a : Fin 8 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else if a = 5 then (0 : Fin 5) else if a = 6 then (0 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 8) else if b = 1 then (1 : Fin 8) else if b = 2 then (3 : Fin 8) else if b = 3 then (4 : Fin 8) else (7 : Fin 8)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def finiteUnaryPeriodLaw : Identity (Fin 1) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0, 0]⟩⟩

def finiteLeftParityLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [0, 0, 0, 1]⟩⟩

def finiteRightParityLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [0, 1, 1, 1]⟩⟩

def finiteSupportThresholdLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [0, 0, 1, 2]⟩⟩

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_225.table.semigroup
      SemigroupBasis.Examples.commutativeParityThresholdFiveBasis := by
  intro e he
  simp only [
    SemigroupBasis.Examples.commutativeParityThresholdFiveBasis,
    List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · change (finiteCommutativityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_225.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_225.table.checkIdentityNat_sound
      finiteCommutativityLaw (by decide)
  · change (finiteUnaryPeriodLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_225.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_225.table.checkIdentityNat_sound
      finiteUnaryPeriodLaw (by decide)
  · change (finiteLeftParityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_225.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_225.table.checkIdentityNat_sound
      finiteLeftParityLaw (by decide)
  · change (finiteRightParityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_225.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_225.table.checkIdentityNat_sound
      finiteRightParityLaw (by decide)
  · change (finiteSupportThresholdLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_225.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_225.table.checkIdentityNat_sound
      finiteSupportThresholdLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_225.table.semigroup
      SemigroupBasis.Examples.commutativeParityThresholdFiveBasis :=
  SemigroupBasis.Generated.CommutativeParityThresholdFiveTransfers.S5_509.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


end S5_225
-- END S5_225

-- BEGIN S5_227
namespace S5_227

def divisorSubMul
    (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6)

def divisorSubTable : FiniteTable where
  order := 6
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_227.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 6) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (1 : Fin 5) else if a = 4 then (2 : Fin 5) else (3 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (4 : Fin 5) else if a = 3 then (4 : Fin 5) else if a = 4 then (4 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    funext i
    exact by decide +revert
  injective := by
    intro a b h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    clear h
    exact by decide +revert

def divisorQuotient :
    SplitSurjection divisorSubTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_509.table.semigroup where
  toFun := fun a : Fin 6 =>
    if a = 0 then (3 : Fin 5) else if a = 1 then (4 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (1 : Fin 5) else if a = 4 then (0 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (2 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (0 : Fin 6) else (1 : Fin 6)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def finiteUnaryPeriodLaw : Identity (Fin 1) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0, 0]⟩⟩

def finiteLeftParityLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [0, 0, 0, 1]⟩⟩

def finiteRightParityLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [0, 1, 1, 1]⟩⟩

def finiteSupportThresholdLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [0, 0, 1, 2]⟩⟩

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_227.table.semigroup
      SemigroupBasis.Examples.commutativeParityThresholdFiveBasis := by
  intro e he
  simp only [
    SemigroupBasis.Examples.commutativeParityThresholdFiveBasis,
    List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · change (finiteCommutativityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_227.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_227.table.checkIdentityNat_sound
      finiteCommutativityLaw (by decide)
  · change (finiteUnaryPeriodLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_227.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_227.table.checkIdentityNat_sound
      finiteUnaryPeriodLaw (by decide)
  · change (finiteLeftParityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_227.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_227.table.checkIdentityNat_sound
      finiteLeftParityLaw (by decide)
  · change (finiteRightParityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_227.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_227.table.checkIdentityNat_sound
      finiteRightParityLaw (by decide)
  · change (finiteSupportThresholdLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_227.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_227.table.checkIdentityNat_sound
      finiteSupportThresholdLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_227.table.semigroup
      SemigroupBasis.Examples.commutativeParityThresholdFiveBasis :=
  SemigroupBasis.Generated.CommutativeParityThresholdFiveTransfers.S5_509.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


end S5_227
-- END S5_227

end SemigroupBasis.Generated.CommutativeParityThresholdFiveTransfers

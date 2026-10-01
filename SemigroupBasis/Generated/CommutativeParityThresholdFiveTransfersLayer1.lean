import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S5_222
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.CommutativeParityThresholdFiveTransfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S5_224
namespace S5_224

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S5_222.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_224.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else (0 : Fin 5) else if a = 0 then (4 : Fin 5) else if a = 1 then (4 : Fin 5) else if a = 2 then (4 : Fin 5) else if a = 3 then (4 : Fin 5) else (0 : Fin 5)
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
    Models SemigroupBasis.Generated.Catalogue.S5_224.table.semigroup
      SemigroupBasis.Examples.commutativeParityThresholdFiveBasis := by
  intro e he
  simp only [
    SemigroupBasis.Examples.commutativeParityThresholdFiveBasis,
    List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · change (finiteCommutativityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_224.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_224.table.checkIdentityNat_sound
      finiteCommutativityLaw (by decide)
  · change (finiteUnaryPeriodLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_224.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_224.table.checkIdentityNat_sound
      finiteUnaryPeriodLaw (by decide)
  · change (finiteLeftParityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_224.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_224.table.checkIdentityNat_sound
      finiteLeftParityLaw (by decide)
  · change (finiteRightParityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_224.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_224.table.checkIdentityNat_sound
      finiteRightParityLaw (by decide)
  · change (finiteSupportThresholdLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_224.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_224.table.checkIdentityNat_sound
      finiteSupportThresholdLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_224.table.semigroup
      SemigroupBasis.Examples.commutativeParityThresholdFiveBasis :=
  SemigroupBasis.Generated.S5_222.representative_basis.inheritAlongPowerEmbedding
    powerEmbedding targetModels


end S5_224
-- END S5_224

-- BEGIN S5_509
namespace S5_509

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S5_222.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_509.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (2 : Fin 5) else (3 : Fin 5) else if a = 0 then (3 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (4 : Fin 5) else if a = 3 then (3 : Fin 5) else (3 : Fin 5)
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
    Models SemigroupBasis.Generated.Catalogue.S5_509.table.semigroup
      SemigroupBasis.Examples.commutativeParityThresholdFiveBasis := by
  intro e he
  simp only [
    SemigroupBasis.Examples.commutativeParityThresholdFiveBasis,
    List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · change (finiteCommutativityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_509.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_509.table.checkIdentityNat_sound
      finiteCommutativityLaw (by decide)
  · change (finiteUnaryPeriodLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_509.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_509.table.checkIdentityNat_sound
      finiteUnaryPeriodLaw (by decide)
  · change (finiteLeftParityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_509.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_509.table.checkIdentityNat_sound
      finiteLeftParityLaw (by decide)
  · change (finiteRightParityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_509.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_509.table.checkIdentityNat_sound
      finiteRightParityLaw (by decide)
  · change (finiteSupportThresholdLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_509.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_509.table.checkIdentityNat_sound
      finiteSupportThresholdLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_509.table.semigroup
      SemigroupBasis.Examples.commutativeParityThresholdFiveBasis :=
  SemigroupBasis.Generated.S5_222.representative_basis.inheritAlongPowerEmbedding
    powerEmbedding targetModels


end S5_509
-- END S5_509

-- BEGIN S5_518
namespace S5_518

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S5_222.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_518.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (2 : Fin 5) else (0 : Fin 5) else if a = 0 then (3 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (4 : Fin 5) else if a = 3 then (3 : Fin 5) else (0 : Fin 5)
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
    Models SemigroupBasis.Generated.Catalogue.S5_518.table.semigroup
      SemigroupBasis.Examples.commutativeParityThresholdFiveBasis := by
  intro e he
  simp only [
    SemigroupBasis.Examples.commutativeParityThresholdFiveBasis,
    List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · change (finiteCommutativityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_518.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_518.table.checkIdentityNat_sound
      finiteCommutativityLaw (by decide)
  · change (finiteUnaryPeriodLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_518.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_518.table.checkIdentityNat_sound
      finiteUnaryPeriodLaw (by decide)
  · change (finiteLeftParityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_518.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_518.table.checkIdentityNat_sound
      finiteLeftParityLaw (by decide)
  · change (finiteRightParityLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_518.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_518.table.checkIdentityNat_sound
      finiteRightParityLaw (by decide)
  · change (finiteSupportThresholdLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_518.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_518.table.checkIdentityNat_sound
      finiteSupportThresholdLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_518.table.semigroup
      SemigroupBasis.Examples.commutativeParityThresholdFiveBasis :=
  SemigroupBasis.Generated.S5_222.representative_basis.inheritAlongPowerEmbedding
    powerEmbedding targetModels


end S5_518
-- END S5_518

end SemigroupBasis.Generated.CommutativeParityThresholdFiveTransfers

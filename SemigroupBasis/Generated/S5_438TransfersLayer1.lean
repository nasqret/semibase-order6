import SemigroupBasis.CoRoots.S5_438
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part04
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.S5_438Transfers.S5_461

open SemigroupBasis

/-- The seven certificate pairs in `S5_461^2`, in quotient order. -/
def divisorCarrierZeroBased : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1)]

theorem divisorCarrierZeroBased_certificate :
    divisorCarrierZeroBased =
      [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0),
        (1, 1)] :=
  rfl

def divisorQuotientZeroBased : List Nat :=
  [0, 0, 1, 3, 4, 2, 2]

theorem divisorQuotientZeroBased_certificate :
    divisorQuotientZeroBased = [0, 0, 1, 3, 4, 2, 2] :=
  rfl

def sourceGeneratorsZeroBased : List Nat := [0, 1, 2, 3]

theorem sourceGeneratorsZeroBased_certificate :
    sourceGeneratorsZeroBased = [0, 1, 2, 3] :=
  rfl

def generatorLiftsZeroBased : List (Nat × Nat) :=
  [(0, 2), (1, 0), (0, 3), (0, 4)]

theorem generatorLiftsZeroBased_certificate :
    generatorLiftsZeroBased =
      [(0, 2), (1, 0), (0, 3), (0, 4)] :=
  rfl

def divisorSubMul (a b : Fin 7) : Fin 7 :=
  if a = 0 then
    if b = 0 then 0
    else if b = 1 then 1
    else if b = 2 then 1
    else if b = 3 then 0
    else if b = 4 then 0
    else if b = 5 then 5
    else 6
  else if a = 1 then
    if b = 0 then 1
    else if b = 1 then 0
    else if b = 2 then 0
    else if b = 3 then 1
    else if b = 4 then 1
    else if b = 5 then 6
    else 5
  else if a = 2 then
    if b = 0 then 1
    else if b = 1 then 0
    else if b = 2 then 0
    else if b = 3 then 1
    else if b = 4 then 1
    else if b = 5 then 6
    else 5
  else if a = 3 then
    b
  else if a = 4 then
    b
  else if a = 5 then
    if b = 0 then 5
    else if b = 1 then 6
    else if b = 2 then 6
    else if b = 3 then 5
    else if b = 4 then 5
    else if b = 5 then 0
    else 1
  else
    if b = 0 then 6
    else if b = 1 then 5
    else if b = 2 then 5
    else if b = 3 then 6
    else if b = 4 then 6
    else if b = 5 then 1
    else 0

def divisorSubTable : FiniteTable where
  order := 7
  mul := divisorSubMul
  assoc := by decide

private def target0 : Fin Generated.Catalogue.S5_461.table.order :=
  ⟨0, by decide⟩

private def target1 : Fin Generated.Catalogue.S5_461.table.order :=
  ⟨1, by decide⟩

private def target2 : Fin Generated.Catalogue.S5_461.table.order :=
  ⟨2, by decide⟩

private def target3 : Fin Generated.Catalogue.S5_461.table.order :=
  ⟨3, by decide⟩

private def target4 : Fin Generated.Catalogue.S5_461.table.order :=
  ⟨4, by decide⟩

private def source0 : Fin Generated.Catalogue.S5_438.table.order :=
  ⟨0, by decide⟩

private def source1 : Fin Generated.Catalogue.S5_438.table.order :=
  ⟨1, by decide⟩

private def source2 : Fin Generated.Catalogue.S5_438.table.order :=
  ⟨2, by decide⟩

private def source3 : Fin Generated.Catalogue.S5_438.table.order :=
  ⟨3, by decide⟩

private def source4 : Fin Generated.Catalogue.S5_438.table.order :=
  ⟨4, by decide⟩

private def divisor0 : Fin divisorSubTable.order :=
  ⟨0, by decide⟩

private def divisor2 : Fin divisorSubTable.order :=
  ⟨2, by decide⟩

private def divisor3 : Fin divisorSubTable.order :=
  ⟨3, by decide⟩

private def divisor4 : Fin divisorSubTable.order :=
  ⟨4, by decide⟩

private def divisor5 : Fin divisorSubTable.order :=
  ⟨5, by decide⟩

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (Generated.Catalogue.S5_461.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 7) (index : Fin 2) =>
    if index = 0 then
      if a = 0 then target0
      else if a = 1 then target0
      else if a = 2 then target0
      else if a = 3 then target0
      else if a = 4 then target0
      else target1
    else
      if a = 0 then target0
      else if a = 1 then target1
      else if a = 2 then target2
      else if a = 3 then target3
      else if a = 4 then target4
      else if a = 5 then target0
      else target1
  map_mul := by
    intro left right
    funext index
    exact by decide +revert
  injective := by
    intro left right equal
    have first := congrFun equal (0 : Fin 2)
    have second := congrFun equal (1 : Fin 2)
    clear equal
    exact by decide +revert

def divisorQuotient :
    SplitSurjection divisorSubTable.semigroup
      Generated.Catalogue.S5_438.table.semigroup where
  toFun := fun value : Fin 7 =>
    if value = 0 then source0
    else if value = 1 then source0
    else if value = 2 then source1
    else if value = 3 then source3
    else if value = 4 then source4
    else source2
  map_mul := by decide
  preimage := fun value : Fin 5 =>
    if value = 0 then divisor0
    else if value = 1 then divisor2
    else if value = 2 then divisor5
    else if value = 3 then divisor3
    else divisor4
  right_inverse := by
    intro value
    exact by decide +revert

theorem targetModels :
    Models Generated.Catalogue.S5_461.table.semigroup
      SemigroupBasis.CoRoots.S5_438.basis := by
  intro identity member
  simp only [SemigroupBasis.CoRoots.S5_438.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [← SemigroupBasis.CoRoots.S5_438.finiteStoredPowerLaw_map]
    exact Generated.Catalogue.S5_461.table.checkIdentityNat_sound
      SemigroupBasis.CoRoots.S5_438.finiteStoredPowerLaw
      (by decide)
  · rw [←
      SemigroupBasis.CoRoots.S5_438.finiteStoredPrefixInflationLaw_map]
    exact Generated.Catalogue.S5_461.table.checkIdentityNat_sound
      SemigroupBasis.CoRoots.S5_438.finiteStoredPrefixInflationLaw
      (by decide)
  · rw [← SemigroupBasis.CoRoots.S5_438.finiteStoredGatherLaw_map]
    exact Generated.Catalogue.S5_461.table.checkIdentityNat_sound
      SemigroupBasis.CoRoots.S5_438.finiteStoredGatherLaw
      (by decide)
  · rw [← SemigroupBasis.CoRoots.S5_438.finiteStoredPrefixSwapLaw_map]
    exact Generated.Catalogue.S5_461.table.checkIdentityNat_sound
      SemigroupBasis.CoRoots.S5_438.finiteStoredPrefixSwapLaw
      (by decide)

theorem representative_basis :
    BasisFor Generated.Catalogue.S5_461.table.semigroup
      SemigroupBasis.CoRoots.S5_438.basis :=
  SemigroupBasis.CoRoots.S5_438.basis_complete.inheritAlongPowerDivisor
      divisorSubEmbedding divisorQuotient targetModels

theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_461.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_438.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S5_438Transfers.S5_461

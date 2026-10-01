import SemigroupBasis.CoRoots.S5_624
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.S5_624Transfers.S5_638

open SemigroupBasis

/-- The seven certificate pairs in `S5_638²`, in quotient order. -/
def divisorCarrierZeroBased : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (2, 0), (4, 0)]

theorem divisorCarrierZeroBased_certificate :
    divisorCarrierZeroBased =
      [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (2, 0),
        (4, 0)] :=
  rfl

def divisorQuotientZeroBased : List Nat :=
  [0, 1, 2, 3, 0, 4, 4]

theorem divisorQuotientZeroBased_certificate :
    divisorQuotientZeroBased = [0, 1, 2, 3, 0, 4, 4] :=
  rfl

def generatorLiftsZeroBased : List (Nat × Nat) :=
  [(0, 1), (0, 3), (2, 0)]

theorem generatorLiftsZeroBased_certificate :
    generatorLiftsZeroBased = [(0, 1), (0, 3), (2, 0)] :=
  rfl

def sourceGeneratorsZeroBased : List Nat :=
  [1, 3, 4]

theorem sourceGeneratorsZeroBased_certificate :
    sourceGeneratorsZeroBased = [1, 3, 4] :=
  rfl

def divisorSubMul (a b : Fin 7) : Fin 7 :=
  if a = 0 then
    0
  else if a = 1 then
    if b = 0 then 0
    else if b = 1 then 0
    else if b = 2 then 1
    else if b = 3 then 1
    else 0
  else if a = 2 then
    if b = 0 then 4
    else if b = 1 then 4
    else if b = 2 then 2
    else if b = 3 then 3
    else 4
  else if a = 3 then
    if b = 0 then 4
    else if b = 1 then 4
    else if b = 2 then 3
    else if b = 3 then 2
    else 4
  else if a = 4 then
    4
  else if a = 5 then
    if b = 5 then 5 else 6
  else
    6

def divisorSubTable : FiniteTable where
  order := 7
  mul := divisorSubMul
  assoc := by decide

private def target0 :
    Fin Generated.Catalogue.S5_638.table.order :=
  ⟨0, by decide⟩

private def target1 :
    Fin Generated.Catalogue.S5_638.table.order :=
  ⟨1, by decide⟩

private def target2 :
    Fin Generated.Catalogue.S5_638.table.order :=
  ⟨2, by decide⟩

private def target3 :
    Fin Generated.Catalogue.S5_638.table.order :=
  ⟨3, by decide⟩

private def target4 :
    Fin Generated.Catalogue.S5_638.table.order :=
  ⟨4, by decide⟩

private def source0 :
    Fin Generated.Catalogue.S5_624.table.order :=
  ⟨0, by decide⟩

private def source1 :
    Fin Generated.Catalogue.S5_624.table.order :=
  ⟨1, by decide⟩

private def source2 :
    Fin Generated.Catalogue.S5_624.table.order :=
  ⟨2, by decide⟩

private def source3 :
    Fin Generated.Catalogue.S5_624.table.order :=
  ⟨3, by decide⟩

private def source4 :
    Fin Generated.Catalogue.S5_624.table.order :=
  ⟨4, by decide⟩

private def divisor0 : Fin divisorSubTable.order :=
  ⟨0, by decide⟩

private def divisor1 : Fin divisorSubTable.order :=
  ⟨1, by decide⟩

private def divisor2 : Fin divisorSubTable.order :=
  ⟨2, by decide⟩

private def divisor3 : Fin divisorSubTable.order :=
  ⟨3, by decide⟩

private def divisor5 : Fin divisorSubTable.order :=
  ⟨5, by decide⟩

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (Generated.Catalogue.S5_638.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 7) (i : Fin 2) =>
    if i = 0 then
      if a = 0 then target0
      else if a = 1 then target0
      else if a = 2 then target0
      else if a = 3 then target0
      else if a = 4 then target0
      else if a = 5 then target2
      else target4
    else
      if a = 0 then target0
      else if a = 1 then target1
      else if a = 2 then target2
      else if a = 3 then target3
      else if a = 4 then target4
      else target0
  map_mul := by
    intro a b
    funext i
    exact by decide +revert
  injective := by
    intro a b equality
    have first := congrFun equality (0 : Fin 2)
    have second := congrFun equality (1 : Fin 2)
    clear equality
    exact by decide +revert

def divisorQuotient :
    SplitSurjection divisorSubTable.semigroup
      Generated.Catalogue.S5_624.table.semigroup where
  toFun := fun a : Fin 7 =>
    if a = 0 then source0
    else if a = 1 then source1
    else if a = 2 then source2
    else if a = 3 then source3
    else if a = 4 then source0
    else source4
  map_mul := by
    decide
  preimage := fun b : Fin 5 =>
    if b = 0 then divisor0
    else if b = 1 then divisor1
    else if b = 2 then divisor2
    else if b = 3 then divisor3
    else divisor5
  right_inverse := by
    intro b
    exact by decide +revert

theorem targetModels :
    Models Generated.Catalogue.S5_638.table.semigroup
      SemigroupBasis.CoRoots.S5_624.basis := by
  intro identity member
  simp only [SemigroupBasis.CoRoots.S5_624.basis,
    SemigroupBasis.Examples.headPositiveParitySuffixBasis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [← SemigroupBasis.CoRoots.S5_624.finiteHeadPowerLaw_map]
    exact Generated.Catalogue.S5_638.table.checkIdentityNat_sound
      SemigroupBasis.CoRoots.S5_624.finiteHeadPowerLaw (by decide)
  · rw [← SemigroupBasis.CoRoots.S5_624.finiteContextPowerLaw_map]
    exact Generated.Catalogue.S5_638.table.checkIdentityNat_sound
      SemigroupBasis.CoRoots.S5_624.finiteContextPowerLaw (by decide)
  · rw [← SemigroupBasis.CoRoots.S5_624.finiteGatherLaw_map]
    exact Generated.Catalogue.S5_638.table.checkIdentityNat_sound
      SemigroupBasis.CoRoots.S5_624.finiteGatherLaw (by decide)
  · rw [← SemigroupBasis.CoRoots.S5_624.finiteSuffixSwapLaw_map]
    exact Generated.Catalogue.S5_638.table.checkIdentityNat_sound
      SemigroupBasis.CoRoots.S5_624.finiteSuffixSwapLaw (by decide)

theorem representative_basis :
    BasisFor Generated.Catalogue.S5_638.table.semigroup
      SemigroupBasis.CoRoots.S5_624.basis :=
  SemigroupBasis.CoRoots.S5_624.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels

theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_638.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_624.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S5_624Transfers.S5_638

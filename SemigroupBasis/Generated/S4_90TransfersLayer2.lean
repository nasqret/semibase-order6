import SemigroupBasis.Generated.S4_90TransfersLayer1

namespace SemigroupBasis.Generated.S4_90Transfers

open SemigroupBasis
open SemigroupBasis.CoRoots.S4_90

-- BEGIN S5_668
namespace S5_668

def divisorSubMul (a b : Fin 7) : Fin 7 :=
  if a = 0 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (3 : Fin 7) else if b = 5 then (3 : Fin 7) else (0 : Fin 7) else if a = 1 then if b = 0 then (1 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (1 : Fin 7) else if b = 3 then (4 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (4 : Fin 7) else (1 : Fin 7) else if a = 2 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (3 : Fin 7) else if b = 5 then (5 : Fin 7) else (0 : Fin 7) else if a = 3 then if b = 0 then (3 : Fin 7) else if b = 1 then (3 : Fin 7) else if b = 2 then (3 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (0 : Fin 7) else (3 : Fin 7) else if a = 4 then if b = 0 then (4 : Fin 7) else if b = 1 then (4 : Fin 7) else if b = 2 then (4 : Fin 7) else if b = 3 then (1 : Fin 7) else if b = 4 then (1 : Fin 7) else if b = 5 then (1 : Fin 7) else (4 : Fin 7) else if a = 5 then if b = 0 then (3 : Fin 7) else if b = 1 then (3 : Fin 7) else if b = 2 then (5 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (2 : Fin 7) else (3 : Fin 7) else if b = 0 then (1 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (1 : Fin 7) else if b = 3 then (4 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (4 : Fin 7) else (6 : Fin 7)

def divisorSubTable : FiniteTable where
  order := 7
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_668.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 7) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (1 : Fin 5) else if a = 4 then (1 : Fin 5) else if a = 5 then (1 : Fin 5) else (4 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (4 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (2 : Fin 5) else if a = 5 then (4 : Fin 5) else (2 : Fin 5)
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
      SemigroupBasis.Generated.Catalogue.S5_981.table.semigroup where
  toFun := fun a : Fin 7 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else if a = 5 then (1 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (2 : Fin 7) else if b = 1 then (5 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (1 : Fin 7) else (6 : Fin 7)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixParityCommutationLaw := rfl

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = suffixParityPowerLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_668.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteSuffixCommutationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_668.table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_668.table.checkIdentityNat_sound finitePowerLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_668.table.semigroup basis :=
  SemigroupBasis.Generated.S4_90Transfers.S5_981.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_668.table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S5_668
-- END S5_668

end SemigroupBasis.Generated.S4_90Transfers

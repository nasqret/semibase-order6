import SemigroupBasis.Generated.NormalBandTransfersLayer1

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.NormalBandTransfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S5_1142
namespace S5_1142

def divisorSubMul
    (a b : Fin 7) : Fin 7 :=
  if a = 0 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (3 : Fin 7) else if b = 5 then (0 : Fin 7) else (3 : Fin 7) else if a = 1 then if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (3 : Fin 7) else if b = 5 then (0 : Fin 7) else (3 : Fin 7) else if a = 2 then if b = 0 then (2 : Fin 7) else if b = 1 then (2 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (4 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (2 : Fin 7) else (4 : Fin 7) else if a = 3 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (3 : Fin 7) else if b = 5 then (0 : Fin 7) else (3 : Fin 7) else if a = 4 then if b = 0 then (2 : Fin 7) else if b = 1 then (2 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (4 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (2 : Fin 7) else (4 : Fin 7) else if a = 5 then if b = 0 then (2 : Fin 7) else if b = 1 then (2 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (4 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7) else if b = 0 then (2 : Fin 7) else if b = 1 then (2 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (4 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7)

def divisorSubTable : FiniteTable where
  order := 7
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_1142.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 7) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (0 : Fin 5) else if a = 5 then (1 : Fin 5) else (1 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (4 : Fin 5) else if a = 5 then (2 : Fin 5) else (4 : Fin 5)
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
      SemigroupBasis.Generated.Catalogue.S5_1040.table.semigroup where
  toFun := fun a : Fin 7 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (2 : Fin 5) else if a = 5 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (5 : Fin 7) else (6 : Fin 7)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteInteriorSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val =
      normalBandIdempotenceLaw := rfl

theorem finiteInteriorSwapLaw_map :
    finiteInteriorSwapLaw.map Fin.val =
      normalBandInteriorSwapLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1142.table.semigroup normalBandBasis := by
  intro e he
  simp only [normalBandBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1142.table.checkIdentityNat_sound
      finiteIdempotenceLaw (by decide)
  · rw [← finiteInteriorSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1142.table.checkIdentityNat_sound
      finiteInteriorSwapLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1142.table.semigroup
      normalBandBasis :=
  SemigroupBasis.Generated.NormalBandTransfers.S5_1040.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


end S5_1142
-- END S5_1142

end SemigroupBasis.Generated.NormalBandTransfers

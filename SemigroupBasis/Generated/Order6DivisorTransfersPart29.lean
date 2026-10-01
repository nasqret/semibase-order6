import SemigroupBasis.Generated.S4_9
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6DivisorTransfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S6_4816
namespace S6_4816

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,2,2,2,2],[1,1,2,2,2,1],[1,1,2,2,2,2]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "982dd14aec80661038de5affaf0f61a2f28a05ed1cddfc999a5e9fc672beca28"

def embedding :
    Embedding SemigroupBasis.Generated.S4_9.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4816
-- END S6_4816

-- BEGIN S6_4817
namespace S6_4817

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,2,2,2,2],[1,1,2,2,2,2],[1,1,2,2,2,2]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a39714d7cb5b5c330b60926dd31639cf29f1ab79ed7477f84c993b45221a8896"

def embedding :
    Embedding SemigroupBasis.Generated.S4_9.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4817
-- END S6_4817

-- BEGIN S6_4867
namespace S6_4867

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,1],[1,1,1,1,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "856e3b0ba03e14ffd0b8cca5027358c5989110582c3d29f0f14fd04c234f3335"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4867
-- END S6_4867

-- BEGIN S6_4868
namespace S6_4868

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,1],[1,1,1,1,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "00fd75c0e585a3d1da440252358f5f0e960fb20e500597c2cf1b9b9e729fbb11"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4868
-- END S6_4868

-- BEGIN S6_4869
namespace S6_4869

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,1],[1,1,1,2,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "78d054f625c9c68119b7938c7425d2af9ecff8b47dcdcb1e7546b846946bd85b"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4869
-- END S6_4869

-- BEGIN S6_4870
namespace S6_4870

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,1],[1,1,1,2,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "297e0c26b21693539edf7bdf106d03996f5802aefbe21ab8de5bea859ed92cb3"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4870
-- END S6_4870

-- BEGIN S6_4871
namespace S6_4871

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,1],[1,1,1,3,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "87a73c08119b689d054d315c46dac772340ad17cc2b74e783db00be23d555bd2"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4871
-- END S6_4871

-- BEGIN S6_4873
namespace S6_4873

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,2],[1,1,1,1,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "065ee83bfe46c224417134390dcd4e146f4e4e61ac521e76d2f67b7e470b2648"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (1 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4873
-- END S6_4873

-- BEGIN S6_4874
namespace S6_4874

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,2],[1,1,1,2,1,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "669c3cb137ca49e0bfbd0c2faff358566135dfb5a0d7c3ea7ab6cae26404e287"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (1 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

end S6_4874
-- END S6_4874

-- BEGIN S6_4875
namespace S6_4875

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,2],[1,1,1,2,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a2400a7dce983e114f1aebdcc3c47e28dc3ad6b63b1508cdf9174b3027c9a4f8"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4875
-- END S6_4875

-- BEGIN S6_4876
namespace S6_4876

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,2],[1,1,1,2,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c97e16a7442280c2ba6201a3f3661cc36a4fa6791c117327205d3aa4cb6fdb2e"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (1 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4876
-- END S6_4876

-- BEGIN S6_4877
namespace S6_4877

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,2],[1,1,1,3,1,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c4c6463de5967d5d96bb69e23a544f26bbf0c287faa937f46d6e41273bd31fcf"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4877
-- END S6_4877

-- BEGIN S6_4878
namespace S6_4878

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,2],[1,1,1,3,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "77c1182574daa305800d4a19aedcfa0dde14db09100f47b81e508ebbc3d5b0c0"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4878
-- END S6_4878

-- BEGIN S6_4879
namespace S6_4879

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,2],[1,1,1,3,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4f49189e9f35060beaf141b0879f94b86c6bcac69014b838e9c83d868edf2a66"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4879
-- END S6_4879

-- BEGIN S6_4881
namespace S6_4881

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,3],[1,1,1,2,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c7e98ff30a20a675771834f831882dce4112d09e2aafbc3276261bcae3c64709"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4881
-- END S6_4881

-- BEGIN S6_4882
namespace S6_4882

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,3],[1,1,1,2,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c5db9b58472d8da4b03ce470ebb8fdf469e57c87d59d40441cb5c2cc975107e6"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4882
-- END S6_4882

-- BEGIN S6_4883
namespace S6_4883

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,3],[1,1,1,3,1,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "853dc8dc124c41465fec51c7e3b0445e8f78df1d6b276ad13dd19eee777c550b"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

end S6_4883
-- END S6_4883

-- BEGIN S6_4884
namespace S6_4884

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,3],[1,1,1,3,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d976afc20931b66629c8536c3aae37110353579763c64620a986e65952587aaf"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4884
-- END S6_4884

-- BEGIN S6_4885
namespace S6_4885

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,1,2,3],[1,1,1,3,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "59d20a5cdd1327e72e7252bb0ffe5f29888e2c995a3f4fac0ee4105de459503b"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4885
-- END S6_4885

-- BEGIN S6_4887
namespace S6_4887

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,1],[1,1,1,1,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b0771d9be5841a2f1e8d15874868a0e902a879a924b2e8c1b79ea6bb54b4da60"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4887
-- END S6_4887

-- BEGIN S6_4888
namespace S6_4888

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,1],[1,1,1,1,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "95eb91bcc2fd0e36219f0cf843a3b6bc785421e6b61a44fa3cf130cebf237f43"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4888
-- END S6_4888

-- BEGIN S6_4889
namespace S6_4889

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,1],[1,1,1,2,1,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5ba7bf5fc23df0143c017b5021fc7ae68cb3e14e7ad99be76aa9d18ef91035ae"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4889
-- END S6_4889

-- BEGIN S6_4890
namespace S6_4890

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,1],[1,1,1,2,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "13936da670a028ded6bd4c1d6163ed1ae1f0bbcdd5a4a4294524386ea380f0bf"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4890
-- END S6_4890

-- BEGIN S6_4891
namespace S6_4891

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,1],[1,1,1,2,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "612274e803082b97af8511f4e86d7addd04b168d55edacf294389dece4b8c94d"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4891
-- END S6_4891

-- BEGIN S6_4892
namespace S6_4892

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,1],[1,1,1,3,1,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "683fa5072b623c99f8e3313ccb01d25982e4f7f9e630131690b909ba0a8ff1d3"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4892
-- END S6_4892

-- BEGIN S6_4893
namespace S6_4893

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,1],[1,1,1,3,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4f2735a6feee4f21413ea1c3fcdbf4aab4bc192d6f6d1024ccc1303048abb107"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4893
-- END S6_4893

-- BEGIN S6_4894
namespace S6_4894

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,1],[1,1,1,3,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8957a99d4b3c9e9afc9bfb1c598f2a5ecfee0904a40933701c44939b611575fb"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4894
-- END S6_4894

-- BEGIN S6_4896
namespace S6_4896

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,2],[1,1,1,1,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c81b6c20effd745d06f290cb8876f07ada87c6e7e6ed00fe40036644bc044db4"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (1 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4896
-- END S6_4896

-- BEGIN S6_4897
namespace S6_4897

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,2],[1,1,1,2,1,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a2b8d269dbeddf2b1fbd33f21722153a2b3ba8c6baa776c36c7ec65303f6784e"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (1 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

end S6_4897
-- END S6_4897

-- BEGIN S6_4898
namespace S6_4898

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,2],[1,1,1,2,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cb26069f3e2468bc6010ef9cbf9d9266be9af9496686b0dbcf8e34298d07ae61"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4898
-- END S6_4898

-- BEGIN S6_4899
namespace S6_4899

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,2],[1,1,1,2,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "fa0dfe644047b03392a6babfc2726b07645736b629d7c19eda2c1b7adf5d3720"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (1 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4899
-- END S6_4899

-- BEGIN S6_4900
namespace S6_4900

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,2],[1,1,1,3,1,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cf82168d72c24ee949f284ac1e6fd6a286b3e73906641db9e107dfdc8db735b1"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4900
-- END S6_4900

-- BEGIN S6_4901
namespace S6_4901

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,2],[1,1,1,3,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e5bf6299a1a1ab71d7942d799891a435f329ea24dffe1185fb84c2a458a9e4fe"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4901
-- END S6_4901

-- BEGIN S6_4902
namespace S6_4902

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,2],[1,1,1,3,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5a97fe275deeefa0ff276442376d862de10be30e1a0564d22bf06d644e4569cb"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4902
-- END S6_4902

-- BEGIN S6_4903
namespace S6_4903

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,3],[1,1,1,1,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e50480a56bb15a8b531c090fe8c9bba4765015b6fef6cbe6bcacaaf18f654815"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4903
-- END S6_4903

-- BEGIN S6_4905
namespace S6_4905

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,3],[1,1,1,2,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "25a01a5b4a143b71e8a07314dd2fd716673e3c668bb7222ad85ae8fce998f066"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4905
-- END S6_4905

-- BEGIN S6_4906
namespace S6_4906

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,3],[1,1,1,2,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "3b0d7599c2722b918b90b46e53c3cc3256924435d2e97956634106db0e5747fa"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4906
-- END S6_4906

-- BEGIN S6_4907
namespace S6_4907

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,3],[1,1,1,3,1,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2f7a630307f2cb0b6469f759ee929c7c4bbbba7c7a3fcc753998240f2d69d6ac"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

end S6_4907
-- END S6_4907

-- BEGIN S6_4908
namespace S6_4908

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,3],[1,1,1,3,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "dfeec01301a65fa07668c129e39b2dd0083d6fd060217571922c5add1dce1c34"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4908
-- END S6_4908

-- BEGIN S6_4909
namespace S6_4909

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,2,2,3],[1,1,1,3,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b031c28b617f24e850cbd7003d614c738e0791ded40675b8369eed646bddaaa7"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4909
-- END S6_4909

-- BEGIN S6_4911
namespace S6_4911

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,1],[1,1,1,1,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a63afb730bec350311f7d879937d1ed28f81da41a48df87ec7de4846f661ae1a"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4911
-- END S6_4911

-- BEGIN S6_4912
namespace S6_4912

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,1],[1,1,1,1,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0ef962c113cd89099fb88742d9b30d78f909e22c0ba6992d2082def9dabc911e"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4912
-- END S6_4912

-- BEGIN S6_4913
namespace S6_4913

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,1],[1,1,1,2,1,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ccdf075961c685a3467bdebbde4c2085147a23659c7a000f4981450273dd9a4f"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4913
-- END S6_4913

-- BEGIN S6_4914
namespace S6_4914

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,1],[1,1,1,2,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "74ce2fe5e632ee19121e361f7718df6398d25148decca90c7a1806c3c9df839c"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4914
-- END S6_4914

-- BEGIN S6_4915
namespace S6_4915

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,1],[1,1,1,2,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "7e60c401bf3df63516a7add7252859e990898c693b56ea7913e6b2b0434af51c"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4915
-- END S6_4915

-- BEGIN S6_4916
namespace S6_4916

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,1],[1,1,1,3,1,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5f71329cd1b41d706fcb605b16246d1b44c374a40c62f0173105b621312014f6"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4916
-- END S6_4916

-- BEGIN S6_4917
namespace S6_4917

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,1],[1,1,1,3,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "1eebd4202d0b6ec778bad19de0c7224c2fb12aae2dd2b90f35747bb541c2f96a"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4917
-- END S6_4917

-- BEGIN S6_4918
namespace S6_4918

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,1],[1,1,1,3,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b69b16c8063310f97af2e37c4bf83232f647d09c6c81d80314096e95d71b80c1"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4918
-- END S6_4918

-- BEGIN S6_4920
namespace S6_4920

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,2],[1,1,1,1,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "f41b5f30ac0399ad40e9881366c2ad454c421fbea6b56c6b820c021cac5283d3"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (1 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4920
-- END S6_4920

-- BEGIN S6_4921
namespace S6_4921

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,2],[1,1,1,2,1,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a9f7012d06b98657871462e2757ff4e949abf4d466675ca81a095920f51846c8"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (1 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

end S6_4921
-- END S6_4921

-- BEGIN S6_4922
namespace S6_4922

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,2],[1,1,1,2,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "784876b048b6a615383bca218965e16ca1e84cd2d4e9c7495188df28d1de6845"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4922
-- END S6_4922

-- BEGIN S6_4923
namespace S6_4923

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,2],[1,1,1,2,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cd0a415a94cd74c91a457cd2fe60369eb155ff229b351473c1390623ae83526a"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (1 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4923
-- END S6_4923

-- BEGIN S6_4924
namespace S6_4924

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,2],[1,1,1,3,1,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "25ad953de37132ed503cfa1e95e04d2d531d548521031961ba37a6005419011c"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4924
-- END S6_4924

-- BEGIN S6_4925
namespace S6_4925

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,2],[1,1,1,3,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "69bcf77159cfc592a731199e2aaed952ea4f44cbdee93d41504ec5f647d465a1"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4925
-- END S6_4925

-- BEGIN S6_4926
namespace S6_4926

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,2],[1,1,1,3,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "deb950287d40e5c88cfe32a94982a804ab8c77abae17e1eac4d853c1f72ff8e3"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4926
-- END S6_4926

-- BEGIN S6_4927
namespace S6_4927

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,3],[1,1,1,1,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "6b93788b0c94d4b621dad3c01d6feeaabb7b989dbc46eda403beb2366a80d5d2"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4927
-- END S6_4927

-- BEGIN S6_4929
namespace S6_4929

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,3],[1,1,1,2,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e8a8b675fc759363c3b7841ae9018e20215900bb0e129d91b82339f98d104c78"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4929
-- END S6_4929

-- BEGIN S6_4930
namespace S6_4930

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,3],[1,1,1,2,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "03ba08878ea9e69a375cc2d34ca2a916fd9daab4d79f804bf366dfe1fbfa41ae"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else (3 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨2, [1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY.reversed := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX.reversed := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY.reversed := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ.reversed := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX.reversed := rfl

theorem targetModels :
    Models table.semigroup (reversedBasis threeNilpotentFourBasis) := by
  intro e he
  simp only [reversedBasis, threeNilpotentFourBasis, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (reversedBasis threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.opposite_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (reversedBasis threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4930
-- END S6_4930

-- BEGIN S6_4931
namespace S6_4931

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,3],[1,1,1,3,1,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b431f35037672ee3911ed4aee18ff5b9a52275f71857b148c27bae57092bc836"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

end S6_4931
-- END S6_4931

-- BEGIN S6_4932
namespace S6_4932

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,3],[1,1,1,3,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "11b107996fb613b6461bca5ee1ea6e8fbc891a4d3f4485a478e38c3b45df5a20"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4932
-- END S6_4932

-- BEGIN S6_4933
namespace S6_4933

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,3],[1,1,1,3,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c01b8b5d48c45510b61b1900b0f1508825116f42f88ba3b3da670a8708a0af71"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4933
-- END S6_4933

-- BEGIN S6_4935
namespace S6_4935

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,2],[1,1,1,1,2,2],[1,1,1,2,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "fe0e005b4f5dab5ff3dfe7a00ebdff7522b9100c0001d78330f1d24cf1f86d27"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (1 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4935
-- END S6_4935

-- BEGIN S6_4936
namespace S6_4936

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,2],[1,1,1,1,2,2],[1,1,1,3,3,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "904abbcde78460eff375f173b8aa8e190d3bb4869c0d53b97ad8052099a555be"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (1 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis (threeNilpotentFourBasis)) :=
  representative_basis.oppositeReversed

end S6_4936
-- END S6_4936

-- BEGIN S6_4938
namespace S6_4938

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,2],[1,1,1,1,2,3],[1,1,1,3,2,3]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0ad096b39e1482a7c71dcb3e9a61715c53f5988054dc51c5065ee25879c8cc2e"

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (1 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = threeNilpotentXXXLawXXY := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = threeNilpotentXXXLawXYX := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = threeNilpotentXXXLawXYY := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = threeNilpotentXXXLawXYZ := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = threeNilpotentXXXLawYXX := rfl

theorem targetModels :
    Models table.semigroup (threeNilpotentFourBasis) := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)

theorem representative_basis :
    BasisFor table.semigroup (threeNilpotentFourBasis) :=
  SemigroupBasis.Generated.S4_9.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

end S6_4938
-- END S6_4938

end SemigroupBasis.Generated.Order6DivisorTransfers

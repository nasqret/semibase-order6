import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Generated.S4_28
import SemigroupBasis.Generated.S4_72
import SemigroupBasis.Generated.S4_76
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6ExtensionTransfersV3

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S6_1229
namespace S6_1229

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,5,1],[1,1,1,1,5,1],[1,1,1,1,5,1],[1,1,1,1,5,4],[5,5,5,5,1,5],[1,1,1,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ab599f150a32f04149ff37f11b85ef52405c104d7addf338609a49f4b0f2ea01"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1229
-- END S6_1229

-- BEGIN S6_1241
namespace S6_1241

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,5,1],[1,1,1,1,5,1],[1,1,1,1,5,3],[1,1,1,1,5,3],[5,5,5,5,1,5],[1,1,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "38427a76e152dbb34dcf0a603b294f2fd7192e4f62289a988a8e5aea6d012acd"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1241
-- END S6_1241

-- BEGIN S6_1246
namespace S6_1246

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,5,1],[1,1,1,1,5,1],[1,1,1,1,5,3],[1,1,1,1,5,4],[5,5,5,5,1,5],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "53177736cc870163ef09dd0835bf2a5261ed763498f276408ed7e7f96b6fe4bd"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1246
-- END S6_1246

-- BEGIN S6_1251
namespace S6_1251

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,5,1],[1,1,1,1,5,2],[1,1,1,1,5,2],[1,1,1,1,5,2],[5,5,5,5,1,5],[1,2,2,2,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "908bac40929752b852ae17918d24153faaf5a89230afb8e14a2a6a1c6700ce6c"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1251
-- END S6_1251

-- BEGIN S6_1255
namespace S6_1255

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,5,1],[1,1,1,1,5,2],[1,1,1,1,5,2],[1,1,1,1,5,4],[5,5,5,5,1,5],[1,2,2,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b4e1e4e0ac15404cc9896395bcbc459d95c49b98b7f501fa5549a82c083a2bab"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1255
-- END S6_1255

-- BEGIN S6_1258
namespace S6_1258

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,5,1],[1,1,1,1,5,2],[1,1,1,1,5,3],[1,1,1,1,5,4],[5,5,5,5,1,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "fc6bcd7effeae4ae8c590e0c9a03bae50c8d8c9844b83095d8e97e015441424b"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1258
-- END S6_1258

-- BEGIN S6_1263
namespace S6_1263

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,5,1],[1,1,1,1,5,2],[1,1,1,2,5,3],[1,1,2,1,5,4],[5,5,5,5,1,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "80bde039f15e6bf68cce366553bf6abeffe009569a8a6d5fecddc8c83c322e09"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1263
-- END S6_1263

-- BEGIN S6_1282
namespace S6_1282

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,1],[1,1,1,4,4,3],[4,4,4,1,1,4],[4,4,4,1,1,4],[1,1,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "acd4d4a0678b1bc33c13441d9bdc69696c1ba90748b652a959d197f993b8cddf"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1282
-- END S6_1282

-- BEGIN S6_1288
namespace S6_1288

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,1],[1,1,1,4,4,3],[4,4,4,1,1,4],[4,4,4,1,1,5],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "bc2a1a11cdab3010e3462dd1bc492412f2987dc1ce2b91ef49272a05aacf9e42"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1288
-- END S6_1288

-- BEGIN S6_1292
namespace S6_1292

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,2],[1,1,1,4,4,2],[4,4,4,1,1,4],[4,4,4,1,1,4],[1,2,2,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a78a20b984825ed1955b90efea423119ca6eafdeb3f3a3c2095b7a13838fe7df"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1292
-- END S6_1292

-- BEGIN S6_1296
namespace S6_1296

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,2],[1,1,1,4,4,2],[4,4,4,1,1,4],[4,4,4,1,1,5],[1,2,2,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c59c39a37c9fe6ea47590b27cf9d500e61c47557f7c1f857ca00afa718df5a9e"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1296
-- END S6_1296

-- BEGIN S6_1299
namespace S6_1299

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,2],[1,1,1,4,4,3],[4,4,4,1,1,4],[4,4,4,1,1,4],[1,2,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "83fd8b2c06a0e95cfafc4cc66d6451e42a34b5d306f79e07ec03e2825b67c6d2"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1299
-- END S6_1299

-- BEGIN S6_1301
namespace S6_1301

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,4,1],[1,1,1,4,4,2],[1,1,1,4,4,3],[4,4,4,1,1,4],[4,4,4,1,1,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "bac483331ccb74c64a6141bf6ed9678b674c5b921882f4ff6ae3e7c1bbf2fed4"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1301
-- END S6_1301

-- BEGIN S6_1337
namespace S6_1337

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,3,1],[1,1,3,3,3,2],[3,3,1,1,1,3],[3,3,1,1,1,3],[3,3,1,1,1,3],[1,2,3,3,3,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2a14c6b81e6dfa5e760d5c226d7dcc05db7bed099e636f48c039a2a4e10adbae"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1337
-- END S6_1337

-- BEGIN S6_1341
namespace S6_1341

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,3,1],[1,1,3,3,3,2],[3,3,1,1,1,3],[3,3,1,1,1,3],[3,3,1,1,1,5],[1,2,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "83e6291a63a8c3e1bdde5847c153fe7ff948a0b501fa61a245f7497c80a798c0"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1341
-- END S6_1341

-- BEGIN S6_1344
namespace S6_1344

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,3,1],[1,1,3,3,3,2],[3,3,1,1,1,3],[3,3,1,1,1,4],[3,3,1,1,1,4],[1,2,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0e71f5b3c12baca69e36583bf54a354235ab3f3d84bbbaaedc8319629a033af1"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1344
-- END S6_1344

-- BEGIN S6_1346
namespace S6_1346

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,3,1],[1,1,3,3,3,2],[3,3,1,1,1,3],[3,3,1,1,1,4],[3,3,1,1,1,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "1e8408088567812de3ff7994b7a07e4f5cbf5694b4a1af1fdf31ccf7a0f2ce03"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1346
-- END S6_1346

-- BEGIN S6_1355
namespace S6_1355

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,3,1],[1,1,3,3,3,2],[3,3,1,1,1,3],[3,3,1,1,2,4],[3,3,1,2,1,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a6a4c27b28c0bdd744461de060e9f8489318a76833d2391d1d613c0216d30bef"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1355
-- END S6_1355

-- BEGIN S6_1357
namespace S6_1357

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,3,1],[1,1,3,3,4,2],[3,3,1,1,1,3],[3,3,1,1,1,4],[3,4,1,1,1,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (2 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "964e29ba1a956c608757b3022f4ac996c41e9bca102ae3d334a2fe99987265ec"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1357
-- END S6_1357

-- BEGIN S6_1365
namespace S6_1365

/-- Exact one-based order-six catalogue table: `[[1,1,3,4,5,1],[1,1,3,4,5,2],[3,3,1,5,4,3],[4,4,5,1,3,4],[5,5,4,3,1,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2fb184f3337b0f25fc18a4724f7dd02e658a63101868000bf0cc8e7a4d09cf21"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_1365
-- END S6_1365

-- BEGIN S6_1401
namespace S6_1401

/-- Exact one-based order-six catalogue table: `[[1,2,2,4,5,1],[2,1,1,5,4,2],[2,1,1,5,4,3],[4,5,5,1,2,4],[5,4,4,2,1,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cdc84e56765429fffdc8b65a9dc8fe73725bd35cb7956bf923f16b7c2ace7803"

def subMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def subTable : FiniteTable where
  order := 6
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 6 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup where
  toFun := fun a : Fin 6 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (3 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

end S6_1401
-- END S6_1401

-- BEGIN S6_3080
namespace S6_3080

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,1,1],[1,1,1,4,3,3],[4,4,4,1,4,4],[1,1,3,4,5,5],[1,1,3,4,5,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "bd976026eb83f1348b8f3710962e6a6561402ec95ecf0d3928387745a37a0208"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_3080
-- END S6_3080

-- BEGIN S6_3081
namespace S6_3081

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,1,1],[1,1,1,4,3,3],[4,4,4,1,4,4],[1,1,3,4,5,6],[1,1,3,4,6,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e4afb7f12573c21f9d561be47d2474b2d103e43e1f0912e2ca6245ee1b7be660"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_3081
-- END S6_3081

-- BEGIN S6_3086
namespace S6_3086

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,2,2],[1,1,1,4,2,2],[4,4,4,1,4,4],[1,2,2,4,5,5],[1,2,2,4,5,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "eacb9c4ad4c928be2c8f7af904629af4ac067c3d9d49573016f18d88318b7b85"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_3086
-- END S6_3086

-- BEGIN S6_3087
namespace S6_3087

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,2,2],[1,1,1,4,2,2],[4,4,4,1,4,4],[1,2,2,4,5,6],[1,2,2,4,6,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "da82d0cbe47c8676bf2ec75b7f79e35e9df7c6b5c5f617b6d14693b256b36f8f"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_3087
-- END S6_3087

-- BEGIN S6_3090
namespace S6_3090

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,2,2],[1,1,1,4,3,3],[4,4,4,1,4,4],[1,2,3,4,5,5],[1,2,3,4,5,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "f2c29dfde5b1343fd7e7c901242dadfd0184f0aa0143413281954a01659ae2a7"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_3090
-- END S6_3090

-- BEGIN S6_3091
namespace S6_3091

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,2,2],[1,1,1,4,3,3],[4,4,4,1,4,4],[1,2,3,4,5,6],[1,2,3,4,6,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "809d8e22a911f8d264642eba689c49862292318c7d8e12926a7fbb22adb51997"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_3091
-- END S6_3091

-- BEGIN S6_3093
namespace S6_3093

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,2,3],[1,1,1,4,3,2],[4,4,4,1,4,4],[1,2,3,4,5,6],[1,3,2,4,6,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "af6b74088416100ca6b2e304a1a23ae5312d244d42706be38bb698fcc95c3d74"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_3093
-- END S6_3093

-- BEGIN S6_3115
namespace S6_3115

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,1,1],[1,1,3,3,2,2],[3,3,1,1,3,3],[3,3,1,1,3,3],[1,2,3,3,5,5],[1,2,3,3,5,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "433c5c3edbff19b2049d0a317e72c2cc4ece0a5df628d7694f21d160d38f1b52"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_3115
-- END S6_3115

-- BEGIN S6_3116
namespace S6_3116

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,1,1],[1,1,3,3,2,2],[3,3,1,1,3,3],[3,3,1,1,3,3],[1,2,3,3,5,6],[1,2,3,3,6,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (5 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "44bf2b8e007d81d8c01d33a23bb734f88d3059477f301869444bea7af52d98cb"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_3116
-- END S6_3116

-- BEGIN S6_3119
namespace S6_3119

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,1,1],[1,1,3,3,2,2],[3,3,1,1,3,3],[3,3,1,1,4,4],[1,2,3,4,5,5],[1,2,3,4,5,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "54e0b9c3b4ebd549a55de184dc32e131a2143006ba7acc63a488d9f046b2ab24"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_3119
-- END S6_3119

-- BEGIN S6_3120
namespace S6_3120

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,1,1],[1,1,3,3,2,2],[3,3,1,1,3,3],[3,3,1,1,4,4],[1,2,3,4,5,6],[1,2,3,4,6,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "62d0df94dd90aa48027730e0f9108d8dc3d32acc93e228b3421a05d5d26b702c"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_3120
-- END S6_3120

-- BEGIN S6_3124
namespace S6_3124

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,1,3],[1,1,3,3,2,4],[3,3,1,1,3,1],[3,3,1,1,4,2],[1,2,3,4,5,6],[3,4,1,2,6,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (2 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (5 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "fe623064c2ea71aad829c5f31c6e17e245ee917cd00643d2ee3cbddd63c8302a"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_3124
-- END S6_3124

-- BEGIN S6_3317
namespace S6_3317

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,4],[5,5,5,5,5,5],[5,5,5,5,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8a6517d8ddd0f823751cebb0a360ffd1fb46405e40c639b8fe383e7f968b5f3c"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_76.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_76.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_76.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_76.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_3317
-- END S6_3317

-- BEGIN S6_3455
namespace S6_3455

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,1,1,1,1,3],[5,5,5,5,5,5],[5,5,5,5,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "1e117e0be271d5cce0314a00743c183de3a79156f43e5d3e86af0bf0c31c1c20"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_76.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_76.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_76.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_76.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_3455
-- END S6_3455

-- BEGIN S6_3520
namespace S6_3520

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,1,1,1,1,4],[5,5,5,5,5,5],[5,5,5,5,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "f35997558241fabae647c7aeb41376f73b9913b3c9f517928bb54b9cf8703d53"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_76.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_76.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_76.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_76.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_3520
-- END S6_3520

-- BEGIN S6_3663
namespace S6_3663

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,1,1,1,1,2],[5,5,5,5,5,5],[5,5,5,5,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "aee4a119c98c89bca3d049406798a8998552fa866588f1cd87fbb7d41d48b381"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_76.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_76.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_76.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_76.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_3663
-- END S6_3663

-- BEGIN S6_3721
namespace S6_3721

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,1,1,1,1,4],[5,5,5,5,5,5],[5,5,5,5,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ee817299a0703e3174afcadd42e6e02725d019ecf3c793151107ab05ae1c10dc"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_76.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_76.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_76.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_76.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_3721
-- END S6_3721

-- BEGIN S6_3780
namespace S6_3780

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,3],[1,1,1,1,1,4],[5,5,5,5,5,5],[5,5,5,5,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "fe1e6469dd06a8ef2671ba200c2ef6ad03c9ba8fe36a26df3aa513f9bc753a38"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_76.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_76.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_76.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_76.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_3780
-- END S6_3780

-- BEGIN S6_4034
namespace S6_4034

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,1,1],[1,1,1,4,1,3],[4,4,4,1,4,4],[1,1,1,4,5,1],[1,1,3,4,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "6c1a9f5dae8aee141f52b722e0e9109abb16df566086b21afa6a112ed5dcce73"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4034
-- END S6_4034

-- BEGIN S6_4037
namespace S6_4037

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,1,1],[1,1,1,4,1,3],[4,4,4,1,4,4],[1,1,1,4,5,5],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b76328e3fc4d7ad567320accf6fbde609dc10f62e42a1ae98b11ea0515fd90fd"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4037
-- END S6_4037

-- BEGIN S6_4054
namespace S6_4054

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,1,1],[1,1,1,4,3,3],[4,4,4,1,4,4],[1,1,3,4,5,5],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c59132cfcab0a6fd9b024440b46b99df2579cd73cbef635ecaab1bf034114585"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4054
-- END S6_4054

-- BEGIN S6_4063
namespace S6_4063

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,1,2],[1,1,1,4,1,2],[4,4,4,1,4,4],[1,1,1,4,5,1],[1,2,2,4,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b291302cd834803d807ce0831d2d751c3b5c8d0905fb9879cdfe900848a4d2e9"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4063
-- END S6_4063

-- BEGIN S6_4065
namespace S6_4065

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,1,2],[1,1,1,4,1,2],[4,4,4,1,4,4],[1,1,1,4,5,5],[1,2,2,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "fa171d1fffe994851549770c0b5505e885ffc28be006fa0d432e5ef9d076d23e"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4065
-- END S6_4065

-- BEGIN S6_4074
namespace S6_4074

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,1,2],[1,1,1,4,1,3],[4,4,4,1,4,4],[1,1,1,4,5,1],[1,2,3,4,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "42c2284e84fbad71daad3fe2f43e59c5a9835c65d5654afe8b1c4c7f1ae921e5"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4074
-- END S6_4074

-- BEGIN S6_4075
namespace S6_4075

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,1,2],[1,1,1,4,1,3],[4,4,4,1,4,4],[1,1,1,4,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c69c2e002566b1913ca4b3cb69b3cb521979513a5952a03856fcaa6d8020f16c"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4075
-- END S6_4075

-- BEGIN S6_4084
namespace S6_4084

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,1,2],[1,1,1,4,3,1],[4,4,4,1,4,4],[1,1,3,4,5,1],[1,2,1,4,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a3197506bca5eff1ec53499453a4fb62c7cfc4a20beee40e47caf023b8e37e7c"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4084
-- END S6_4084

-- BEGIN S6_4088
namespace S6_4088

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,1,2],[1,1,1,4,3,3],[4,4,4,1,4,4],[1,1,3,4,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "787ff0150990af335e853027b6f11ef0dda47a6068cb57f25681d0093eeba93c"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4088
-- END S6_4088

-- BEGIN S6_4092
namespace S6_4092

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,2,2],[1,1,1,4,2,2],[4,4,4,1,4,4],[1,2,2,4,5,5],[1,2,2,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "f57df7aaa4b853aba2e4e741c757eda559184ba1ca967993fed73e31969e7727"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4092
-- END S6_4092

-- BEGIN S6_4098
namespace S6_4098

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,2,2],[1,1,1,4,2,3],[4,4,4,1,4,4],[1,2,2,4,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cd6ecac75a310fc49db636b2aa417c7f86061c27a77f0367a15c8e9d3a9af7b6"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4098
-- END S6_4098

-- BEGIN S6_4101
namespace S6_4101

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,1],[1,1,1,4,2,2],[1,1,1,4,3,3],[4,4,4,1,4,4],[1,2,3,4,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d5ebdefe7eca455b35eec50a4e76054e9a8d6c758612ebc4e927b5c69eae920d"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4101
-- END S6_4101

-- BEGIN S6_4108
namespace S6_4108

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,6],[1,1,1,4,1,6],[1,1,1,4,3,6],[4,4,4,1,4,6],[1,1,3,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4a37bb4fa7bd3d09f13410e47ccd37bea9f0d8fdbde42c72b1fcb002c10ab0e0"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4108
-- END S6_4108

-- BEGIN S6_4111
namespace S6_4111

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,6],[1,1,1,4,2,6],[1,1,1,4,2,6],[4,4,4,1,4,6],[1,2,2,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ffbd7f114c8f6c27f62d1a64510b6399bc88583c73b0f35edac49ed1d4482e69"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4111
-- END S6_4111

-- BEGIN S6_4113
namespace S6_4113

/-- Exact one-based order-six catalogue table: `[[1,1,1,4,1,6],[1,1,1,4,2,6],[1,1,1,4,3,6],[4,4,4,1,4,6],[1,2,3,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a76ff104a40bc06d6bd8183f28d9ffebd16262654f5c9d1eb1817553cd1b156e"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4113
-- END S6_4113

-- BEGIN S6_4168
namespace S6_4168

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,1,1],[1,1,3,3,1,2],[3,3,1,1,3,3],[3,3,1,1,3,3],[1,1,3,3,5,1],[1,2,3,3,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "1af0722bc72a00e2a1750207d2b6c8567fb78399c9c70cdb0d9d886a3afaf9cb"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4168
-- END S6_4168

-- BEGIN S6_4170
namespace S6_4170

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,1,1],[1,1,3,3,1,2],[3,3,1,1,3,3],[3,3,1,1,3,3],[1,1,3,3,5,5],[1,2,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5ad202d3f50d7b6206adf3e8606594ab1a308dd6fc4bccaae5bbc664e1cd25a0"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4170
-- END S6_4170

-- BEGIN S6_4183
namespace S6_4183

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,1,1],[1,1,3,3,1,2],[3,3,1,1,3,3],[3,3,1,1,3,4],[1,1,3,3,5,1],[1,2,3,4,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cfed1ad4f0c526365850efa8654dff1ad23b4d2ed61be42143fecfef1f5f57d8"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4183
-- END S6_4183

-- BEGIN S6_4184
namespace S6_4184

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,1,1],[1,1,3,3,1,2],[3,3,1,1,3,3],[3,3,1,1,3,4],[1,1,3,3,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "aea253c7f93c3fe445b43775af98a5d40d5f850bc2a9980f862d6f32571a9f67"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4184
-- END S6_4184

-- BEGIN S6_4194
namespace S6_4194

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,1,1],[1,1,3,3,1,2],[3,3,1,1,3,3],[3,3,1,1,4,3],[1,1,3,4,5,1],[1,2,3,3,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "56bb4dd899fdae2908e5747548acde202a4b3a3575a277e9d54e72afe8015795"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4194
-- END S6_4194

-- BEGIN S6_4197
namespace S6_4197

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,1,1],[1,1,3,3,1,2],[3,3,1,1,3,3],[3,3,1,1,4,4],[1,1,3,4,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8267fedc7548c8c2a4e8fb7d948755e84240fc5c74152e473d6c5d01af45cdb3"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4197
-- END S6_4197

-- BEGIN S6_4201
namespace S6_4201

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,1,1],[1,1,3,3,2,2],[3,3,1,1,3,3],[3,3,1,1,3,3],[1,2,3,3,5,5],[1,2,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "997be64cc03d4cabf77cce7373645e9cc08c9c6c5797945159712d9679d92a7f"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4201
-- END S6_4201

-- BEGIN S6_4207
namespace S6_4207

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,1,1],[1,1,3,3,2,2],[3,3,1,1,3,3],[3,3,1,1,3,4],[1,2,3,3,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8b48c97771d56658b4b6c1edebe57df03b850305ab325a9dc1160631b5c9ab3d"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4207
-- END S6_4207

-- BEGIN S6_4209
namespace S6_4209

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,1,1],[1,1,3,3,2,2],[3,3,1,1,3,3],[3,3,1,1,4,4],[1,2,3,4,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4101001f3bf36f14e41007244492ee1f086442e80013ab420fd8130a93924a87"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4209
-- END S6_4209

-- BEGIN S6_4218
namespace S6_4218

/-- Exact one-based order-six catalogue table: `[[1,1,3,3,1,6],[1,1,3,3,2,6],[3,3,1,1,3,6],[3,3,1,1,3,6],[1,2,3,3,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ecdc16aa7828b1c8e2a9a258e49e3144550f940ed851f4b48159c8c1926c74eb"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_28.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_28.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_28.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_4218
-- END S6_4218

end SemigroupBasis.Generated.Order6ExtensionTransfersV3

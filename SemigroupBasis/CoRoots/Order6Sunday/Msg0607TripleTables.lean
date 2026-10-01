import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

/-!
Literal order-six catalogue tables S6_14887, S6_14888, S6_14895
(`research/order6/catalogue.json`, sha256 944f356c…, one-based rows translated
to `Fin 6`), the four-variable candidate basis Σ4

  x = xxx,   xxyzxty = xyxzxty,   xyxxzx = xyzx,

finite soundness of Σ4 on each table (fused kernel checker), and the two
separating submonoids used by the completeness argument: the three-element
left-zero monoid `L21` (identity plus two left zeros) and the four-element
monoid `T2 = {1, g, c₁, c₂}` (g² = 1, cᵢ cⱼ = cⱼ, g cᵢ = cᵢ, cᵢ g = cᵢ'),
each embedded in each table.
-/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleTables

open SemigroupBasis

/-- `x = xxx`. -/
def cubeLaw : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

/-- `xxyzxty = xyxzxty` (x = 0, y = 1, z = 2, t = 3). -/
def swapLaw : Identity Nat := ⟨⟨0, [0, 1, 2, 0, 3, 1]⟩, ⟨0, [1, 0, 2, 0, 3, 1]⟩⟩

/-- `xyxxzx = xyzx`. -/
def deleteLaw : Identity Nat := ⟨⟨0, [1, 0, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

/-- The candidate basis Σ4. -/
def basis : List (Identity Nat) := [cubeLaw, swapLaw, deleteLaw]

private def toFin1 : Nat → Fin 1
  | _ => 0

private def toFin3 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin4 : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

/-! ## The separating monoids -/

namespace L21

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then (if b = 0 then (0 : Fin 3) else if b = 1 then (1 : Fin 3) else (2 : Fin 3))
  else if a = 1 then (if b = 0 then (1 : Fin 3) else if b = 1 then (1 : Fin 3) else (1 : Fin 3))
  else if b = 0 then (2 : Fin 3) else if b = 1 then (2 : Fin 3) else (2 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end L21

namespace T2

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then (if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4))
  else if a = 1 then (if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4))
  else if a = 2 then (if b = 0 then (2 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4))
  else if b = 0 then (3 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end T2

/-! ## The three catalogue tables -/

namespace S6_14887

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6))
  else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6))
  else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6))
  else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6))
  else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6))
  else if b = 0 then (5 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem cubeValid : cubeLaw.SatisfiedBy table.semigroup := by
  have roundTrip : (cubeLaw.map toFin1).map Fin.val = cubeLaw := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (cubeLaw.map toFin1) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem swapValid : swapLaw.SatisfiedBy table.semigroup := by
  have roundTrip : (swapLaw.map toFin4).map Fin.val = swapLaw := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (swapLaw.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem deleteValid : deleteLaw.SatisfiedBy table.semigroup := by
  have roundTrip : (deleteLaw.map toFin3).map Fin.val = deleteLaw := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (deleteLaw.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem tableModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact cubeValid
  · exact swapValid
  · exact deleteValid

theorem oppositeModels : Models table.semigroup.opposite (reversedBasis basis) :=
  tableModels.oppositeReversed

/-- `L21 = {1, 3, 4}` (one-based) inside the table. -/
def leftZeroEmbedding : Embedding L21.table.semigroup table.semigroup where
  toFun := fun a => (if a.val = 0 then 0 else if a.val = 1 then 2 else 3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    revert a b
    decide

/-- `T2 = {1, 2, 5, 6}` (one-based) inside the table. -/
def transformationEmbedding : Embedding T2.table.semigroup table.semigroup where
  toFun := fun a => (if a.val = 0 then 0 else if a.val = 1 then 1 else if a.val = 2 then 4 else 5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    revert a b
    decide

end S6_14887

namespace S6_14888

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6))
  else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6))
  else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6))
  else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6))
  else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6))
  else if b = 0 then (5 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem cubeValid : cubeLaw.SatisfiedBy table.semigroup := by
  have roundTrip : (cubeLaw.map toFin1).map Fin.val = cubeLaw := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (cubeLaw.map toFin1) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem swapValid : swapLaw.SatisfiedBy table.semigroup := by
  have roundTrip : (swapLaw.map toFin4).map Fin.val = swapLaw := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (swapLaw.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem deleteValid : deleteLaw.SatisfiedBy table.semigroup := by
  have roundTrip : (deleteLaw.map toFin3).map Fin.val = deleteLaw := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (deleteLaw.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem tableModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact cubeValid
  · exact swapValid
  · exact deleteValid

theorem oppositeModels : Models table.semigroup.opposite (reversedBasis basis) :=
  tableModels.oppositeReversed

/-- `L21 = {1, 3, 4}` (one-based) inside the table. -/
def leftZeroEmbedding : Embedding L21.table.semigroup table.semigroup where
  toFun := fun a => (if a.val = 0 then 0 else if a.val = 1 then 2 else 3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    revert a b
    decide

/-- `T2 = {1, 2, 5, 6}` (one-based) inside the table. -/
def transformationEmbedding : Embedding T2.table.semigroup table.semigroup where
  toFun := fun a => (if a.val = 0 then 0 else if a.val = 1 then 1 else if a.val = 2 then 4 else 5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    revert a b
    decide

end S6_14888

namespace S6_14895

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6))
  else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6))
  else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6))
  else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6))
  else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6))
  else if b = 0 then (5 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem cubeValid : cubeLaw.SatisfiedBy table.semigroup := by
  have roundTrip : (cubeLaw.map toFin1).map Fin.val = cubeLaw := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (cubeLaw.map toFin1) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem swapValid : swapLaw.SatisfiedBy table.semigroup := by
  have roundTrip : (swapLaw.map toFin4).map Fin.val = swapLaw := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (swapLaw.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem deleteValid : deleteLaw.SatisfiedBy table.semigroup := by
  have roundTrip : (deleteLaw.map toFin3).map Fin.val = deleteLaw := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (deleteLaw.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem tableModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact cubeValid
  · exact swapValid
  · exact deleteValid

theorem oppositeModels : Models table.semigroup.opposite (reversedBasis basis) :=
  tableModels.oppositeReversed

/-- `L21 = {1, 3, 5}` (one-based) inside the table. -/
def leftZeroEmbedding : Embedding L21.table.semigroup table.semigroup where
  toFun := fun a => (if a.val = 0 then 0 else if a.val = 1 then 2 else 4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    revert a b
    decide

/-- `T2 = {1, 2, 5, 6}` (one-based) inside the table. -/
def transformationEmbedding : Embedding T2.table.semigroup table.semigroup where
  toFun := fun a => (if a.val = 0 then 0 else if a.val = 1 then 1 else if a.val = 2 then 4 else 5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    revert a b
    decide

end S6_14895

end SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleTables

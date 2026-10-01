import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9638Completeness
import SemigroupBasis.TransferPower

/-! Three exact e122 endpoints reuse the completed S9638 seed. The seed
embeds in the square of each target; the exact original six-law list is
recovered by explicit derivations in both directions, not by a finite bound. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9638Derivations
  (basis derivesHeadReturn derivesMiddleDuplication derivesLastDuplication)

abbrev seedTable : FiniteTable :=
  SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638FourObservations.table (0 : Fin 4)

private def row (v0 v1 v2 v3 v4 v5 : Fin 6) (b : Fin 6) : Fin 6 :=
  if b = 0 then v0 else if b = 1 then v1 else if b = 2 then v2
  else if b = 3 then v3 else if b = 4 then v4 else v5

def mul5551 (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 0
  else if a = 2 then row 0 0 0 0 0 2 b
  else if a = 3 then row 0 0 0 1 0 0 b
  else if a = 4 then 4 else row 0 0 0 0 4 5 b

def mul5561 (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 0
  else if a = 2 then row 0 0 0 0 0 2 b
  else if a = 3 then row 0 0 0 1 0 2 b
  else if a = 4 then 4 else row 0 0 0 0 4 5 b

def mul9545 (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 0
  else if a = 2 then row 0 0 1 0 0 0 b
  else if a = 3 then 3
  else if a = 4 then row 3 3 3 3 3 4 b else row 0 0 0 3 3 5 b

def mul (family : Fin 3) : Fin 6 → Fin 6 → Fin 6 :=
  if family = 0 then mul5551 else if family = 1 then mul5561 else mul9545

theorem associative : ∀ (family : Fin 3) (a b c : Fin 6),
    mul family (mul family a b) c = mul family a (mul family b c) := by
  intro family
  refine Fin.cases (by decide) (fun rest => ?_) family
  refine Fin.cases (by decide) (fun last => ?_) rest
  exact Fin.cases (by decide) (fun empty => Fin.elim0 empty) last

def table (family : Fin 3) : FiniteTable where
  order := 6
  mul := mul family
  assoc := associative family

theorem four_laws : ∀ (family : Fin 3) (a b c : Fin 6),
    mul family (mul family a b) a = mul family (mul family a a) b ∧
    mul family (mul family a b) c = mul family (mul family (mul family a b) b) c ∧
    mul family (mul family a b) c = mul family (mul family (mul family a b) c) c ∧
    mul family (mul family (mul family a b) c) b = mul family (mul family a b) c := by
  intro family
  refine Fin.cases (by decide) (fun rest => ?_) family
  refine Fin.cases (by decide) (fun last => ?_) rest
  exact Fin.cases (by decide) (fun empty => Fin.elim0 empty) last

theorem modelsSeed (family : Fin 3) : Models (table family).semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · intro valuation
    change mul family (mul family (valuation 0) (valuation 1)) (valuation 0) =
      mul family (mul family (valuation 0) (valuation 0)) (valuation 1)
    exact (four_laws family (valuation 0) (valuation 1) (valuation 2)).1
  · intro valuation
    change mul family (mul family (valuation 0) (valuation 1)) (valuation 2) =
      mul family (mul family (mul family (valuation 0) (valuation 1)) (valuation 1))
        (valuation 2)
    exact (four_laws family (valuation 0) (valuation 1) (valuation 2)).2.1
  · intro valuation
    change mul family (mul family (valuation 0) (valuation 1)) (valuation 2) =
      mul family (mul family (mul family (valuation 0) (valuation 1)) (valuation 2))
        (valuation 2)
    exact (four_laws family (valuation 0) (valuation 1) (valuation 2)).2.2.1
  · intro valuation
    change mul family (mul family (mul family (valuation 0) (valuation 1)) (valuation 2))
        (valuation 1) = mul family (mul family (valuation 0) (valuation 1)) (valuation 2)
    exact (four_laws family (valuation 0) (valuation 1) (valuation 2)).2.2.2

def coordinateMap (family : Fin 3) (coordinate : Fin 2) (value : Fin 6) : Fin 6 :=
  if family = 2 then
    if coordinate = 0 then row 5 5 5 3 4 0 value else row 0 1 2 0 0 0 value
  else
    if coordinate = 0 then row 5 5 5 0 2 4 value else row 0 1 3 0 0 0 value

theorem coordinate_map_mul : ∀ (family : Fin 3) (coordinate : Fin 2) (a b : Fin 6),
    coordinateMap family coordinate (seedTable.mul a b) =
      mul family (coordinateMap family coordinate a) (coordinateMap family coordinate b) := by
  intro family
  refine Fin.cases (by decide) (fun rest => ?_) family
  refine Fin.cases (by decide) (fun last => ?_) rest
  exact Fin.cases (by decide) (fun empty => Fin.elim0 empty) last

def coordinateHom (family : Fin 3) (coordinate : Fin 2) :
    Hom seedTable.semigroup (table family).semigroup where
  toFun := coordinateMap family coordinate
  map_mul := coordinate_map_mul family coordinate

theorem jointly_injective : ∀ (family : Fin 3) (a b : Fin 6),
    coordinateMap family 0 a = coordinateMap family 0 b →
    coordinateMap family 1 a = coordinateMap family 1 b → a = b := by
  intro family
  refine Fin.cases (by decide) (fun rest => ?_) family
  refine Fin.cases (by decide) (fun last => ?_) rest
  exact Fin.cases (by decide) (fun empty => Fin.elim0 empty) last

def seedIntoSquare (family : Fin 3) :
    Embedding seedTable.semigroup ((table family).semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms (coordinateHom family) (by
    intro a b same
    exact jointly_injective family a b (same 0) (same 1))

theorem seed_basis (family : Fin 3) : BasisFor (table family).semigroup basis := by
  have seed : BasisFor seedTable.semigroup basis :=
    SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9638Completeness.representative_basis
  exact seed.inheritAlongPowerEmbedding (seedIntoSquare family) (modelsSeed family)

def displayed : List (Identity Nat) :=
  [⟨⟨0, [0,0]⟩, ⟨0, [0,0,0]⟩⟩,
   ⟨⟨0, [0,0,1]⟩, ⟨0, [0,1]⟩⟩,
   ⟨⟨0, [0,1]⟩, ⟨0, [0,1,1]⟩⟩,
   ⟨⟨0, [0,1]⟩, ⟨0, [1,0]⟩⟩,
   ⟨⟨0, [1,1]⟩, ⟨0, [1,1,1]⟩⟩,
   ⟨⟨0, [1,1,2]⟩, ⟨0, [1,2]⟩⟩]

theorem displayedInSeed (identity : Identity Nat) (member : identity ∈ displayed) :
    Derives basis identity.lhs identity.rhs := by
  simp only [displayed, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact derivesLastDuplication (Word.singleton 0) (Word.singleton 0) (Word.singleton 0)
  · exact (derivesMiddleDuplication (Word.singleton 0) (Word.singleton 0) (Word.singleton 1)).symm
  · exact derivesLastDuplication (Word.singleton 0) (Word.singleton 0) (Word.singleton 1)
  · exact (derivesHeadReturn (Word.singleton 0) (Word.singleton 1)).symm
  · exact derivesLastDuplication (Word.singleton 0) (Word.singleton 1) (Word.singleton 1)
  · exact (derivesMiddleDuplication (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)).symm

theorem seedInDisplayed (identity : Identity Nat) (member : identity ∈ basis) :
    Derives displayed identity.lhs identity.rhs := by
  have doubleLast : Derives displayed (Word.mk 0 [0,1]) (Word.mk 0 [0,1,1]) :=
    Derives.fromBasis (e := ⟨⟨0,[0,1]⟩,⟨0,[0,1,1]⟩⟩) (by decide)
  have headReturn : Derives displayed (Word.mk 0 [0,1]) (Word.mk 0 [1,0]) :=
    Derives.fromBasis (e := ⟨⟨0,[0,1]⟩,⟨0,[1,0]⟩⟩) (by decide)
  have middleDelete : Derives displayed (Word.mk 0 [1,1,2]) (Word.mk 0 [1,2]) :=
    Derives.fromBasis (e := ⟨⟨0,[1,1,2]⟩,⟨0,[1,2]⟩⟩) (by decide)
  let renameVars : Nat → Word Nat := fun n => if n = 0 then Word.singleton 1 else Word.singleton 2
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact headReturn.symm
  · exact middleDelete.symm
  · have middle : Derives displayed (Word.mk 1 [1,2]) (Word.mk 1 [1,2,2]) :=
      Derives.subst doubleLast renameVars
    have second : Derives displayed (Word.mk 0 [1,1,2]) (Word.mk 0 [1,1,2,2]) :=
      middle.prepend (Word.singleton 0)
    let doubled : Nat → Word Nat := fun n =>
      if n = 0 then Word.singleton 0 else if n = 1 then Word.singleton 1 else Word.mk 2 [2]
    have third : Derives displayed (Word.mk 0 [1,1,2,2]) (Word.mk 0 [1,2,2]) :=
      Derives.subst middleDelete doubled
    exact middleDelete.symm.trans (second.trans third)
  · have middle : Derives displayed (Word.mk 1 [2,1]) (Word.mk 1 [1,2]) :=
      Derives.subst headReturn.symm renameVars
    have first : Derives displayed (Word.mk 0 [1,2,1]) (Word.mk 0 [1,1,2]) :=
      middle.prepend (Word.singleton 0)
    exact first.trans middleDelete

theorem modelsDisplayed (family : Fin 3) : Models (table family).semigroup displayed := by
  intro identity member valuation
  exact Derives.sound (modelsSeed family) (displayedInSeed identity member) valuation

theorem displayed_basis (family : Fin 3) : BasisFor (table family).semigroup displayed :=
  (seed_basis family).replace (modelsDisplayed family) seedInDisplayed

namespace S6_5551
abbrev table : FiniteTable := Msg0524E122FamilyTransfer.table (0 : Fin 3)
theorem representative_basis : BasisFor table.semigroup displayed := displayed_basis 0
theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis displayed) :=
  representative_basis.oppositeReversed
end S6_5551

namespace S6_5561
abbrev table : FiniteTable := Msg0524E122FamilyTransfer.table (1 : Fin 3)
theorem representative_basis : BasisFor table.semigroup displayed := displayed_basis 1
theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis displayed) :=
  representative_basis.oppositeReversed
end S6_5561

namespace S6_9545
abbrev table : FiniteTable := Msg0524E122FamilyTransfer.table (2 : Fin 3)
theorem representative_basis : BasisFor table.semigroup displayed := displayed_basis 2
theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis displayed) :=
  representative_basis.oppositeReversed
end S6_9545

example : ∀ family : Fin 3, Embedding seedTable.semigroup ((table family).semigroup.pi (Fin 2)) :=
  seedIntoSquare
example : ∀ family : Fin 3, BasisFor (table family).semigroup displayed := displayed_basis
example : BasisFor S6_5551.table.semigroup displayed := S6_5551.representative_basis
example : BasisFor S6_5551.table.semigroup.opposite (reversedBasis displayed) := S6_5551.opposite_basis
example : BasisFor S6_5561.table.semigroup displayed := S6_5561.representative_basis
example : BasisFor S6_5561.table.semigroup.opposite (reversedBasis displayed) := S6_5561.opposite_basis
example : BasisFor S6_9545.table.semigroup displayed := S6_9545.representative_basis
example : BasisFor S6_9545.table.semigroup.opposite (reversedBasis displayed) := S6_9545.opposite_basis

#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.associative
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.four_laws
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.modelsSeed
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.coordinate_map_mul
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.jointly_injective
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.seedIntoSquare
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.seed_basis
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.displayedInSeed
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.seedInDisplayed
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.modelsDisplayed
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.displayed_basis
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.S6_5551.representative_basis
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.S6_5551.opposite_basis
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.S6_5561.representative_basis
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.S6_5561.opposite_basis
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.S6_9545.representative_basis
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer.S6_9545.opposite_basis

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524E122FamilyTransfer

import SemigroupBasis.CoRoots.Order6SporadicSection25Basis
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Order6Subdirect.Common
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

private def affineTable : FiniteTable := Order6Subdirect.oppositeTable Generated.Catalogue.S4_96.table

private def toFin1 : Nat → Fin 1
  | _ => 0

private def toFin2 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin3 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin4 : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private def toFin5 : Nat → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 4

theorem law00_affine_valid : law00.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law00.map toFin1).map Fin.val = law00 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law00.map toFin1) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law00_component_valid : law00.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law00.map toFin1).map Fin.val = law00 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law00.map toFin1) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law01_affine_valid : law01.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law01.map toFin2).map Fin.val = law01 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law01.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law01_component_valid : law01.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law01.map toFin2).map Fin.val = law01 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law01.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law02_affine_valid : law02.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law02.map toFin2).map Fin.val = law02 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law02.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law02_component_valid : law02.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law02.map toFin2).map Fin.val = law02 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law02.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law03_affine_valid : law03.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law03.map toFin3).map Fin.val = law03 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law03.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law03_component_valid : law03.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law03.map toFin3).map Fin.val = law03 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law03.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law04_affine_valid : law04.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law04.map toFin2).map Fin.val = law04 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law04.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law04_component_valid : law04.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law04.map toFin2).map Fin.val = law04 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law04.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law05_affine_valid : law05.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law05.map toFin3).map Fin.val = law05 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law05.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law05_component_valid : law05.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law05.map toFin3).map Fin.val = law05 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law05.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law06_affine_valid : law06.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law06.map toFin3).map Fin.val = law06 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law06.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law06_component_valid : law06.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law06.map toFin3).map Fin.val = law06 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law06.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law07_affine_valid : law07.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law07.map toFin4).map Fin.val = law07 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law07.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law07_component_valid : law07.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law07.map toFin4).map Fin.val = law07 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law07.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law08_affine_valid : law08.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law08.map toFin3).map Fin.val = law08 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law08.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law08_component_valid : law08.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law08.map toFin3).map Fin.val = law08 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law08.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law09_affine_valid : law09.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law09.map toFin4).map Fin.val = law09 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law09.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law09_component_valid : law09.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law09.map toFin4).map Fin.val = law09 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law09.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law10_affine_valid : law10.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law10.map toFin4).map Fin.val = law10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law10.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law10_component_valid : law10.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law10.map toFin4).map Fin.val = law10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law10.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law11_affine_valid : law11.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law11.map toFin5).map Fin.val = law11 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law11.map toFin5) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law11_component_valid : law11.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law11.map toFin5).map Fin.val = law11 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law11.map toFin5) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law12_affine_valid : law12.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law12.map toFin2).map Fin.val = law12 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law12.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law12_component_valid : law12.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law12.map toFin2).map Fin.val = law12 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law12.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law13_affine_valid : law13.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law13.map toFin3).map Fin.val = law13 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law13.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law13_component_valid : law13.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law13.map toFin3).map Fin.val = law13 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law13.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law14_affine_valid : law14.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law14.map toFin3).map Fin.val = law14 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law14.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law14_component_valid : law14.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law14.map toFin3).map Fin.val = law14 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law14.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law15_affine_valid : law15.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law15.map toFin4).map Fin.val = law15 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law15.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law15_component_valid : law15.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law15.map toFin4).map Fin.val = law15 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law15.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law16_affine_valid : law16.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law16.map toFin3).map Fin.val = law16 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law16.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law16_component_valid : law16.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law16.map toFin3).map Fin.val = law16 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law16.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law17_affine_valid : law17.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law17.map toFin4).map Fin.val = law17 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law17.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law17_component_valid : law17.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law17.map toFin4).map Fin.val = law17 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law17.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law18_affine_valid : law18.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law18.map toFin4).map Fin.val = law18 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law18.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law18_component_valid : law18.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law18.map toFin4).map Fin.val = law18 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law18.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law19_affine_valid : law19.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law19.map toFin5).map Fin.val = law19 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law19.map toFin5) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law19_component_valid : law19.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law19.map toFin5).map Fin.val = law19 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law19.map toFin5) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law20_affine_valid : law20.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law20.map toFin2).map Fin.val = law20 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law20.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law20_component_valid : law20.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law20.map toFin2).map Fin.val = law20 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law20.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law21_affine_valid : law21.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law21.map toFin3).map Fin.val = law21 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law21.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law21_component_valid : law21.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law21.map toFin3).map Fin.val = law21 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law21.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law22_affine_valid : law22.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law22.map toFin3).map Fin.val = law22 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law22.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law22_component_valid : law22.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law22.map toFin3).map Fin.val = law22 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law22.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law23_affine_valid : law23.SatisfiedBy affineTable.semigroup := by
  have roundTrip : (law23.map toFin4).map Fin.val = law23 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound affineTable (law23.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law23_component_valid : law23.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup := by
  have roundTrip : (law23.map toFin4).map Fin.val = law23 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_70.table (law23.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem core_models_affine : Models Generated.Catalogue.S4_96.table.semigroup.opposite (basis false) := by
  intro identity member
  change identity ∈ coreBasis at member
  simp only [coreBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact law00_affine_valid
  · exact law01_affine_valid
  · exact law02_affine_valid
  · exact law03_affine_valid
  · exact law04_affine_valid
  · exact law05_affine_valid
  · exact law06_affine_valid
  · exact law07_affine_valid
  · exact law08_affine_valid
  · exact law09_affine_valid
  · exact law10_affine_valid
  · exact law11_affine_valid
  · exact law12_affine_valid
  · exact law13_affine_valid
  · exact law14_affine_valid
  · exact law15_affine_valid
  · exact law16_affine_valid
  · exact law17_affine_valid
  · exact law18_affine_valid
  · exact law19_affine_valid
  · exact law20_affine_valid
  · exact law21_affine_valid
  · exact law22_affine_valid
  · exact law23_affine_valid

theorem core_models_component : Models Generated.Catalogue.S4_70.table.semigroup (basis false) := by
  intro identity member
  change identity ∈ coreBasis at member
  simp only [coreBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact law00_component_valid
  · exact law01_component_valid
  · exact law02_component_valid
  · exact law03_component_valid
  · exact law04_component_valid
  · exact law05_component_valid
  · exact law06_component_valid
  · exact law07_component_valid
  · exact law08_component_valid
  · exact law09_component_valid
  · exact law10_component_valid
  · exact law11_component_valid
  · exact law12_component_valid
  · exact law13_component_valid
  · exact law14_component_valid
  · exact law15_component_valid
  · exact law16_component_valid
  · exact law17_component_valid
  · exact law18_component_valid
  · exact law19_component_valid
  · exact law20_component_valid
  · exact law21_component_valid
  · exact law22_component_valid
  · exact law23_component_valid

def frozenF4FinBasis : List (Identity (Fin 5)) :=
[   -- 25.2a[-]: xxxx = xx
   ⟨⟨0, [0, 0, 0]⟩, ⟨0, [0]⟩⟩,
   -- 25.2a[k]: xxxkx = xkx
   ⟨⟨0, [0, 0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩,
   -- 25.2a[h]: xhxxx = xhx
   ⟨⟨0, [1, 0, 0, 0]⟩, ⟨0, [1, 0]⟩⟩,
   -- 25.2a[hk]: xhxxkx = xhkx
   ⟨⟨0, [1, 0, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩,
   -- 25.2b[-]: xyyyx = xyx
   ⟨⟨0, [1, 1, 1, 0]⟩, ⟨0, [1, 0]⟩⟩,
   -- 25.2b[t]: xyyytx = xytx
   ⟨⟨0, [1, 1, 1, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩,
   -- 25.2b[k]: xykyyx = xykx
   ⟨⟨0, [1, 2, 1, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩,
   -- 25.2b[kt]: xykyytx = xyktx
   ⟨⟨0, [1, 2, 1, 1, 3, 0]⟩, ⟨0, [1, 2, 3, 0]⟩⟩,
   -- 25.2b[h]: xhyyyx = xhyx
   ⟨⟨0, [1, 2, 2, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩,
   -- 25.2b[ht]: xhyyytx = xhytx
   ⟨⟨0, [1, 2, 2, 2, 3, 0]⟩, ⟨0, [1, 2, 3, 0]⟩⟩,
   -- 25.2b[hk]: xhykyyx = xhykx
   ⟨⟨0, [1, 2, 3, 2, 2, 0]⟩, ⟨0, [1, 2, 3, 0]⟩⟩,
   -- 25.2b[hkt]: xhykyytx = xhyktx
   ⟨⟨0, [1, 2, 3, 2, 2, 4, 0]⟩, ⟨0, [1, 2, 3, 4, 0]⟩⟩,
   -- 25.2c[-]: xyxxy = xyyxx
   ⟨⟨0, [1, 0, 0, 1]⟩, ⟨0, [1, 1, 0, 0]⟩⟩,
   -- 25.2c[t]: xyxxty = xytyxx
   ⟨⟨0, [1, 0, 0, 2, 1]⟩, ⟨0, [1, 2, 1, 0, 0]⟩⟩,
   -- 25.2c[k]: xykxxy = xykyxx
   ⟨⟨0, [1, 2, 0, 0, 1]⟩, ⟨0, [1, 2, 1, 0, 0]⟩⟩,
   -- 25.2c[kt]: xykxxty = xyktyxx
   ⟨⟨0, [1, 2, 0, 0, 3, 1]⟩, ⟨0, [1, 2, 3, 1, 0, 0]⟩⟩,
   -- 25.2c[h]: xhyxxy = xhyyxx
   ⟨⟨0, [1, 2, 0, 0, 2]⟩, ⟨0, [1, 2, 2, 0, 0]⟩⟩,
   -- 25.2c[ht]: xhyxxty = xhytyxx
   ⟨⟨0, [1, 2, 0, 0, 3, 2]⟩, ⟨0, [1, 2, 3, 2, 0, 0]⟩⟩,
   -- 25.2c[hk]: xhykxxy = xhykyxx
   ⟨⟨0, [1, 2, 3, 0, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0, 0]⟩⟩,
   -- 25.2c[hkt]: xhykxxty = xhyktyxx
   ⟨⟨0, [1, 2, 3, 0, 0, 4, 2]⟩, ⟨0, [1, 2, 3, 4, 2, 0, 0]⟩⟩,
   -- 25.2d[-]: xyxy = xyyx
   ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩,
   -- 25.2d[k]: xykxy = xykyx
   ⟨⟨0, [1, 2, 0, 1]⟩, ⟨0, [1, 2, 1, 0]⟩⟩,
   -- 25.2d[h]: xhyxy = xhyyx
   ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩,
   -- 25.2d[hk]: xhykxy = xhykyx
   ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩]

theorem basis_false_eq_frozen_fin_data :
  basis false = frozenF4FinBasis.map (Identity.map Fin.val) := by decide

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law00_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law00_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law01_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law01_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law02_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law02_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law03_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law03_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law04_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law04_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law05_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law05_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law06_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law06_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law07_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law07_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law08_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law08_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law09_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law09_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law10_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law10_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law11_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law11_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law12_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law12_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law13_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law13_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law14_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law14_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law15_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law15_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law16_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law16_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law17_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law17_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law18_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law18_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law19_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law19_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law20_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law20_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law21_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law21_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law22_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law22_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law23_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law23_component_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.core_models_affine
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.core_models_component
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.basis_false_eq_frozen_fin_data

end SemigroupBasis.CoRoots.Order6SporadicSection25

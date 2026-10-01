import SemigroupBasis.CoRoots.Order6SporadicSection25F3AffineModel

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

private def f3ToFin1 : Nat → Fin 1
  | _ => 0

private def f3ToFin2 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def f3ToFin3 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def f3ToFin4 : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private def f3ToFin5 : Nat → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 4

theorem law00_separator_valid : law00.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law00.map f3ToFin1).map Fin.val = law00 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law00.map f3ToFin1) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law01_separator_valid : law01.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law01.map f3ToFin2).map Fin.val = law01 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law01.map f3ToFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law02_separator_valid : law02.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law02.map f3ToFin2).map Fin.val = law02 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law02.map f3ToFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law03_separator_valid : law03.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law03.map f3ToFin3).map Fin.val = law03 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law03.map f3ToFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law04_separator_valid : law04.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law04.map f3ToFin2).map Fin.val = law04 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law04.map f3ToFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law05_separator_valid : law05.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law05.map f3ToFin3).map Fin.val = law05 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law05.map f3ToFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law06_separator_valid : law06.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law06.map f3ToFin3).map Fin.val = law06 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law06.map f3ToFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law07_separator_valid : law07.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law07.map f3ToFin4).map Fin.val = law07 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law07.map f3ToFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law08_separator_valid : law08.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law08.map f3ToFin3).map Fin.val = law08 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law08.map f3ToFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law09_separator_valid : law09.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law09.map f3ToFin4).map Fin.val = law09 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law09.map f3ToFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law10_separator_valid : law10.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law10.map f3ToFin4).map Fin.val = law10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law10.map f3ToFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law11_separator_valid : law11.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law11.map f3ToFin5).map Fin.val = law11 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law11.map f3ToFin5) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law12_separator_valid : law12.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law12.map f3ToFin2).map Fin.val = law12 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law12.map f3ToFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law13_separator_valid : law13.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law13.map f3ToFin3).map Fin.val = law13 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law13.map f3ToFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law14_separator_valid : law14.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law14.map f3ToFin3).map Fin.val = law14 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law14.map f3ToFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law15_separator_valid : law15.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law15.map f3ToFin4).map Fin.val = law15 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law15.map f3ToFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law16_separator_valid : law16.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law16.map f3ToFin3).map Fin.val = law16 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law16.map f3ToFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law17_separator_valid : law17.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law17.map f3ToFin4).map Fin.val = law17 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law17.map f3ToFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law18_separator_valid : law18.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law18.map f3ToFin4).map Fin.val = law18 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law18.map f3ToFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law19_separator_valid : law19.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law19.map f3ToFin5).map Fin.val = law19 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law19.map f3ToFin5) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law20_separator_valid : law20.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law20.map f3ToFin2).map Fin.val = law20 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law20.map f3ToFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law21_separator_valid : law21.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law21.map f3ToFin3).map Fin.val = law21 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law21.map f3ToFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law22_separator_valid : law22.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law22.map f3ToFin3).map Fin.val = law22 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law22.map f3ToFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law23_separator_valid : law23.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law23.map f3ToFin4).map Fin.val = law23 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law23.map f3ToFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law24_separator_valid : law24.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup := by
  have roundTrip : (law24.map f3ToFin2).map Fin.val = law24 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound Generated.Catalogue.S4_69.table (law24.map f3ToFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem basis_true_models_separator : Models Generated.Catalogue.S4_69.table.semigroup (basis true) := by
  intro identity member
  change identity ∈ [law00,law01,law02,law03,law04,law05,law06,law07,law08,law09,law10,law11,law12,law13,law14,law15,law16,law17,law18,law19,law20,law21,law22,law23,law24] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact law00_separator_valid
  · exact law01_separator_valid
  · exact law02_separator_valid
  · exact law03_separator_valid
  · exact law04_separator_valid
  · exact law05_separator_valid
  · exact law06_separator_valid
  · exact law07_separator_valid
  · exact law08_separator_valid
  · exact law09_separator_valid
  · exact law10_separator_valid
  · exact law11_separator_valid
  · exact law12_separator_valid
  · exact law13_separator_valid
  · exact law14_separator_valid
  · exact law15_separator_valid
  · exact law16_separator_valid
  · exact law17_separator_valid
  · exact law18_separator_valid
  · exact law19_separator_valid
  · exact law20_separator_valid
  · exact law21_separator_valid
  · exact law22_separator_valid
  · exact law23_separator_valid
  · exact law24_separator_valid

def frozenF3FinBasis : List (Identity (Fin 5)) :=
[   -- 25.4a[-]: xxxx = xx
   ⟨⟨0, [0, 0, 0]⟩, ⟨0, [0]⟩⟩,
   -- 25.4a[k]: xxxkx = xkx
   ⟨⟨0, [0, 0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩,
   -- 25.4a[h]: xhxxx = xhx
   ⟨⟨0, [1, 0, 0, 0]⟩, ⟨0, [1, 0]⟩⟩,
   -- 25.4a[hk]: xhxxkx = xhkx
   ⟨⟨0, [1, 0, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩,
   -- 25.4b[-]: xyyyx = xyx
   ⟨⟨0, [1, 1, 1, 0]⟩, ⟨0, [1, 0]⟩⟩,
   -- 25.4b[t]: xyyytx = xytx
   ⟨⟨0, [1, 1, 1, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩,
   -- 25.4b[k]: xykyyx = xykx
   ⟨⟨0, [1, 2, 1, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩,
   -- 25.4b[kt]: xykyytx = xyktx
   ⟨⟨0, [1, 2, 1, 1, 3, 0]⟩, ⟨0, [1, 2, 3, 0]⟩⟩,
   -- 25.4b[h]: xhyyyx = xhyx
   ⟨⟨0, [1, 2, 2, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩,
   -- 25.4b[ht]: xhyyytx = xhytx
   ⟨⟨0, [1, 2, 2, 2, 3, 0]⟩, ⟨0, [1, 2, 3, 0]⟩⟩,
   -- 25.4b[hk]: xhykyyx = xhykx
   ⟨⟨0, [1, 2, 3, 2, 2, 0]⟩, ⟨0, [1, 2, 3, 0]⟩⟩,
   -- 25.4b[hkt]: xhykyytx = xhyktx
   ⟨⟨0, [1, 2, 3, 2, 2, 4, 0]⟩, ⟨0, [1, 2, 3, 4, 0]⟩⟩,
   -- 25.4c[-]: xyxxy = xyyxx
   ⟨⟨0, [1, 0, 0, 1]⟩, ⟨0, [1, 1, 0, 0]⟩⟩,
   -- 25.4c[t]: xyxxty = xytyxx
   ⟨⟨0, [1, 0, 0, 2, 1]⟩, ⟨0, [1, 2, 1, 0, 0]⟩⟩,
   -- 25.4c[k]: xykxxy = xykyxx
   ⟨⟨0, [1, 2, 0, 0, 1]⟩, ⟨0, [1, 2, 1, 0, 0]⟩⟩,
   -- 25.4c[kt]: xykxxty = xyktyxx
   ⟨⟨0, [1, 2, 0, 0, 3, 1]⟩, ⟨0, [1, 2, 3, 1, 0, 0]⟩⟩,
   -- 25.4c[h]: xhyxxy = xhyyxx
   ⟨⟨0, [1, 2, 0, 0, 2]⟩, ⟨0, [1, 2, 2, 0, 0]⟩⟩,
   -- 25.4c[ht]: xhyxxty = xhytyxx
   ⟨⟨0, [1, 2, 0, 0, 3, 2]⟩, ⟨0, [1, 2, 3, 2, 0, 0]⟩⟩,
   -- 25.4c[hk]: xhykxxy = xhykyxx
   ⟨⟨0, [1, 2, 3, 0, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0, 0]⟩⟩,
   -- 25.4c[hkt]: xhykxxty = xhyktyxx
   ⟨⟨0, [1, 2, 3, 0, 0, 4, 2]⟩, ⟨0, [1, 2, 3, 4, 2, 0, 0]⟩⟩,
   -- 25.4d[-]: xyxy = xyyx
   ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩,
   -- 25.4d[k]: xykxy = xykyx
   ⟨⟨0, [1, 2, 0, 1]⟩, ⟨0, [1, 2, 1, 0]⟩⟩,
   -- 25.4d[h]: xhyxy = xhyyx
   ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩,
   -- 25.4d[hk]: xhykxy = xhykyx
   ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩,
   -- 25.4e: xxyyxxyy = xxyy
   ⟨⟨0, [0, 1, 1, 0, 0, 1, 1]⟩, ⟨0, [0, 1, 1]⟩⟩]

theorem basis_true_eq_frozen_fin_data :
  basis true = frozenF3FinBasis.map (Identity.map Fin.val) := by decide

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law00_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law01_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law02_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law03_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law04_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law05_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law06_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law07_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law08_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law09_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law10_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law11_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law12_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law13_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law14_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law15_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law16_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law17_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law18_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law19_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law20_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law21_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law22_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law23_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law24_separator_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.basis_true_models_separator
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.basis_true_eq_frozen_fin_data

end SemigroupBasis.CoRoots.Order6SporadicSection25

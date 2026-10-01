import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

/-! Exact msg0514 finite16-law table witnesses for6432/6439. No unrestricted
reach, separation, completeness, transport, or endpoint is supplied. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

open SemigroupBasis

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

-- xx=xxx
def basisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

-- xyx=xxyx
def basisLaw1 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

-- xxyy=xyxy
def basisLaw2 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩

-- xxyy=xyyx
def basisLaw3 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

-- xxyy=yxxy
def basisLaw4 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

-- xyxzz=xzyxz
def basisLaw5 : Identity Nat := ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [2, 1, 0, 2]⟩⟩

-- xyxzz=zxyxz
def basisLaw6 : Identity Nat := ⟨⟨0, [1, 0, 2, 2]⟩, ⟨2, [0, 1, 0, 2]⟩⟩

-- xyzxz=xyzzx
def basisLaw7 : Identity Nat := ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

-- xyzxz=zyxxz
def basisLaw8 : Identity Nat := ⟨⟨0, [1, 2, 0, 2]⟩, ⟨2, [1, 0, 0, 2]⟩⟩

-- xxyzz=xxzyzz
def basisLaw9 : Identity Nat := ⟨⟨0, [0, 1, 2, 2]⟩, ⟨0, [0, 2, 1, 2, 2]⟩⟩

-- xyxztz=xzyxtz
def basisLaw10 : Identity Nat := ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [2, 1, 0, 3, 2]⟩⟩

-- xyxztz=zxyxtz
def basisLaw11 : Identity Nat := ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨2, [0, 1, 0, 3, 2]⟩⟩

-- xyzxtz=zyxxtz
def basisLaw12 : Identity Nat := ⟨⟨0, [1, 2, 0, 3, 2]⟩, ⟨2, [1, 0, 0, 3, 2]⟩⟩

-- xyzztx=zyxztx
def basisLaw13 : Identity Nat := ⟨⟨0, [1, 2, 2, 3, 0]⟩, ⟨2, [1, 0, 2, 3, 0]⟩⟩

-- xyztxz=zyxtxz
def basisLaw14 : Identity Nat := ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨2, [1, 0, 3, 0, 2]⟩⟩

-- xyztzx=zyxtzx
def basisLaw15 : Identity Nat := ⟨⟨0, [1, 2, 3, 2, 0]⟩, ⟨2, [1, 0, 3, 2, 0]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2, basisLaw3, basisLaw4, basisLaw5, basisLaw6, basisLaw7, basisLaw8, basisLaw9, basisLaw10, basisLaw11, basisLaw12, basisLaw13, basisLaw14, basisLaw15]

namespace S6_6432

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6))
  else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6))
  else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6))
  else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6))
  else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6))
  else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem law0Valid : basisLaw0.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw0.map toFin1).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw0.map toFin1) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law1Valid : basisLaw1.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw1.map toFin2).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw1.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law2Valid : basisLaw2.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw2.map toFin2).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw2.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law3Valid : basisLaw3.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw3.map toFin2).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw3.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law4Valid : basisLaw4.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw4.map toFin2).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw4.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law5Valid : basisLaw5.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw5.map toFin3).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw5.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law6Valid : basisLaw6.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw6.map toFin3).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw6.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law7Valid : basisLaw7.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw7.map toFin3).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw7.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law8Valid : basisLaw8.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw8.map toFin3).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw8.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law9Valid : basisLaw9.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw9.map toFin3).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw9.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law10Valid : basisLaw10.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw10.map toFin4).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw10.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law11Valid : basisLaw11.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw11.map toFin4).map Fin.val = basisLaw11 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw11.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law12Valid : basisLaw12.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw12.map toFin4).map Fin.val = basisLaw12 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw12.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law13Valid : basisLaw13.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw13.map toFin4).map Fin.val = basisLaw13 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw13.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law14Valid : basisLaw14.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw14.map toFin4).map Fin.val = basisLaw14 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw14.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law15Valid : basisLaw15.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw15.map toFin4).map Fin.val = basisLaw15 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw15.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem tableModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact law0Valid
  · exact law1Valid
  · exact law2Valid
  · exact law3Valid
  · exact law4Valid
  · exact law5Valid
  · exact law6Valid
  · exact law7Valid
  · exact law8Valid
  · exact law9Valid
  · exact law10Valid
  · exact law11Valid
  · exact law12Valid
  · exact law13Valid
  · exact law14Valid
  · exact law15Valid

theorem oppositeModels : Models table.semigroup.opposite (reversedBasis basis) :=
  tableModels.oppositeReversed

end S6_6432

namespace S6_6439

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6))
  else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6))
  else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6))
  else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6))
  else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6))
  else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem law0Valid : basisLaw0.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw0.map toFin1).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw0.map toFin1) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law1Valid : basisLaw1.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw1.map toFin2).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw1.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law2Valid : basisLaw2.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw2.map toFin2).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw2.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law3Valid : basisLaw3.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw3.map toFin2).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw3.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law4Valid : basisLaw4.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw4.map toFin2).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw4.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law5Valid : basisLaw5.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw5.map toFin3).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw5.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law6Valid : basisLaw6.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw6.map toFin3).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw6.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law7Valid : basisLaw7.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw7.map toFin3).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw7.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law8Valid : basisLaw8.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw8.map toFin3).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw8.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law9Valid : basisLaw9.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw9.map toFin3).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw9.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law10Valid : basisLaw10.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw10.map toFin4).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw10.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law11Valid : basisLaw11.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw11.map toFin4).map Fin.val = basisLaw11 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw11.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law12Valid : basisLaw12.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw12.map toFin4).map Fin.val = basisLaw12 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw12.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law13Valid : basisLaw13.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw13.map toFin4).map Fin.val = basisLaw13 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw13.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law14Valid : basisLaw14.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw14.map toFin4).map Fin.val = basisLaw14 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw14.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law15Valid : basisLaw15.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw15.map toFin4).map Fin.val = basisLaw15 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw15.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem tableModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact law0Valid
  · exact law1Valid
  · exact law2Valid
  · exact law3Valid
  · exact law4Valid
  · exact law5Valid
  · exact law6Valid
  · exact law7Valid
  · exact law8Valid
  · exact law9Valid
  · exact law10Valid
  · exact law11Valid
  · exact law12Valid
  · exact law13Valid
  · exact law14Valid
  · exact law15Valid

theorem oppositeModels : Models table.semigroup.opposite (reversedBasis basis) :=
  tableModels.oppositeReversed

end S6_6439

end SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

/-! Exact msg0521 finite30-law table witnesses for4091/4297. No unrestricted
reach, separation, completeness, transport, or endpoint is supplied. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0521RepairedThirtyLawFinite

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

-- xx=xxxx
def basisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

-- xxyy=xyyx
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

-- yxxy=yxyx
def basisLaw2 : Identity Nat := ⟨⟨1, [0, 0, 1]⟩, ⟨1, [0, 1, 0]⟩⟩

-- xyx=xxxyx
def basisLaw3 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 0, 1, 0]⟩⟩

-- xyx=xxyxx
def basisLaw4 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0, 0]⟩⟩

-- xyx=xyxxx
def basisLaw5 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩

-- xxyxz=xyxxz
def basisLaw6 : Identity Nat := ⟨⟨0, [0, 1, 0, 2]⟩, ⟨0, [1, 0, 0, 2]⟩⟩

-- xxyyy=xyyyx
def basisLaw7 : Identity Nat := ⟨⟨0, [0, 1, 1, 1]⟩, ⟨0, [1, 1, 1, 0]⟩⟩

-- xxyzx=xyzxx
def basisLaw8 : Identity Nat := ⟨⟨0, [0, 1, 2, 0]⟩, ⟨0, [1, 2, 0, 0]⟩⟩

-- xxyzy=xxzyy
def basisLaw9 : Identity Nat := ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [0, 2, 1, 1]⟩⟩

-- xxyzy=xyxzy
def basisLaw10 : Identity Nat := ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 0, 2, 1]⟩⟩

-- xxyzy=xyzyx
def basisLaw11 : Identity Nat := ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 2, 1, 0]⟩⟩

-- xxyzy=xzyxy
def basisLaw12 : Identity Nat := ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [2, 1, 0, 1]⟩⟩

-- xxyzy=xzyyx
def basisLaw13 : Identity Nat := ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [2, 1, 1, 0]⟩⟩

-- xyxzx=xzxyx
def basisLaw14 : Identity Nat := ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [2, 0, 1, 0]⟩⟩

-- xyxzz=xzyxz
def basisLaw15 : Identity Nat := ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [2, 1, 0, 2]⟩⟩

-- xyxzz=xzzyx
def basisLaw16 : Identity Nat := ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [2, 2, 1, 0]⟩⟩

-- xyyzy=xyzyy
def basisLaw17 : Identity Nat := ⟨⟨0, [1, 1, 2, 1]⟩, ⟨0, [1, 2, 1, 1]⟩⟩

-- xxyztz=xxtzyz
def basisLaw18 : Identity Nat := ⟨⟨0, [0, 1, 2, 3, 2]⟩, ⟨0, [0, 3, 2, 1, 2]⟩⟩

-- xxyztz=xyzxtz
def basisLaw19 : Identity Nat := ⟨⟨0, [0, 1, 2, 3, 2]⟩, ⟨0, [1, 2, 0, 3, 2]⟩⟩

-- xxyztz=xyztzx
def basisLaw20 : Identity Nat := ⟨⟨0, [0, 1, 2, 3, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

-- xxyztz=xtzxyz
def basisLaw21 : Identity Nat := ⟨⟨0, [0, 1, 2, 3, 2]⟩, ⟨0, [3, 2, 0, 1, 2]⟩⟩

-- xyxztz=xyxtzz
def basisLaw22 : Identity Nat := ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [1, 0, 3, 2, 2]⟩⟩

-- xyxztz=xzyxtz
def basisLaw23 : Identity Nat := ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [2, 1, 0, 3, 2]⟩⟩

-- xyxztz=xztzyx
def basisLaw24 : Identity Nat := ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [2, 3, 2, 1, 0]⟩⟩

-- xyxztz=xtzyxz
def basisLaw25 : Identity Nat := ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [3, 2, 1, 0, 2]⟩⟩

-- xyxztz=xtzzyx
def basisLaw26 : Identity Nat := ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [3, 2, 2, 1, 0]⟩⟩

-- xyxztt=xzttyx
def basisLaw27 : Identity Nat := ⟨⟨0, [1, 0, 2, 3, 3]⟩, ⟨0, [2, 3, 3, 1, 0]⟩⟩

-- xyxtzz=xtzzyx
def basisLaw28 : Identity Nat := ⟨⟨0, [1, 0, 3, 2, 2]⟩, ⟨0, [3, 2, 2, 1, 0]⟩⟩

-- xyxtzt=xzttyx
def basisLaw29 : Identity Nat := ⟨⟨0, [1, 0, 3, 2, 3]⟩, ⟨0, [2, 3, 3, 1, 0]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2, basisLaw3, basisLaw4, basisLaw5, basisLaw6, basisLaw7, basisLaw8, basisLaw9, basisLaw10, basisLaw11, basisLaw12, basisLaw13, basisLaw14, basisLaw15, basisLaw16, basisLaw17, basisLaw18, basisLaw19, basisLaw20, basisLaw21, basisLaw22, basisLaw23, basisLaw24, basisLaw25, basisLaw26, basisLaw27, basisLaw28, basisLaw29]

namespace S6_4091

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6))
  else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6))
  else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6))
  else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6))
  else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6))
  else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

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
  have roundTrip : (basisLaw5.map toFin2).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw5.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law6Valid : basisLaw6.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw6.map toFin3).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw6.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law7Valid : basisLaw7.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw7.map toFin2).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw7.map toFin2) (by decide)
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
  have roundTrip : (basisLaw10.map toFin3).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw10.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law11Valid : basisLaw11.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw11.map toFin3).map Fin.val = basisLaw11 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw11.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law12Valid : basisLaw12.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw12.map toFin3).map Fin.val = basisLaw12 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw12.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law13Valid : basisLaw13.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw13.map toFin3).map Fin.val = basisLaw13 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw13.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law14Valid : basisLaw14.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw14.map toFin3).map Fin.val = basisLaw14 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw14.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law15Valid : basisLaw15.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw15.map toFin3).map Fin.val = basisLaw15 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw15.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law16Valid : basisLaw16.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw16.map toFin3).map Fin.val = basisLaw16 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw16.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law17Valid : basisLaw17.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw17.map toFin3).map Fin.val = basisLaw17 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw17.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law18Valid : basisLaw18.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw18.map toFin4).map Fin.val = basisLaw18 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw18.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law19Valid : basisLaw19.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw19.map toFin4).map Fin.val = basisLaw19 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw19.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law20Valid : basisLaw20.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw20.map toFin4).map Fin.val = basisLaw20 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw20.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law21Valid : basisLaw21.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw21.map toFin4).map Fin.val = basisLaw21 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw21.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law22Valid : basisLaw22.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw22.map toFin4).map Fin.val = basisLaw22 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw22.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law23Valid : basisLaw23.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw23.map toFin4).map Fin.val = basisLaw23 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw23.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law24Valid : basisLaw24.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw24.map toFin4).map Fin.val = basisLaw24 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw24.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law25Valid : basisLaw25.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw25.map toFin4).map Fin.val = basisLaw25 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw25.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law26Valid : basisLaw26.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw26.map toFin4).map Fin.val = basisLaw26 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw26.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law27Valid : basisLaw27.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw27.map toFin4).map Fin.val = basisLaw27 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw27.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law28Valid : basisLaw28.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw28.map toFin4).map Fin.val = basisLaw28 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw28.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law29Valid : basisLaw29.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw29.map toFin4).map Fin.val = basisLaw29 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw29.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem tableModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact law16Valid
  · exact law17Valid
  · exact law18Valid
  · exact law19Valid
  · exact law20Valid
  · exact law21Valid
  · exact law22Valid
  · exact law23Valid
  · exact law24Valid
  · exact law25Valid
  · exact law26Valid
  · exact law27Valid
  · exact law28Valid
  · exact law29Valid

theorem oppositeModels : Models table.semigroup.opposite (reversedBasis basis) :=
  tableModels.oppositeReversed

end S6_4091

namespace S6_4297

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6))
  else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6))
  else if a = 2 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6))
  else if a = 3 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6))
  else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6))
  else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

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
  have roundTrip : (basisLaw5.map toFin2).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw5.map toFin2) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law6Valid : basisLaw6.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw6.map toFin3).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw6.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law7Valid : basisLaw7.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw7.map toFin2).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw7.map toFin2) (by decide)
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
  have roundTrip : (basisLaw10.map toFin3).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw10.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law11Valid : basisLaw11.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw11.map toFin3).map Fin.val = basisLaw11 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw11.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law12Valid : basisLaw12.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw12.map toFin3).map Fin.val = basisLaw12 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw12.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law13Valid : basisLaw13.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw13.map toFin3).map Fin.val = basisLaw13 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw13.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law14Valid : basisLaw14.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw14.map toFin3).map Fin.val = basisLaw14 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw14.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law15Valid : basisLaw15.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw15.map toFin3).map Fin.val = basisLaw15 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw15.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law16Valid : basisLaw16.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw16.map toFin3).map Fin.val = basisLaw16 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw16.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law17Valid : basisLaw17.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw17.map toFin3).map Fin.val = basisLaw17 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw17.map toFin3) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law18Valid : basisLaw18.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw18.map toFin4).map Fin.val = basisLaw18 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw18.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law19Valid : basisLaw19.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw19.map toFin4).map Fin.val = basisLaw19 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw19.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law20Valid : basisLaw20.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw20.map toFin4).map Fin.val = basisLaw20 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw20.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law21Valid : basisLaw21.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw21.map toFin4).map Fin.val = basisLaw21 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw21.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law22Valid : basisLaw22.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw22.map toFin4).map Fin.val = basisLaw22 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw22.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law23Valid : basisLaw23.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw23.map toFin4).map Fin.val = basisLaw23 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw23.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law24Valid : basisLaw24.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw24.map toFin4).map Fin.val = basisLaw24 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw24.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law25Valid : basisLaw25.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw25.map toFin4).map Fin.val = basisLaw25 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw25.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law26Valid : basisLaw26.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw26.map toFin4).map Fin.val = basisLaw26 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw26.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law27Valid : basisLaw27.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw27.map toFin4).map Fin.val = basisLaw27 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw27.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law28Valid : basisLaw28.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw28.map toFin4).map Fin.val = basisLaw28 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw28.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law29Valid : basisLaw29.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw29.map toFin4).map Fin.val = basisLaw29 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw29.map toFin4) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem tableModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact law16Valid
  · exact law17Valid
  · exact law18Valid
  · exact law19Valid
  · exact law20Valid
  · exact law21Valid
  · exact law22Valid
  · exact law23Valid
  · exact law24Valid
  · exact law25Valid
  · exact law26Valid
  · exact law27Valid
  · exact law28Valid
  · exact law29Valid

theorem oppositeModels : Models table.semigroup.opposite (reversedBasis basis) :=
  tableModels.oppositeReversed

end S6_4297

end SemigroupBasis.CoRoots.Order6Sunday.Msg0521RepairedThirtyLawFinite

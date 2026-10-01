import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Opposite

/-! Literal-table soundness of the exact msg-0447 F/G law lists.
All lists and structural controls are finite. No unrestricted
recursive-key, reachability or completeness field is supplied. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite

open SemigroupBasis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

namespace S6_9726

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def basisLaw0 : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 0, 1]⟩, ⟨0, [0, 1, 0]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩
def basisLaw3 : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
def basisLaw4 : Identity Nat := ⟨⟨0, [1, 0, 0, 2]⟩, ⟨0, [1, 0, 2, 0]⟩⟩
def basisLaw5 : Identity Nat := ⟨⟨0, [1, 2, 0, 1]⟩, ⟨0, [1, 2, 1, 0]⟩⟩
def basisLaw6 : Identity Nat := ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2, basisLaw3, basisLaw4, basisLaw5, basisLaw6]

theorem law0Valid : basisLaw0.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law0OppositeValid : basisLaw0.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law0Valid

theorem law1Valid : basisLaw1.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law1OppositeValid : basisLaw1.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law1Valid

theorem law2Valid : basisLaw2.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law2OppositeValid : basisLaw2.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law2Valid

theorem law3Valid : basisLaw3.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law3OppositeValid : basisLaw3.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law3Valid

theorem law4Valid : basisLaw4.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law4OppositeValid : basisLaw4.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law4Valid

theorem law5Valid : basisLaw5.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law5OppositeValid : basisLaw5.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law5Valid

theorem law6Valid : basisLaw6.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law6OppositeValid : basisLaw6.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law6Valid

/-- Soundness of this explicitly listed finite basis, not completeness. -/
theorem tableModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact law0Valid
  · exact law1Valid
  · exact law2Valid
  · exact law3Valid
  · exact law4Valid
  · exact law5Valid
  · exact law6Valid

theorem oppositeModels : Models table.semigroup.opposite (reversedBasis basis) :=
  tableModels.oppositeReversed

/-- Zero-based element 5 is the identity; the quantifier is over six elements. -/
theorem identityControl : ∀ a : Fin 6, mul 5 a = a ∧ mul a 5 = a := by decide

/-- Fixed zero-based left-zero, chain and right-action controls. -/
theorem structuralControl :
    (∀ a : Fin 6, mul 3 a = 3 ∧ mul 4 a = 4) ∧
    mul 2 2 = 1 ∧ mul (mul 2 2) 2 = 0 ∧ mul 2 4 = 3 ∧ mul 2 3 = 0 := by decide

end S6_9726

namespace S6_6447

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def basisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [1, 1]⟩, ⟨1, [0, 1, 1]⟩⟩
def basisLaw3 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
def basisLaw4 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
def basisLaw5 : Identity Nat := ⟨⟨0, [0, 1, 2, 1]⟩, ⟨1, [0, 0, 2, 1]⟩⟩
def basisLaw6 : Identity Nat := ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 0, 2]⟩⟩
def basisLaw7 : Identity Nat := ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩
def basisLaw8 : Identity Nat := ⟨⟨0, [1, 2, 0, 1]⟩, ⟨0, [1, 2, 1, 0]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2, basisLaw3, basisLaw4, basisLaw5, basisLaw6, basisLaw7, basisLaw8]

theorem law0Valid : basisLaw0.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law0OppositeValid : basisLaw0.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law0Valid

theorem law1Valid : basisLaw1.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law1OppositeValid : basisLaw1.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law1Valid

theorem law2Valid : basisLaw2.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law2OppositeValid : basisLaw2.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law2Valid

theorem law3Valid : basisLaw3.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law3OppositeValid : basisLaw3.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law3Valid

theorem law4Valid : basisLaw4.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law4OppositeValid : basisLaw4.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law4Valid

theorem law5Valid : basisLaw5.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law5OppositeValid : basisLaw5.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law5Valid

theorem law6Valid : basisLaw6.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law6OppositeValid : basisLaw6.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law6Valid

theorem law7Valid : basisLaw7.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law7OppositeValid : basisLaw7.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law7Valid

theorem law8Valid : basisLaw8.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem law8OppositeValid : basisLaw8.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact law8Valid

/-- Soundness of this explicitly listed finite basis, not completeness. -/
theorem tableModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact law0Valid
  · exact law1Valid
  · exact law2Valid
  · exact law3Valid
  · exact law4Valid
  · exact law5Valid
  · exact law6Valid
  · exact law7Valid
  · exact law8Valid

theorem oppositeModels : Models table.semigroup.opposite (reversedBasis basis) :=
  tableModels.oppositeReversed

/-- Zero-based element 5 is the identity; the quantifier is over six elements. -/
theorem identityControl : ∀ a : Fin 6, mul 5 a = a ∧ mul a 5 = a := by decide

/-- Fixed right-lowering actions and left action on the three-element chain. -/
theorem structuralControl :
    mul 2 4 = 1 ∧ mul 2 3 = 0 ∧ mul 4 4 = 3 ∧
    (∀ a : Fin 6, a.val < 3 → mul 3 a = a ∧ mul 4 a = a) := by decide

end S6_6447

end SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite

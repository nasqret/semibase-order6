import SemigroupBasis.CoRoots.Order6Sunday.L6FordOnly.Sigma09a2Finite
import SemigroupBasis.Opposite

/-! Finite FORDONLY-EXACT layer for the four laws and four literal tables
recorded in msg0473 and the finite-only msg0484 claim. Reordering the old
law list and reversing its second law do not change its equational content.
The finite screens are separate bounded evidence, not completeness. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.FordOnlyExactFinite

open SemigroupBasis

/-- xxx = xxxx. -/
def basisLaw0 : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0]⟩⟩

/-- xxy = xyx. -/
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

/-- xxy = xxxy. -/
def basisLaw2 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩⟩

/-- xyy = xyyy. -/
def basisLaw3 : Identity Nat := ⟨⟨0, [1, 1]⟩, ⟨0, [1, 1, 1]⟩⟩

/-- The approved four laws in their exact displayed order and orientation. -/
def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2, basisLaw3]

theorem law0FromRecorded :
    Derives L6FordOnly.Sigma09a2Finite.basis basisLaw0.lhs basisLaw0.rhs :=
  Derives.fromBasis (e := basisLaw0)
    (by decide)

theorem law1FromRecorded :
    Derives L6FordOnly.Sigma09a2Finite.basis basisLaw1.lhs basisLaw1.rhs :=
  Derives.fromBasis (e := basisLaw1)
    (by decide)

theorem law2FromRecorded :
    Derives L6FordOnly.Sigma09a2Finite.basis basisLaw2.lhs basisLaw2.rhs := by
  have backward :
      Derives L6FordOnly.Sigma09a2Finite.basis basisLaw2.rhs basisLaw2.lhs :=
    Derives.fromBasis (e := ⟨basisLaw2.rhs, basisLaw2.lhs⟩)
      (by decide)
  exact backward.symm

theorem law3FromRecorded :
    Derives L6FordOnly.Sigma09a2Finite.basis basisLaw3.lhs basisLaw3.rhs :=
  Derives.fromBasis (e := basisLaw3)
    (by decide)

/-- Only the four entries of the approved finite list are covered. -/
theorem basisFromRecorded :
    FiniteCertificate.DerivesAll L6FordOnly.Sigma09a2Finite.basis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact law0FromRecorded
  · exact law1FromRecorded
  · exact law2FromRecorded
  · exact law3FromRecorded

private def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

namespace S6_5553

/-- Reuse the recorded literal table and its original four-law proof. -/
theorem models :
    Models L6FordOnly.Sigma09a2Finite.S6_5553.table.semigroup basis := by
  intro identity member valuation
  exact Derives.sound L6FordOnly.Sigma09a2Finite.S6_5553.models
    (basisFromRecorded identity member) valuation

theorem oppositeModels :
    Models L6FordOnly.Sigma09a2Finite.S6_5553.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

end S6_5553

namespace S6_5563

/-- The exact catalogue table pinned by the finite claim receipt. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6))
  else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6))
  else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6))
  else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6))
  else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6))
  else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinTwo (by decide)

theorem oppositeModels :
    Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_5563

namespace S6_9546

/-- Reuse the recorded literal table and its original four-law proof. -/
theorem models :
    Models L6FordOnly.Sigma09a2Finite.S6_9546.table.semigroup basis := by
  intro identity member valuation
  exact Derives.sound L6FordOnly.Sigma09a2Finite.S6_9546.models
    (basisFromRecorded identity member) valuation

theorem oppositeModels :
    Models L6FordOnly.Sigma09a2Finite.S6_9546.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

end S6_9546

namespace S6_9657

/-- The exact catalogue table pinned by the finite claim receipt. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6))
  else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6))
  else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6))
  else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6))
  else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6))
  else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinTwo (by decide)

theorem oppositeModels :
    Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_9657

end SemigroupBasis.CoRoots.Order6Sunday.FordOnlyExactFinite

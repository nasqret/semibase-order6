import SemigroupBasis.CoRoots.Order6Sunday.LateFinite
import SemigroupBasis.Opposite

/-! Fixed-list and literal-table inputs for the two twin schemas staged in
msg0491/0492. The eleven recorded tables and their old Models are reused
unchanged. Only the displayed two-law lists are covered here; no converse
law-list reduction or arbitrary-word normal form is asserted. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.TwinTwoLawFinite

open SemigroupBasis

namespace A

/-- x = xxx. -/
def basisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

/-- xyzy = xzyy. -/
def basisLaw1 : Identity Nat := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

/-- Family A's exact staged order and orientation. -/
def basis : List (Identity Nat) := [basisLaw0, basisLaw1]

theorem law0FromRecorded :
    Derives LateFinite.SigmaF137a.basis basisLaw0.lhs basisLaw0.rhs :=
  Derives.fromBasis (e := basisLaw0) (by decide)

theorem law1FromRecorded :
    Derives LateFinite.SigmaF137a.basis basisLaw1.lhs basisLaw1.rhs :=
  Derives.fromBasis (e := basisLaw1) (by decide)

/-- Only the two members of this concrete list are covered. -/
theorem basisFromRecorded :
    FiniteCertificate.DerivesAll LateFinite.SigmaF137a.basis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact law0FromRecorded
  · exact law1FromRecorded

namespace S6_11915

theorem models :
    Models LateFinite.SigmaF137c.S6_11915.table.semigroup basis := by
  intro identity member valuation
  exact Derives.sound LateFinite.SigmaF137c.S6_11915.models
    (basisFromRecorded identity member) valuation

theorem oppositeModels :
    Models LateFinite.SigmaF137c.S6_11915.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

end S6_11915

namespace S6_14689

theorem models :
    Models LateFinite.SigmaF137c.S6_14689.table.semigroup basis := by
  intro identity member valuation
  exact Derives.sound LateFinite.SigmaF137c.S6_14689.models
    (basisFromRecorded identity member) valuation

theorem oppositeModels :
    Models LateFinite.SigmaF137c.S6_14689.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

end S6_14689

namespace S6_14814

theorem models :
    Models LateFinite.SigmaF137a.S6_14814.table.semigroup basis := by
  intro identity member valuation
  exact Derives.sound LateFinite.SigmaF137a.S6_14814.models
    (basisFromRecorded identity member) valuation

theorem oppositeModels :
    Models LateFinite.SigmaF137a.S6_14814.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

end S6_14814

namespace S6_14833

theorem models :
    Models LateFinite.SigmaF137b.S6_14833.table.semigroup basis := by
  intro identity member valuation
  exact Derives.sound LateFinite.SigmaF137b.S6_14833.models
    (basisFromRecorded identity member) valuation

theorem oppositeModels :
    Models LateFinite.SigmaF137b.S6_14833.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

end S6_14833

namespace S6_14851

theorem models :
    Models LateFinite.SigmaF137c.S6_14851.table.semigroup basis := by
  intro identity member valuation
  exact Derives.sound LateFinite.SigmaF137c.S6_14851.models
    (basisFromRecorded identity member) valuation

theorem oppositeModels :
    Models LateFinite.SigmaF137c.S6_14851.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

end S6_14851

namespace S6_14852

theorem models :
    Models LateFinite.SigmaF137c.S6_14852.table.semigroup basis := by
  intro identity member valuation
  exact Derives.sound LateFinite.SigmaF137c.S6_14852.models
    (basisFromRecorded identity member) valuation

theorem oppositeModels :
    Models LateFinite.SigmaF137c.S6_14852.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

end S6_14852

end A

namespace B

/-- x = xxx. -/
def basisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

/-- yzyx = yyzx, the literal reversal of Family A's second law. -/
def basisLaw1 : Identity Nat := ⟨⟨1, [2, 1, 0]⟩, ⟨1, [1, 2, 0]⟩⟩

/-- Family B's exact staged order and orientation. -/
def basis : List (Identity Nat) := [basisLaw0, basisLaw1]

private def cycleVariables : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | n => n

theorem law0FromRecorded :
    Derives LateFinite.Sigma086fa.basis basisLaw0.lhs basisLaw0.rhs :=
  Derives.fromBasis (e := basisLaw0) (by decide)

/-- Reverse the recorded xxyz = xyxz and rename (x,y,z) to (y,z,x). -/
theorem law1FromRecorded :
    Derives LateFinite.Sigma086fa.basis basisLaw1.lhs basisLaw1.rhs := by
  have recorded :
      Derives LateFinite.Sigma086fa.basis
        LateFinite.Sigma086fa.basisLaw8.lhs LateFinite.Sigma086fa.basisLaw8.rhs :=
    Derives.fromBasis (e := LateFinite.Sigma086fa.basisLaw8) (by decide)
  exact Derives.rename recorded.symm cycleVariables

/-- Only the two members of this concrete list are covered. -/
theorem basisFromRecorded :
    FiniteCertificate.DerivesAll LateFinite.Sigma086fa.basis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact law0FromRecorded
  · exact law1FromRecorded

namespace S6_11897

theorem models :
    Models LateFinite.Sigma086fa.S6_11897.table.semigroup basis := by
  intro identity member valuation
  exact Derives.sound LateFinite.Sigma086fa.S6_11897.models
    (basisFromRecorded identity member) valuation

theorem oppositeModels :
    Models LateFinite.Sigma086fa.S6_11897.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

end S6_11897

namespace S6_14651

theorem models :
    Models LateFinite.Sigma086fb.S6_14651.table.semigroup basis := by
  intro identity member valuation
  exact Derives.sound LateFinite.Sigma086fb.S6_14651.models
    (basisFromRecorded identity member) valuation

theorem oppositeModels :
    Models LateFinite.Sigma086fb.S6_14651.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

end S6_14651

namespace S6_14680

theorem models :
    Models LateFinite.Sigma086fc.S6_14680.table.semigroup basis := by
  intro identity member valuation
  exact Derives.sound LateFinite.Sigma086fc.S6_14680.models
    (basisFromRecorded identity member) valuation

theorem oppositeModels :
    Models LateFinite.Sigma086fc.S6_14680.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

end S6_14680

namespace S6_14762

theorem models :
    Models LateFinite.Sigma086fc.S6_14762.table.semigroup basis := by
  intro identity member valuation
  exact Derives.sound LateFinite.Sigma086fc.S6_14762.models
    (basisFromRecorded identity member) valuation

theorem oppositeModels :
    Models LateFinite.Sigma086fc.S6_14762.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

end S6_14762

namespace S6_14780

theorem models :
    Models LateFinite.Sigma086fc.S6_14780.table.semigroup basis := by
  intro identity member valuation
  exact Derives.sound LateFinite.Sigma086fc.S6_14780.models
    (basisFromRecorded identity member) valuation

theorem oppositeModels :
    Models LateFinite.Sigma086fc.S6_14780.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

end S6_14780

end B

/-- Closed equality of two concrete two-entry lists; no key theorem. -/
theorem basisBIsReversal : B.basis = reversedBasis A.basis := by decide

end SemigroupBasis.CoRoots.Order6Sunday.TwinTwoLawFinite

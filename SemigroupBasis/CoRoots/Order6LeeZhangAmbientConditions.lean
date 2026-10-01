import SemigroupBasis.CoRoots.S5_379Family
import SemigroupBasis.CoRoots.S5_791Family
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Generated.S3_4
import SemigroupBasis.Generated.S4_96
import SemigroupBasis.Order6Subdirect.Common

/-!
# Shared Lee--Zhang ambient conditions for order six

The order-six canonical-root ledger contains several tables whose varieties
are the ambient joins in Lee--Zhang Conditions 7, 8, and 14.  This file fixes
the exact identity systems, proves their finite-factor soundness, and reduces
each unrestricted completeness statement to one named derivational
obligation.  Target-specific files only need subdirect witnesses once these
three obligations are closed.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions

open SemigroupBasis
open SemigroupBasis.Order6Subdirect

namespace Common

def productPair {A : Type u} {B : Type v}
    (G : Semigroup A) (H : Semigroup B) (a : A) (b : B) :
    SubdirectPair (G.prod H) G H where
  left := prodFstSplit G H b
  right := prodSndSplit G H a
  jointlyInjective := by
    intro left right equality
    exact Prod.ext (congrArg Prod.fst equality)
      (congrArg Prod.snd equality)

end Common

/-! ## Condition 7 -/

namespace Condition7

def cyclicTable : FiniteTable :=
  SemigroupBasis.Generated.S2_2.table

def coreTable : FiniteTable :=
  SemigroupBasis.CoRoots.S5_379.table

def cyclic : Semigroup (Fin 2) := cyclicTable.semigroup
def core : Semigroup (Fin 5) := coreTable.semigroup
def product : Semigroup (Fin 2 × Fin 5) := cyclic.prod core

/-- Lee--Zhang Condition 7 in the canonical direct orientation:
`x^4 = x^2`, `x^3 y x = x y x`, `x y^2 x = y x^2 y`, and
`x y z x = x z y x`. -/
def finiteBasis : List (Identity (Fin 3)) :=
  [
    ⟨⟨0, [0, 0, 0]⟩, ⟨0, [0]⟩⟩,
    ⟨⟨0, [0, 0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩,
    ⟨⟨0, [1, 1, 0]⟩, ⟨1, [0, 0, 1]⟩⟩,
    ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩
  ]

def basis : List (Identity Nat) :=
  finiteBasis.map (Identity.map Fin.val)

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

theorem cyclicModels : Models cyclic basis :=
  models_of_finite_checks cyclicTable finiteBasis (by decide)

theorem coreModels : Models core basis :=
  models_of_finite_checks coreTable finiteBasis (by decide)

/-- The sole unrestricted mathematical obligation for Condition 7. -/
def DerivationalObligation : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy cyclic →
    identity.SatisfiedBy core →
    Derives basis identity.lhs identity.rhs

def intersectionBasis (complete : DerivationalObligation) :
    IntersectionBasis cyclic core basis where
  leftModels := cyclicModels
  rightModels := coreModels
  complete := complete

theorem product_basisFor (complete : DerivationalObligation) :
    BasisFor product basis :=
  IntersectionBasis.basisFor (intersectionBasis complete)
    (Common.productPair cyclic core 0 0)

theorem oppositeProduct_basisFor (complete : DerivationalObligation) :
    BasisFor product.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (product_basisFor complete).oppositeReversed

end Condition7

/-! ## Condition 8 -/

namespace Condition8

def firstTable : FiniteTable :=
  SemigroupBasis.Generated.S3_4.table

def affineTable : FiniteTable :=
  SemigroupBasis.Generated.S4_96.table

def firstFactor : Semigroup (Fin 3) := firstTable.semigroup
def affineFactor : Semigroup (Fin 4) := affineTable.semigroup
def product : Semigroup (Fin 3 × Fin 4) :=
  firstFactor.prod affineFactor

/-- The reversal of the displayed Condition 8 system, matching the canonical
`S3_4 x S4_96` factor orientation:
`z y x^3 = z y x`, `y x^3 = y^3 x`, `x^2 y x = y x^3`, and
`y x y x = x y^2 x`. -/
def finiteBasis : List (Identity (Fin 3)) :=
  [
    ⟨⟨2, [1, 0, 0, 0]⟩, ⟨2, [1, 0]⟩⟩,
    ⟨⟨1, [0, 0, 0]⟩, ⟨1, [1, 1, 0]⟩⟩,
    ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 0, 0]⟩⟩,
    ⟨⟨1, [0, 1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩
  ]

def basis : List (Identity Nat) :=
  finiteBasis.map (Identity.map Fin.val)

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

theorem firstFactorModels : Models firstFactor basis :=
  models_of_finite_checks firstTable finiteBasis (by decide)

theorem affineFactorModels : Models affineFactor basis :=
  models_of_finite_checks affineTable finiteBasis (by decide)

/-- The sole unrestricted mathematical obligation for Condition 8. -/
def DerivationalObligation : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy firstFactor →
    identity.SatisfiedBy affineFactor →
    Derives basis identity.lhs identity.rhs

def intersectionBasis (complete : DerivationalObligation) :
    IntersectionBasis firstFactor affineFactor basis where
  leftModels := firstFactorModels
  rightModels := affineFactorModels
  complete := complete

theorem product_basisFor (complete : DerivationalObligation) :
    BasisFor product basis :=
  IntersectionBasis.basisFor (intersectionBasis complete)
    (Common.productPair firstFactor affineFactor 0 0)

theorem oppositeProduct_basisFor (complete : DerivationalObligation) :
    BasisFor product.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (product_basisFor complete).oppositeReversed

end Condition8

/-! ## Condition 14 -/

namespace Condition14

def cyclicTable : FiniteTable :=
  SemigroupBasis.Generated.S2_2.table

def coreTable : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_791.table

def cyclic : Semigroup (Fin 2) := cyclicTable.semigroup
def core : Semigroup (Fin 5) := coreTable.semigroup
def product : Semigroup (Fin 2 × Fin 5) := cyclic.prod core

/-- Lee--Zhang Condition 14 in the canonical direct orientation. -/
def finiteBasis : List (Identity (Fin 3)) :=
  [
    ⟨⟨0, [0, 0, 0]⟩, ⟨0, [0]⟩⟩,
    ⟨⟨0, [1, 1, 1, 0]⟩, ⟨0, [1, 0]⟩⟩,
    ⟨⟨0, [1, 0, 0, 0]⟩, ⟨0, [1, 0]⟩⟩,
    ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩,
    ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [0, 1, 2, 0]⟩⟩,
    ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
  ]

def basis : List (Identity Nat) :=
  finiteBasis.map (Identity.map Fin.val)

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

theorem cyclicModels : Models cyclic basis :=
  models_of_finite_checks cyclicTable finiteBasis (by decide)

theorem coreModels : Models core basis :=
  models_of_finite_checks coreTable finiteBasis (by decide)

/-- The sole unrestricted mathematical obligation for Condition 14. -/
def DerivationalObligation : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy cyclic →
    identity.SatisfiedBy core →
    Derives basis identity.lhs identity.rhs

def intersectionBasis (complete : DerivationalObligation) :
    IntersectionBasis cyclic core basis where
  leftModels := cyclicModels
  rightModels := coreModels
  complete := complete

theorem product_basisFor (complete : DerivationalObligation) :
    BasisFor product basis :=
  IntersectionBasis.basisFor (intersectionBasis complete)
    (Common.productPair cyclic core 0 0)

theorem oppositeProduct_basisFor (complete : DerivationalObligation) :
    BasisFor product.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (product_basisFor complete).oppositeReversed

end Condition14

end SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions

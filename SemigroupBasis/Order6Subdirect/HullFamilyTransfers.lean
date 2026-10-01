import SemigroupBasis.CoRoots.S5_107Basis
import SemigroupBasis.CoRoots.S5_831Family
import SemigroupBasis.Order6Subdirect.Hull16_1_S3_16_S5_107
import SemigroupBasis.Order6Subdirect.Hull16_1_S3_16_S5_108
import SemigroupBasis.Order6Subdirect.Hull16_1_S3_16_S5_108op
import SemigroupBasis.Order6Subdirect.Hull16_1_S3_16_S5_109
import SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8
import SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8
import SemigroupBasis.Order6Subdirect.Hull23_1_S3_11_S5_831
import SemigroupBasis.Order6Subdirect.Hull23_1_S3_11_S5_832

/-!
# Reuse between order-six product hulls with equivalent factors

Several Lee--Zhang product hulls differ only by replacing one factor with a
semigroup having the same already-certified lower-order basis.  This module
turns one unrestricted derivational proof into the corresponding sibling
obligations.  It contains no new completeness assumption.
-/

namespace SemigroupBasis
namespace Order6Subdirect
namespace HullFamilyTransfers

/-- Two semigroups presented by the same complete basis have the same
unrestricted identity theory. -/
theorem sameIdentityTheoryOver_of_common_basis
    {A : Type u} {B : Type v} {X : Type w}
    {G : Semigroup A} {H : Semigroup B}
    {basis : List (Identity X)}
    (basisForG : BasisFor G basis) (basisForH : BasisFor H basis) :
    SameIdentityTheoryOver G H X := by
  intro identity
  constructor
  · intro validInG valuation
    exact Derives.sound basisForH.1
      (basisForG.2 identity validInG) valuation
  · intro validInH valuation
    exact Derives.sound basisForG.1
      (basisForH.2 identity validInH) valuation

theorem hull16_left_107_eq_108 :
    Hull16_1_S3_16_S5_107.G = Hull16_1_S3_16_S5_108.G := rfl

theorem hull16_left_107_eq_109 :
    Hull16_1_S3_16_S5_107.G = Hull16_1_S3_16_S5_109.G := rfl

theorem hull16_basis_107_eq_108 :
    Hull16_1_S3_16_S5_107.publishedBasis =
      Hull16_1_S3_16_S5_108.publishedBasis := rfl

theorem hull16_basis_107_eq_109 :
    Hull16_1_S3_16_S5_107.publishedBasis =
      Hull16_1_S3_16_S5_109.publishedBasis := rfl

theorem hull16_right_107_sameTheory_108 :
    SameIdentityTheoryOver
      Hull16_1_S3_16_S5_107.H Hull16_1_S3_16_S5_108.H Nat := by
  simpa only [Hull16_1_S3_16_S5_107.H,
    Hull16_1_S3_16_S5_107.rightTable,
    Hull16_1_S3_16_S5_108.H,
    Hull16_1_S3_16_S5_108.rightTable] using
      sameIdentityTheoryOver_of_common_basis
        SemigroupBasis.CoRoots.S5_107Family.S5_107.basisFor
        SemigroupBasis.CoRoots.S5_107Family.S5_108.basisFor

theorem hull16_right_107_sameTheory_109 :
    SameIdentityTheoryOver
      Hull16_1_S3_16_S5_107.H Hull16_1_S3_16_S5_109.H Nat := by
  simpa only [Hull16_1_S3_16_S5_107.H,
    Hull16_1_S3_16_S5_107.rightTable,
    Hull16_1_S3_16_S5_109.H,
    Hull16_1_S3_16_S5_109.rightTable] using
      sameIdentityTheoryOver_of_common_basis
        SemigroupBasis.CoRoots.S5_107Family.S5_107.basisFor
        SemigroupBasis.CoRoots.S5_107Family.S5_109.basisFor

/-- A proof of the Proposition 16.1 obligation for `S5_107` also closes the
`S5_108` hull. -/
theorem hull16_108_of_107
    (source : Hull16_1_S3_16_S5_107.DerivationalObligation) :
    Hull16_1_S3_16_S5_108.DerivationalObligation := by
  intro identity validLeft validRight
  have validLeftSource :
      identity.SatisfiedBy Hull16_1_S3_16_S5_107.G := by
    rw [hull16_left_107_eq_108]
    exact validLeft
  have validRightSource :
      identity.SatisfiedBy Hull16_1_S3_16_S5_107.H :=
    (hull16_right_107_sameTheory_108 identity).mpr validRight
  have derived := source identity validLeftSource validRightSource
  simpa only [hull16_basis_107_eq_108] using derived

/-- A proof of the Proposition 16.1 obligation for `S5_107` also closes the
`S5_109` hull. -/
theorem hull16_109_of_107
    (source : Hull16_1_S3_16_S5_107.DerivationalObligation) :
    Hull16_1_S3_16_S5_109.DerivationalObligation := by
  intro identity validLeft validRight
  have validLeftSource :
      identity.SatisfiedBy Hull16_1_S3_16_S5_107.G := by
    rw [hull16_left_107_eq_109]
    exact validLeft
  have validRightSource :
      identity.SatisfiedBy Hull16_1_S3_16_S5_107.H :=
    (hull16_right_107_sameTheory_109 identity).mpr validRight
  have derived := source identity validLeftSource validRightSource
  simpa only [hull16_basis_107_eq_109] using derived

/-- A proof of the Proposition 16.1 obligation for `S5_107` also closes the
`S5_108` opposite-orientation hull. -/
theorem hull16_108op_of_107
    (source : Hull16_1_S3_16_S5_107.DerivationalObligation) :
    Hull16_1_S3_16_S5_108op.DerivationalObligation := by
  have rightTheory :
      SameIdentityTheoryOver
        Hull16_1_S3_16_S5_107.H Hull16_1_S3_16_S5_108op.H Nat := by
    have sourceSelfDual :
        SameIdentityTheoryOver
          Hull16_1_S3_16_S5_107.H
          Hull16_1_S3_16_S5_107.H.opposite Nat := by
      let onto :
          SplitSurjection
            Hull16_1_S3_16_S5_107.H.opposite
            Hull16_1_S3_16_S5_107.H :=
        { toFun :=
            SemigroupBasis.CoRoots.S5_107Family.S5_107.selfDualEmbedding.toFun
          map_mul :=
            SemigroupBasis.CoRoots.S5_107Family.S5_107.selfDualEmbedding.map_mul
          preimage :=
            SemigroupBasis.CoRoots.S5_107Family.S5_107.selfDualEmbedding.toFun
          right_inverse :=
            SemigroupBasis.CoRoots.S5_107Family.S5_107.selfDualInvolution }
      intro identity
      constructor
      · exact
          SemigroupBasis.CoRoots.S5_107Family.S5_107.selfDualEmbedding.pullback_identity
            identity
      · exact onto.pushforwardIdentity identity
    have oppositeFamily :
        SameIdentityTheoryOver
          Hull16_1_S3_16_S5_107.H.opposite
          Hull16_1_S3_16_S5_108op.H Nat := by
      simpa only [Hull16_1_S3_16_S5_107.H,
        Hull16_1_S3_16_S5_107.rightTable,
        Hull16_1_S3_16_S5_108op.H,
        Hull16_1_S3_16_S5_108op.rightTable,
        oppositeTable_semigroup] using
          sameIdentityTheoryOver_of_common_basis
            SemigroupBasis.CoRoots.S5_107Family.S5_107.basisFor.oppositeReversed
            SemigroupBasis.CoRoots.S5_107Family.S5_108.oppositeBasisFor
    intro identity
    exact (sourceSelfDual identity).trans (oppositeFamily identity)
  intro identity validLeft validRight
  have leftEq :
      Hull16_1_S3_16_S5_107.G = Hull16_1_S3_16_S5_108op.G := rfl
  have validLeftSource :
      identity.SatisfiedBy Hull16_1_S3_16_S5_107.G := by
    rw [leftEq]
    exact validLeft
  have validRightSource :
      identity.SatisfiedBy Hull16_1_S3_16_S5_107.H :=
    (rightTheory identity).mpr validRight
  have derived := source identity validLeftSource validRightSource
  have basisEq :
      Hull16_1_S3_16_S5_107.publishedBasis =
        Hull16_1_S3_16_S5_108op.publishedBasis := rfl
  simpa only [basisEq] using derived

theorem hull21_right_831_eq_832 :
    Hull21_1_S5_831_S3_8.H = Hull21_1_S5_832_S3_8.H := rfl

theorem hull21_basis_831_eq_832 :
    Hull21_1_S5_831_S3_8.publishedBasis =
      Hull21_1_S5_832_S3_8.publishedBasis := rfl

theorem hull21_left_831_sameTheory_832 :
    SameIdentityTheoryOver
      Hull21_1_S5_831_S3_8.G Hull21_1_S5_832_S3_8.G Nat := by
  simpa only [Hull21_1_S5_831_S3_8.G,
    Hull21_1_S5_831_S3_8.leftTable,
    Hull21_1_S5_832_S3_8.G,
    Hull21_1_S5_832_S3_8.leftTable] using
      sameIdentityTheoryOver_of_common_basis
        SemigroupBasis.CoRoots.S5_831Family.S5_831.basisFor
        SemigroupBasis.CoRoots.S5_831Family.S5_832.basisFor

/-- A proof of the Proposition 21.1 obligation for `S5_831` also closes the
otherwise identical `S5_832` hull. -/
theorem hull21_832_of_831
    (source : Hull21_1_S5_831_S3_8.DerivationalObligation) :
    Hull21_1_S5_832_S3_8.DerivationalObligation := by
  intro identity validLeft validRight
  have validLeftSource :
      identity.SatisfiedBy Hull21_1_S5_831_S3_8.G :=
    (hull21_left_831_sameTheory_832 identity).mpr validLeft
  have validRightSource :
      identity.SatisfiedBy Hull21_1_S5_831_S3_8.H := by
    rw [hull21_right_831_eq_832]
    exact validRight
  have derived := source identity validLeftSource validRightSource
  simpa only [hull21_basis_831_eq_832] using derived

theorem hull23_left_831_eq_832 :
    Hull23_1_S3_11_S5_831.G = Hull23_1_S3_11_S5_832.G := rfl

theorem hull23_basis_831_eq_832 :
    Hull23_1_S3_11_S5_831.publishedBasis =
      Hull23_1_S3_11_S5_832.publishedBasis := rfl

theorem hull23_right_831_sameTheory_832 :
    SameIdentityTheoryOver
      Hull23_1_S3_11_S5_831.H Hull23_1_S3_11_S5_832.H Nat := by
  simpa only [Hull23_1_S3_11_S5_831.H,
    Hull23_1_S3_11_S5_831.rightTable,
    Hull23_1_S3_11_S5_832.H,
    Hull23_1_S3_11_S5_832.rightTable] using
      sameIdentityTheoryOver_of_common_basis
        SemigroupBasis.CoRoots.S5_831Family.S5_831.basisFor
        SemigroupBasis.CoRoots.S5_831Family.S5_832.basisFor

/-- A proof of the Proposition 23.1 obligation for `S5_831` also closes its
`S5_832` sibling hull. -/
theorem hull23_832_of_831
    (source : Hull23_1_S3_11_S5_831.DerivationalObligation) :
    Hull23_1_S3_11_S5_832.DerivationalObligation := by
  intro identity validLeft validRight
  have validLeftSource :
      identity.SatisfiedBy Hull23_1_S3_11_S5_831.G := by
    rw [hull23_left_831_eq_832]
    exact validLeft
  have validRightSource :
      identity.SatisfiedBy Hull23_1_S3_11_S5_831.H :=
    (hull23_right_831_sameTheory_832 identity).mpr validRight
  have derived := source identity validLeftSource validRightSource
  simpa only [hull23_basis_831_eq_832] using derived

end HullFamilyTransfers
end Order6Subdirect
end SemigroupBasis

import SemigroupBasis.CoRoots.S5_83Family
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma
import SemigroupBasis.Generated.S3_16
import SemigroupBasis.Subdirect

/-!
# The six-law `S3_16` / `S5_83` intersection

This is the shared syntax layer for the order-six roots `S6_3373`,
`S6_3378`, and `S6_6177`.  The displayed system is

* `xx = xxx`;
* `xxyx = xyx`;
* `xxyz = xyz`;
* `xyx = xyy`;
* `xyzx = xyzxx`;
* `xyzx = xyzyx`.

The companion normal-form module proves unrestricted completeness for both
right factors `S5_83` and `S5_84`.  This file keeps the generated basis as the
literal theorem surface, proves factor soundness by finite reflection, and
records the block rewrites used by that normalizer.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Direct

open SemigroupBasis
open SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyz : Word Nat := w 0 [0, 1, 2]
def xyz : Word Nat := w 0 [1, 2]
def xyy : Word Nat := w 0 [1, 1]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xyzxx : Word Nat := w 0 [1, 2, 0, 0]
def xyzyx : Word Nat := w 0 [1, 2, 1, 0]

def powerLaw : Identity Nat := Identity.mk xx xxx
def leftDeletionLaw : Identity Nat := Identity.mk xxyx xyx
def protectedDeletionLaw : Identity Nat := Identity.mk xxyz xyz
def terminalTransferLaw : Identity Nat := Identity.mk xyx xyy
def finalExpansionLaw : Identity Nat := Identity.mk xyzx xyzxx
def guardedRotationLaw : Identity Nat := Identity.mk xyzx xyzyx

/-- Exact generated basis, SHA-256
`2788f421bc5802f4ab428021363f6d91022992778c60c26d357126cf59b2d45f`. -/
abbrev basis : List (Identity Nat) :=
  Sigma_2788f421bc5802f4.basis

def candidateBasisSHA256 : String :=
  Sigma_2788f421bc5802f4.sha256

private def detectorToFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem modelsS3_16 :
    Models SemigroupBasis.Generated.S3_16.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_16.table basis detectorToFinThree
      (by decide)

theorem modelsS5_83 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup
      basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_83.table
      basis detectorToFinThree (by decide)

theorem modelsS5_84 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup
      basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_84.table
      basis detectorToFinThree (by decide)

private def substituteThree
    (first second third : Word Nat) : Nat -> Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

theorem derivesPowerLaw : Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) (by decide)

theorem derivesLeftDeletionLaw : Derives basis xxyx xyx :=
  Derives.fromBasis (e := leftDeletionLaw) (by decide)

theorem derivesProtectedDeletionLaw : Derives basis xxyz xyz :=
  Derives.fromBasis (e := protectedDeletionLaw) (by decide)

theorem derivesTerminalTransferLaw : Derives basis xyx xyy :=
  Derives.fromBasis (e := terminalTransferLaw) (by decide)

theorem derivesFinalExpansionLaw : Derives basis xyzx xyzxx :=
  Derives.fromBasis (e := finalExpansionLaw) (by decide)

theorem derivesGuardedRotationLaw : Derives basis xyzx xyzyx :=
  Derives.fromBasis (e := guardedRotationLaw) (by decide)

/-- Expand two consecutive copies of a nonempty block to three. -/
theorem derivesSquareExpansion (block : Word Nat) :
    Derives basis (block ++ block) ((block ++ block) ++ block) := by
  have instantiated :=
    Derives.subst derivesPowerLaw
      (substituteThree block block block)
  simpa [powerLaw, xx, xxx, w, substituteThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using instantiated

/-- Delete the first of two copies when a return to that block follows. -/
theorem derivesLeftDeletion (left middle : Word Nat) :
    Derives basis (((left ++ left) ++ middle) ++ left)
      ((left ++ middle) ++ left) := by
  have instantiated :=
    Derives.subst derivesLeftDeletionLaw
      (substituteThree left middle middle)
  simpa [leftDeletionLaw, xxyx, xyx, w, substituteThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using instantiated

/-- Delete a doubled block while two nonempty blocks remain to its right. -/
theorem derivesProtectedDeletion
    (block firstGuard secondGuard : Word Nat) :
    Derives basis
      (((block ++ block) ++ firstGuard) ++ secondGuard)
      ((block ++ firstGuard) ++ secondGuard) := by
  have instantiated :=
    Derives.subst derivesProtectedDeletionLaw
      (substituteThree block firstGuard secondGuard)
  simpa [protectedDeletionLaw, xxyz, xyz, w, substituteThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      instantiated

/-- Transfer a returned first block into a second copy of the middle block. -/
theorem derivesTerminalTransfer (left middle : Word Nat) :
    Derives basis ((left ++ middle) ++ left)
      ((left ++ middle) ++ middle) := by
  have instantiated :=
    Derives.subst derivesTerminalTransferLaw
      (substituteThree left middle middle)
  simpa [terminalTransferLaw, xyx, xyy, w, substituteThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      instantiated

/-- Duplicate a final returned block after two nonempty guard blocks. -/
theorem derivesFinalExpansion
    (returned firstGuard secondGuard : Word Nat) :
    Derives basis
      (((returned ++ firstGuard) ++ secondGuard) ++ returned)
      ((((returned ++ firstGuard) ++ secondGuard) ++ returned) ++ returned) := by
  have instantiated :=
    Derives.subst derivesFinalExpansionLaw
      (substituteThree returned firstGuard secondGuard)
  simpa [finalExpansionLaw, xyzx, xyzxx, w, substituteThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      instantiated

/-- Insert the middle guard before a returned first block. -/
theorem derivesGuardedRotation
    (firstGuard secondGuard middle : Word Nat) :
    Derives basis
      ((firstGuard ++ secondGuard) ++ (middle ++ firstGuard))
      ((firstGuard ++ secondGuard) ++ (middle ++ (secondGuard ++ firstGuard))) := by
  have instantiated :=
    Derives.subst derivesGuardedRotationLaw
      (substituteThree firstGuard secondGuard middle)
  simpa [guardedRotationLaw, xyzx, xyzyx, w, substituteThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      instantiated

/-- The derived endpoint expansion `xyx = xyxx`. -/
theorem derivesRightEndpointExpansion (left middle : Word Nat) :
    Derives basis ((left ++ middle) ++ left)
      (((left ++ middle) ++ left) ++ left) := by
  have step1 := (derivesLeftDeletion left middle).symm
  have step2 :=
    derivesFinalExpansion left left middle
  have step3 :=
    Derives.appendRight (derivesLeftDeletion left middle) left
  exact step1.trans (by
    simpa [Word.append_assoc] using step2.trans step3)

/-- Interleave two square blocks: `xxyy = xyxy`. -/
theorem derivesSquareInterleave (left right : Word Nat) :
    Derives basis ((left ++ left) ++ (right ++ right))
      ((left ++ right) ++ (left ++ right)) := by
  have expandRight :=
    Derives.prepend (left ++ left) (derivesSquareExpansion right)
  have deleteLeft :=
    derivesProtectedDeletion left right (right ++ right)
  have transfer :=
    Derives.appendRight (derivesTerminalTransfer left right).symm right
  have expanded :
      Derives basis
        ((left ++ left) ++ (right ++ right))
        (((left ++ left) ++ right) ++ (right ++ right)) := by
    simpa [Word.append_assoc] using expandRight
  have finished :
      Derives basis
        (((left ++ left) ++ right) ++ (right ++ right))
        ((left ++ right) ++ (left ++ right)) := by
    have deleted :
        Derives basis
          (((left ++ left) ++ right) ++ (right ++ right))
          ((left ++ right) ++ (right ++ right)) := by
      simpa [Word.append_assoc] using deleteLeft
    have transferred :
        Derives basis
          ((left ++ right) ++ (right ++ right))
          ((left ++ right) ++ (left ++ right)) := by
      simpa [Word.append_assoc] using transfer
    exact deleted.trans transferred
  exact expanded.trans finished

/-- Delete a returned block before two protected nonempty suffix blocks. -/
theorem derivesRegularContractionBeforeTwo
    (left middle firstGuard secondGuard : Word Nat) :
    Derives basis
      ((((left ++ middle) ++ left) ++ firstGuard) ++ secondGuard)
      (((left ++ middle) ++ firstGuard) ++ secondGuard) := by
  have transfer :=
    Derives.appendRight
      (Derives.appendRight
        (derivesTerminalTransfer left middle) firstGuard)
      secondGuard
  have deleteMiddle :=
    Derives.prepend left
      (derivesProtectedDeletion middle firstGuard secondGuard)
  exact transfer.trans (by
    simpa [Word.append_assoc] using deleteMiddle)

end SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Direct

import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Generated.S3_16

/-!
# The literal B10 basis for the `S3_16 x S5_804` intersection

This module records the accepted ten identities for L2D delivery d024 in
their authenticated order.  It also supplies independent exhaustive model
checks for both selected factors and the ten direct block-substitution
instances consumed by the endpoint-cap and fixed-final replay modules.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyx : Word Nat := w 0 [1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xyxyx : Word Nat := w 0 [1, 0, 1, 0]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xyxzy : Word Nat := w 0 [1, 0, 2, 1]
def xyzxy : Word Nat := w 0 [1, 2, 0, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def xyzyx : Word Nat := w 0 [1, 2, 1, 0]
def xyzzx : Word Nat := w 0 [1, 2, 2, 0]

/-- Law 1: `xx = xxx`. -/
def powerLaw : Identity Nat := Identity.mk xx xxx

/-- Law 2: `xxyx = xyx`. -/
def leftContractionLaw : Identity Nat := Identity.mk xxyx xyx

/-- Law 3: `xyx = xyxx`. -/
def rightExpansionLaw : Identity Nat := Identity.mk xyx xyxx

/-- Law 4: `xyx = xyxyx`. -/
def alternatingExpansionLaw : Identity Nat := Identity.mk xyx xyxyx

/-- Law 5: `xyx = xyyx`. -/
def middleDuplicationLaw : Identity Nat := Identity.mk xyx xyyx

/-- Law 6: `xyxzx = xyzx`. -/
def crossingContractionLaw : Identity Nat := Identity.mk xyxzx xyzx

/-- Law 7: `xyxzy = xyzxy`. -/
def finalCrossingShiftLaw : Identity Nat := Identity.mk xyxzy xyzxy

/-- Law 8: `xyyzx = xyzx`. -/
def nestedDeletionLaw : Identity Nat := Identity.mk xyyzx xyzx

/-- Law 9: `xyzx = xyzyx`. -/
def finalInsertionLaw : Identity Nat := Identity.mk xyzx xyzyx

/-- Law 10: `xyzx = xyzzx`. -/
def finalDuplicationLaw : Identity Nat := Identity.mk xyzx xyzzx

/-- The accepted direct B10 basis in its authenticated displayed order. -/
def B10 : List (Identity Nat) :=
  [powerLaw, leftContractionLaw, rightExpansionLaw,
    alternatingExpansionLaw, middleDuplicationLaw,
    crossingContractionLaw, finalCrossingShiftLaw,
    nestedDeletionLaw, finalInsertionLaw, finalDuplicationLaw]

/-- List-level derivability specialized to the literal B10 basis. -/
abbrev B10ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives B10

theorem B10_length : B10.length = 10 := by
  decide

/-- Recorded SHA-256 of the literal ten-law displayed list. -/
def displayedBasisSHA256 : String :=
  "86a233ce9b903e4df1c4da10183be308432fefdbd9dd753968b369b766c85f59"

theorem displayedBasisSHA256_exact :
    displayedBasisSHA256 =
      "86a233ce9b903e4df1c4da10183be308432fefdbd9dd753968b369b766c85f59" :=
  rfl

/-! ## Independent finite-table soundness -/

/-- B10 uses only the displayed variable names `0`, `1`, and `2`.
`FiniteCertificate.checkModels` checks the exact round trip for every law. -/
private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem s3_16_models_checked :
    FiniteCertificate.checkModels
      SemigroupBasis.Generated.S3_16.table B10 toFinThree = true := by
  decide

private theorem s5_804_models_checked :
    FiniteCertificate.checkModels
      SemigroupBasis.Generated.Catalogue.S5_804.table B10 toFinThree = true := by
  decide

/-- Every literal B10 law is valid in the direct `S3_16` factor. -/
theorem s3_16_models :
    Models SemigroupBasis.Generated.S3_16.table.semigroup B10 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_16.table B10 toFinThree
      s3_16_models_checked

/-- Every literal B10 law is valid in the direct `S5_804` factor. -/
theorem s5_804_models :
    Models SemigroupBasis.Generated.Catalogue.S5_804.table.semigroup B10 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_804.table B10 toFinThree
      s5_804_models_checked

/-! ## Literal B10 block instances -/

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

private theorem basisPowerLaw : Derives B10 xx xxx :=
  Derives.fromBasis (e := powerLaw) (by simp [B10])

private theorem basisLeftContractionLaw : Derives B10 xxyx xyx :=
  Derives.fromBasis (e := leftContractionLaw) (by simp [B10])

private theorem basisRightExpansionLaw : Derives B10 xyx xyxx :=
  Derives.fromBasis (e := rightExpansionLaw) (by simp [B10])

private theorem basisAlternatingExpansionLaw : Derives B10 xyx xyxyx :=
  Derives.fromBasis (e := alternatingExpansionLaw) (by simp [B10])

private theorem basisMiddleDuplicationLaw : Derives B10 xyx xyyx :=
  Derives.fromBasis (e := middleDuplicationLaw) (by simp [B10])

private theorem basisCrossingContractionLaw : Derives B10 xyxzx xyzx :=
  Derives.fromBasis (e := crossingContractionLaw) (by simp [B10])

private theorem basisFinalCrossingShiftLaw : Derives B10 xyxzy xyzxy :=
  Derives.fromBasis (e := finalCrossingShiftLaw) (by simp [B10])

private theorem basisNestedDeletionLaw : Derives B10 xyyzx xyzx :=
  Derives.fromBasis (e := nestedDeletionLaw) (by simp [B10])

private theorem basisFinalInsertionLaw : Derives B10 xyzx xyzyx :=
  Derives.fromBasis (e := finalInsertionLaw) (by simp [B10])

private theorem basisFinalDuplicationLaw : Derives B10 xyzx xyzzx :=
  Derives.fromBasis (e := finalDuplicationLaw) (by simp [B10])

/-- Direct block substitution in law 1, `xx = xxx`. -/
theorem derivesPowerExpansion (x : Word Nat) :
    Derives B10 (x ++ x) ((x ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisPowerLaw (instantiateThreeWords x x x)
  simpa [powerLaw, xx, xxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in law 2, `xxyx = xyx`. -/
theorem derivesLeftContraction (x y : Word Nat) :
    Derives B10 (((x ++ x) ++ y) ++ x) ((x ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisLeftContractionLaw
      (instantiateThreeWords x y y)
  simpa [leftContractionLaw, xxyx, xyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in law 3, `xyx = xyxx`. -/
theorem derivesRightExpansion (x y : Word Nat) :
    Derives B10 ((x ++ y) ++ x) (((x ++ y) ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisRightExpansionLaw
      (instantiateThreeWords x y y)
  simpa [rightExpansionLaw, xyx, xyxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in law 4, `xyx = xyxyx`. -/
theorem derivesAlternatingExpansion (x y : Word Nat) :
    Derives B10 ((x ++ y) ++ x)
      ((((x ++ y) ++ x) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisAlternatingExpansionLaw
      (instantiateThreeWords x y y)
  simpa [alternatingExpansionLaw, xyx, xyxyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Direct block substitution in law 5, `xyx = xyyx`. -/
theorem derivesMiddleDuplication (x y : Word Nat) :
    Derives B10 ((x ++ y) ++ x) (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisMiddleDuplicationLaw
      (instantiateThreeWords x y y)
  simpa [middleDuplicationLaw, xyx, xyyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in law 6, `xyxzx = xyzx`. -/
theorem derivesCrossingContraction (x y z : Word Nat) :
    Derives B10 ((((x ++ y) ++ x) ++ z) ++ x)
      (((x ++ y) ++ z) ++ x) := by
  have substituted :=
    Derives.subst basisCrossingContractionLaw
      (instantiateThreeWords x y z)
  simpa [crossingContractionLaw, xyxzx, xyzx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Direct block substitution in law 7, `xyxzy = xyzxy`. -/
theorem derivesFinalCrossingShift (x y z : Word Nat) :
    Derives B10 ((((x ++ y) ++ x) ++ z) ++ y)
      ((((x ++ y) ++ z) ++ x) ++ y) := by
  have substituted :=
    Derives.subst basisFinalCrossingShiftLaw
      (instantiateThreeWords x y z)
  simpa [finalCrossingShiftLaw, xyxzy, xyzxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Direct block substitution in law 8, `xyyzx = xyzx`. -/
theorem derivesNestedDeletion (x y z : Word Nat) :
    Derives B10 ((((x ++ y) ++ y) ++ z) ++ x)
      (((x ++ y) ++ z) ++ x) := by
  have substituted :=
    Derives.subst basisNestedDeletionLaw
      (instantiateThreeWords x y z)
  simpa [nestedDeletionLaw, xyyzx, xyzx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in law 9, `xyzx = xyzyx`. -/
theorem derivesFinalInsertion (x y z : Word Nat) :
    Derives B10 (((x ++ y) ++ z) ++ x)
      ((((x ++ y) ++ z) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisFinalInsertionLaw
      (instantiateThreeWords x y z)
  simpa [finalInsertionLaw, xyzx, xyzyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in law 10, `xyzx = xyzzx`. -/
theorem derivesFinalDuplication (x y z : Word Nat) :
    Derives B10 (((x ++ y) ++ z) ++ x)
      ((((x ++ y) ++ z) ++ z) ++ x) := by
  have substituted :=
    Derives.subst basisFinalDuplicationLaw
      (instantiateThreeWords x y z)
  simpa [finalDuplicationLaw, xyzx, xyzzx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

end SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial

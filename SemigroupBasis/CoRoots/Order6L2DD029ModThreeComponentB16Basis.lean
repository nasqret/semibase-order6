import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S4_124
import SemigroupBasis.Generated.S4_70

/-!
# The literal B16 basis for the `S4_124 x S4_70` intersection

This module records the accepted sixteen identities for L2D delivery d029 in
their authenticated order.  It also supplies independent exhaustive model
checks for the two direct factors and direct block-substitution instances of
all sixteen laws.  No bounded-search derivation is imported here.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

namespace SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

def xx : Word Nat := w 0 [0]
def xxxxx : Word Nat := w 0 [0, 0, 0, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def yxyyy : Word Nat := w 1 [0, 1, 1, 1]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyxy : Word Nat := w 0 [0, 1, 0, 1]
def yxxxy : Word Nat := w 1 [0, 0, 0, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def yxxy : Word Nat := w 1 [0, 0, 1]
def xyxzy : Word Nat := w 0 [1, 0, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def yxxzy : Word Nat := w 1 [0, 0, 2, 1]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def aaabab : Word Nat := w 0 [0, 0, 1, 0, 1]
def bab : Word Nat := w 1 [0, 1]
def aba : Word Nat := w 0 [1, 0]
def aaaaba : Word Nat := w 0 [0, 0, 0, 1, 0]
def cabccc : Word Nat := w 2 [0, 1, 2, 2, 2]
def babbcb : Word Nat := w 1 [0, 1, 1, 2, 1]
def dacbd : Word Nat := w 3 [0, 2, 1, 3]
def dabcd : Word Nat := w 3 [0, 1, 2, 3]
def abcda : Word Nat := w 0 [1, 2, 3, 0]
def abdca : Word Nat := w 0 [1, 3, 2, 0]
def cabdc : Word Nat := w 2 [0, 1, 3, 2]
def cadbc : Word Nat := w 2 [0, 3, 1, 2]
def bacdb : Word Nat := w 1 [0, 2, 3, 1]
def badcb : Word Nat := w 1 [0, 3, 2, 1]

/-- Law 1: `xx = xxxxx`. -/
def powerLaw : Identity Nat := Identity.mk xx xxxxx

/-- Law 2: `xxxyx = yxyyy`. -/
def tripleTransferLaw : Identity Nat := Identity.mk xxxyx yxyyy

/-- Law 3: `xxyx = xyxx`. -/
def endpointTransferLaw : Identity Nat := Identity.mk xxyx xyxx

/-- Law 4: `xxyxy = yxxxy`. -/
def tripleHeadSwitchLaw : Identity Nat := Identity.mk xxyxy yxxxy

/-- Law 5: `xyxy = xyyx`. -/
def squareFinalLaw : Identity Nat := Identity.mk xyxy xyyx

/-- Law 6: `xyxy = yxxy`. -/
def squareInitialLaw : Identity Nat := Identity.mk xyxy yxxy

/-- Law 7: `xyxzy = xyyzx`. -/
def attachmentXYYZXLaw : Identity Nat := Identity.mk xyxzy xyyzx

/-- Law 8: `xyxzy = yxxzy`. -/
def attachmentYXXZYLaw : Identity Nat := Identity.mk xyxzy yxxzy

/-- Law 9: `xyzx = xzyx`. -/
def anchoredSwapLaw : Identity Nat := Identity.mk xyzx xzyx

/-- Law 10: `aaabab = bab`. -/
def unaryAnchorContractionLaw : Identity Nat := Identity.mk aaabab bab

/-- Law 11: `aba = aaaaba`. -/
def unaryAnchorExpansionLaw : Identity Nat := Identity.mk aba aaaaba

/-- Law 12: `cabccc = babbcb`. -/
def threeLetterAnchorRepairLaw : Identity Nat := Identity.mk cabccc babbcb

/-- Law 13: `dacbd = dabcd`. -/
def longInteriorDACBDLaw : Identity Nat := Identity.mk dacbd dabcd

/-- Law 14: `abcda = abdca`. -/
def longInteriorABCDALaw : Identity Nat := Identity.mk abcda abdca

/-- Law 15: `cabdc = cadbc`. -/
def longInteriorCABDCLaw : Identity Nat := Identity.mk cabdc cadbc

/-- Law 16: `bacdb = badcb`. -/
def longInteriorBACDBLaw : Identity Nat := Identity.mk bacdb badcb

/-- The accepted direct B16 basis in its authenticated displayed order. -/
def B16 : List (Identity Nat) :=
  [powerLaw, tripleTransferLaw, endpointTransferLaw,
    tripleHeadSwitchLaw, squareFinalLaw, squareInitialLaw,
    attachmentXYYZXLaw, attachmentYXXZYLaw, anchoredSwapLaw,
    unaryAnchorContractionLaw, unaryAnchorExpansionLaw,
    threeLetterAnchorRepairLaw, longInteriorDACBDLaw,
    longInteriorABCDALaw, longInteriorCABDCLaw,
    longInteriorBACDBLaw]

/-- List-level derivability specialized to the literal B16 basis. -/
abbrev B16ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives B16

theorem B16_length : B16.length = 16 := by
  decide

/-- Recorded SHA-256 of the literal sixteen-law displayed list. -/
def displayedBasisSHA256 : String :=
  "b07f6a78d49156d1f94c23451b6dd52ef448b2a5158cb108cbd7bf928781d65e"

theorem displayedBasisSHA256_exact :
    displayedBasisSHA256 =
      "b07f6a78d49156d1f94c23451b6dd52ef448b2a5158cb108cbd7bf928781d65e" :=
  rfl

/-! ## Independent finite-table soundness -/

/-- B16 uses exactly the displayed variable names `0`, `1`, `2`, and `3`.
The finite checker also verifies their exact round trip in every law. -/
private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private theorem s4_124_models_checked :
    FiniteCertificate.checkModels
      SemigroupBasis.Generated.S4_124.table B16 toFinFour = true := by
  decide

private theorem s4_70_models_checked :
    FiniteCertificate.checkModels
      SemigroupBasis.Generated.S4_70.table B16 toFinFour = true := by
  decide

/-- Every literal B16 law is valid in the direct `S4_124` factor. -/
theorem s4_124_models :
    Models SemigroupBasis.Generated.S4_124.table.semigroup B16 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_124.table B16 toFinFour
      s4_124_models_checked

/-- Every literal B16 law is valid in the direct `S4_70` factor. -/
theorem s4_70_models :
    Models SemigroupBasis.Generated.S4_70.table.semigroup B16 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_70.table B16 toFinFour
      s4_70_models_checked

/-! ## Literal B16 block instances -/

private def instantiateFourWords
    (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | n + 4 => Word.singleton (n + 4)

/-- Direct substitution of arbitrary nonempty words into a literal B16 law. -/
theorem derivesBasisSubstitution
    (identity : Identity Nat) (member : identity ∈ B16)
    (substitution : Nat → Word Nat) :
    Derives B16
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  Derives.subst (Derives.fromBasis member) substitution

/-- Direct block substitution in law 1, `xx = xxxxx`. -/
theorem derivesPowerExpansion (x : Word Nat) :
    Derives B16 (x ++ x)
      (((((x ++ x) ++ x) ++ x) ++ x)) := by
  have substituted :=
    derivesBasisSubstitution powerLaw (by simp [B16])
      (instantiateFourWords x x x x)
  simpa [powerLaw, xx, xxxxx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in law 2, `xxxyx = yxyyy`. -/
theorem derivesTripleTransfer (x y : Word Nat) :
    Derives B16 ((((x ++ x) ++ x) ++ y) ++ x)
      ((((y ++ x) ++ y) ++ y) ++ y) := by
  have substituted :=
    derivesBasisSubstitution tripleTransferLaw (by simp [B16])
      (instantiateFourWords x y y y)
  simpa [tripleTransferLaw, xxxyx, yxyyy, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in law 3, `xxyx = xyxx`. -/
theorem derivesEndpointTransfer (x y : Word Nat) :
    Derives B16 (((x ++ x) ++ y) ++ x)
      (((x ++ y) ++ x) ++ x) := by
  have substituted :=
    derivesBasisSubstitution endpointTransferLaw (by simp [B16])
      (instantiateFourWords x y y y)
  simpa [endpointTransferLaw, xxyx, xyxx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in law 4, `xxyxy = yxxxy`. -/
theorem derivesTripleHeadSwitch (x y : Word Nat) :
    Derives B16 ((((x ++ x) ++ y) ++ x) ++ y)
      ((((y ++ x) ++ x) ++ x) ++ y) := by
  have substituted :=
    derivesBasisSubstitution tripleHeadSwitchLaw (by simp [B16])
      (instantiateFourWords x y y y)
  simpa [tripleHeadSwitchLaw, xxyxy, yxxxy, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in law 5, `xyxy = xyyx`. -/
theorem derivesSquareFinalSwitch (x y : Word Nat) :
    Derives B16 (((x ++ y) ++ x) ++ y)
      (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    derivesBasisSubstitution squareFinalLaw (by simp [B16])
      (instantiateFourWords x y y y)
  simpa [squareFinalLaw, xyxy, xyyx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in law 6, `xyxy = yxxy`. -/
theorem derivesSquareInitialSwitch (x y : Word Nat) :
    Derives B16 (((x ++ y) ++ x) ++ y)
      (((y ++ x) ++ x) ++ y) := by
  have substituted :=
    derivesBasisSubstitution squareInitialLaw (by simp [B16])
      (instantiateFourWords x y y y)
  simpa [squareInitialLaw, xyxy, yxxy, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in law 7, `xyxzy = xyyzx`. -/
theorem derivesAttachmentXYYZX (x y z : Word Nat) :
    Derives B16 ((((x ++ y) ++ x) ++ z) ++ y)
      ((((x ++ y) ++ y) ++ z) ++ x) := by
  have substituted :=
    derivesBasisSubstitution attachmentXYYZXLaw (by simp [B16])
      (instantiateFourWords x y z z)
  simpa [attachmentXYYZXLaw, xyxzy, xyyzx, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Direct block substitution in law 8, `xyxzy = yxxzy`. -/
theorem derivesAttachmentYXXZY (x y z : Word Nat) :
    Derives B16 ((((x ++ y) ++ x) ++ z) ++ y)
      ((((y ++ x) ++ x) ++ z) ++ y) := by
  have substituted :=
    derivesBasisSubstitution attachmentYXXZYLaw (by simp [B16])
      (instantiateFourWords x y z z)
  simpa [attachmentYXXZYLaw, xyxzy, yxxzy, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Direct block substitution in law 9, `xyzx = xzyx`. -/
theorem derivesAnchoredSwap (x y z : Word Nat) :
    Derives B16 (((x ++ y) ++ z) ++ x)
      (((x ++ z) ++ y) ++ x) := by
  have substituted :=
    derivesBasisSubstitution anchoredSwapLaw (by simp [B16])
      (instantiateFourWords x y z z)
  simpa [anchoredSwapLaw, xyzx, xzyx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in law 10, `aaabab = bab`. -/
theorem derivesUnaryAnchorContraction (a b : Word Nat) :
    Derives B16 (((((a ++ a) ++ a) ++ b) ++ a) ++ b)
      ((b ++ a) ++ b) := by
  have substituted :=
    derivesBasisSubstitution unaryAnchorContractionLaw (by simp [B16])
      (instantiateFourWords a b b b)
  simpa [unaryAnchorContractionLaw, aaabab, bab, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Direct block substitution in law 11, `aba = aaaaba`. -/
theorem derivesUnaryAnchorExpansion (a b : Word Nat) :
    Derives B16 ((a ++ b) ++ a)
      (((((a ++ a) ++ a) ++ a) ++ b) ++ a) := by
  have substituted :=
    derivesBasisSubstitution unaryAnchorExpansionLaw (by simp [B16])
      (instantiateFourWords a b b b)
  simpa [unaryAnchorExpansionLaw, aba, aaaaba, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Direct block substitution in law 12, `cabccc = babbcb`. -/
theorem derivesThreeLetterAnchorRepair (a b c : Word Nat) :
    Derives B16 (((((c ++ a) ++ b) ++ c) ++ c) ++ c)
      (((((b ++ a) ++ b) ++ b) ++ c) ++ b) := by
  have substituted :=
    derivesBasisSubstitution threeLetterAnchorRepairLaw (by simp [B16])
      (instantiateFourWords a b c c)
  simpa [threeLetterAnchorRepairLaw, cabccc, babbcb, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Direct block substitution in law 13, `dacbd = dabcd`. -/
theorem derivesLongInteriorDACBD
    (a b c d : Word Nat) :
    Derives B16 ((((d ++ a) ++ c) ++ b) ++ d)
      ((((d ++ a) ++ b) ++ c) ++ d) := by
  have substituted :=
    derivesBasisSubstitution longInteriorDACBDLaw (by simp [B16])
      (instantiateFourWords a b c d)
  simpa [longInteriorDACBDLaw, dacbd, dabcd, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Direct block substitution in law 14, `abcda = abdca`. -/
theorem derivesLongInteriorABCDA
    (a b c d : Word Nat) :
    Derives B16 ((((a ++ b) ++ c) ++ d) ++ a)
      ((((a ++ b) ++ d) ++ c) ++ a) := by
  have substituted :=
    derivesBasisSubstitution longInteriorABCDALaw (by simp [B16])
      (instantiateFourWords a b c d)
  simpa [longInteriorABCDALaw, abcda, abdca, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Direct block substitution in law 15, `cabdc = cadbc`. -/
theorem derivesLongInteriorCABDC
    (a b c d : Word Nat) :
    Derives B16 ((((c ++ a) ++ b) ++ d) ++ c)
      ((((c ++ a) ++ d) ++ b) ++ c) := by
  have substituted :=
    derivesBasisSubstitution longInteriorCABDCLaw (by simp [B16])
      (instantiateFourWords a b c d)
  simpa [longInteriorCABDCLaw, cabdc, cadbc, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Direct block substitution in law 16, `bacdb = badcb`. -/
theorem derivesLongInteriorBACDB
    (a b c d : Word Nat) :
    Derives B16 ((((b ++ a) ++ c) ++ d) ++ b)
      ((((b ++ a) ++ d) ++ c) ++ b) := by
  have substituted :=
    derivesBasisSubstitution longInteriorBACDBLaw (by simp [B16])
      (instantiateFourWords a b c d)
  simpa [longInteriorBACDBLaw, bacdb, badcb, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

end SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16

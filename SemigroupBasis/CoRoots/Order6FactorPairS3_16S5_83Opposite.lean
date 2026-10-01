import SemigroupBasis.CoRoots.S5_83Family
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_16
import SemigroupBasis.Subdirect

/-!
# The four-law `S3_16` / `S5_83^op` intersection

The displayed system is the canonical packet basis for the order-six roots
`S6_3811`, `S6_6434`, `S6_3824`, and `S6_6441`:

* `xx = xxx`;
* `xxy = xxyy`;
* `xxy = xyx`;
* `xyz = xyzz`.

This file records the syntax, factor soundness, and the contextual contractions
used by the shared unrestricted normalizer.  Completeness is proved in the
companion normal-form module.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Opposite

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyx : Word Nat := w 0 [1, 0]
def xyz : Word Nat := w 0 [1, 2]
def xyzz : Word Nat := w 0 [1, 2, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def doubledFinalLaw : Identity Nat := ⟨xxy, xxyy⟩
def returnLaw : Identity Nat := ⟨xxy, xyx⟩
def longFinalInsertionLaw : Identity Nat := ⟨xyz, xyzz⟩

/-- Exact four-law packet basis, SHA-256
`0ede399c0125f2e3ef9f4c40866cfb67adf7cbf0b3af47ffe841e8999b25e95f`. -/
def basis : List (Identity Nat) :=
  [powerLaw, doubledFinalLaw, returnLaw, longFinalInsertionLaw]

def candidateBasisUpToOppositeSHA256 : String :=
  "0ede399c0125f2e3ef9f4c40866cfb67adf7cbf0b3af47ffe841e8999b25e95f"

private def detectorToFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def oppositeFiniteTable (table : FiniteTable) : FiniteTable where
  order := table.order
  mul := fun left right => table.mul right left
  assoc := fun left middle right =>
    (table.assoc right middle left).symm

private theorem oppositeFiniteTable_semigroup (table : FiniteTable) :
    (oppositeFiniteTable table).semigroup =
      table.semigroup.opposite := by
  rfl

theorem modelsS3_16 :
    Models SemigroupBasis.Generated.S3_16.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_16.table basis detectorToFinThree
      (by decide)

theorem modelsS5_83Opposite :
    Models
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite
      basis := by
  rw [← oppositeFiniteTable_semigroup]
  exact FiniteCertificate.checkModels_sound
    (oppositeFiniteTable
      SemigroupBasis.Generated.Catalogue.S5_83.table)
    basis detectorToFinThree (by decide)

private def instantiateThreeWords
    (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

theorem derivesPowerLaw : Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

theorem derivesDoubledFinalLaw : Derives basis xxy xxyy :=
  Derives.fromBasis (e := doubledFinalLaw) (by simp [basis])

theorem derivesReturnLaw : Derives basis xxy xyx :=
  Derives.fromBasis (e := returnLaw) (by simp [basis])

theorem derivesLongFinalInsertionLaw : Derives basis xyz xyzz :=
  Derives.fromBasis (e := longFinalInsertionLaw) (by simp [basis])

/-- Contract three consecutive copies of any nonempty block to two. -/
theorem derivesThreeToTwo (block : Word Nat) :
    Derives basis ((block ++ block) ++ block) (block ++ block) := by
  have substituted :=
    Derives.subst derivesPowerLaw.symm
      (instantiateThreeWords block block block)
  simpa [powerLaw, xx, xxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Gather a later block next to its first occurrence. -/
theorem derivesGather (block middle : Word Nat) :
    Derives basis ((block ++ middle) ++ block)
      ((block ++ block) ++ middle) := by
  have substituted :=
    Derives.subst derivesReturnLaw.symm
      (instantiateThreeWords block middle middle)
  simpa [returnLaw, xxy, xyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Remove a doubled final block after a doubled nonempty prefix. -/
theorem derivesDoubledFinalContraction (initial final : Word Nat) :
    Derives basis
      ((initial ++ initial) ++ (final ++ final))
      ((initial ++ initial) ++ final) := by
  have substituted :=
    Derives.subst derivesDoubledFinalLaw.symm
      (instantiateThreeWords initial final final)
  simpa [doubledFinalLaw, xxy, xxyy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Remove a doubled final block after any two nonempty prefix blocks. -/
theorem derivesLongFinalContraction
    (first second final : Word Nat) :
    Derives basis
      (((first ++ second) ++ final) ++ final)
      ((first ++ second) ++ final) := by
  have substituted :=
    Derives.subst derivesLongFinalInsertionLaw.symm
      (instantiateThreeWords first second final)
  simpa [longFinalInsertionLaw, xyz, xyzz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

end SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Opposite

import SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16Basis

/-!
# Literal-B16 mod-three anchor-switch leaves for d029

This module isolates the nine endpoint-retarget leaves needed after an
envelope interior has been reduced modulo three.  If `A` is the old endpoint
and `B` the new endpoint, the old interior multiplicity is `0`, `1`, or `2`
and the supported new multiplicity is `1`, `2`, or `3`.  The forced target
interior multiplicities are

* old: `0 -> 2`, `1 -> 3`, `2 -> 1`;
* new: `1 -> 2`, `2 -> 0`, `3 -> 1`.

Every proof below is a concrete composition of literal B16 substitutions,
symmetry, and word/list contexts.  In particular, this module imports only
the B16 basis surface and reuses no `S5_442` derivation theorem.
-/

namespace SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16

open SemigroupBasis

/-! ## Empty-trailing word cores -/

/-- Cell `(0,1)`: `ABA -> BBBAAB`. -/
theorem derivesAnchorSwitch01Core (old new : Word Nat) :
    Derives B16 ((old ++ new) ++ old)
      (((((new ++ new) ++ new) ++ old) ++ old) ++ new) := by
  have expand :
      Derives B16 ((old ++ new) ++ old)
        (((((new ++ new) ++ new) ++ old) ++ new) ++ old) := by
    simpa [Word.append_assoc] using
      (derivesUnaryAnchorContraction new old).symm
  have finish :
      Derives B16
        (((((new ++ new) ++ new) ++ old) ++ new) ++ old)
        (((((new ++ new) ++ new) ++ old) ++ old) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.prepend (new ++ new)
        (derivesSquareFinalSwitch new old)
  exact expand.trans finish

/-- Cell `(0,2)`: `ABBA -> BAAB`. -/
theorem derivesAnchorSwitch02Core (old new : Word Nat) :
    Derives B16 (((old ++ new) ++ new) ++ old)
      (((new ++ old) ++ old) ++ new) := by
  exact
    (derivesSquareFinalSwitch old new).symm.trans
      (derivesSquareInitialSwitch old new)

/-- Cell `(0,3)`: `ABBBA -> BAABB`. -/
theorem derivesAnchorSwitch03Core (old new : Word Nat) :
    Derives B16 ((((old ++ new) ++ new) ++ new) ++ old)
      ((((new ++ old) ++ old) ++ new) ++ new) := by
  have openEnvelope :
      Derives B16 ((((old ++ new) ++ new) ++ new) ++ old)
        ((((old ++ new) ++ old) ++ new) ++ new) := by
    simpa [Word.append_assoc] using
      (derivesAttachmentXYYZX old new new).symm
  have switch :
      Derives B16 ((((old ++ new) ++ old) ++ new) ++ new)
        ((((new ++ old) ++ old) ++ new) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesSquareInitialSwitch old new) new
  exact openEnvelope.trans switch

/-- Cell `(1,1)`: `ABAA -> BBBAAAB`. -/
theorem derivesAnchorSwitch11Core (old new : Word Nat) :
    Derives B16 (((old ++ new) ++ old) ++ old)
      ((((((new ++ new) ++ new) ++ old) ++ old) ++ old) ++ new) := by
  have expand :
      Derives B16 (((old ++ new) ++ old) ++ old)
        ((((((new ++ new) ++ new) ++ old) ++ new) ++ old) ++ old) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesUnaryAnchorContraction new old).symm old
  have finish :
      Derives B16
        ((((((new ++ new) ++ new) ++ old) ++ new) ++ old) ++ old)
        ((((((new ++ new) ++ new) ++ old) ++ old) ++ old) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.prepend (new ++ new)
        (derivesAttachmentXYYZX new old old)
  exact expand.trans finish

/-- Cell `(1,2)`: `ABABA -> BAAAB`. -/
theorem derivesAnchorSwitch12Core (old new : Word Nat) :
    Derives B16 ((((old ++ new) ++ old) ++ new) ++ old)
      ((((new ++ old) ++ old) ++ old) ++ new) := by
  have duplicate :
      Derives B16 ((((old ++ new) ++ old) ++ new) ++ old)
        ((((old ++ new) ++ old) ++ old) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.prepend old
        (derivesSquareFinalSwitch new old)
  have switch :
      Derives B16 ((((old ++ new) ++ old) ++ old) ++ new)
        ((((new ++ old) ++ old) ++ old) ++ new) := by
    simpa [Word.append_assoc] using
      derivesAttachmentYXXZY old new old
  exact duplicate.trans switch

/-- Cell `(1,3)`: `AABBBA -> BAAABB`. -/
theorem derivesAnchorSwitch13Core (old new : Word Nat) :
    Derives B16 (((((old ++ old) ++ new) ++ new) ++ new) ++ old)
      (((((new ++ old) ++ old) ++ old) ++ new) ++ new) := by
  have openEnvelope :
      Derives B16 (((((old ++ old) ++ new) ++ new) ++ new) ++ old)
        (((((old ++ old) ++ new) ++ old) ++ new) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.prepend old
        (derivesAttachmentXYYZX old new new).symm
  have switch :
      Derives B16 (((((old ++ old) ++ new) ++ old) ++ new) ++ new)
        (((((new ++ old) ++ old) ++ old) ++ new) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesTripleHeadSwitch old new) new
  exact openEnvelope.trans switch

/-- Cell `(2,1)`: `AAABA -> BABBB`. -/
theorem derivesAnchorSwitch21Core (old new : Word Nat) :
    Derives B16 ((((old ++ old) ++ old) ++ new) ++ old)
      ((((new ++ old) ++ new) ++ new) ++ new) :=
  derivesTripleTransfer old new

/-- Cell `(2,2)`: `AAABBA -> BAB`. -/
theorem derivesAnchorSwitch22Core (old new : Word Nat) :
    Derives B16 (((((old ++ old) ++ old) ++ new) ++ new) ++ old)
      ((new ++ old) ++ new) := by
  have openEnvelope :
      Derives B16 (((((old ++ old) ++ old) ++ new) ++ new) ++ old)
        (((((old ++ old) ++ old) ++ new) ++ old) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.prepend (old ++ old)
        (derivesSquareFinalSwitch old new).symm
  have contract :
      Derives B16 (((((old ++ old) ++ old) ++ new) ++ old) ++ new)
        ((new ++ old) ++ new) :=
    derivesUnaryAnchorContraction old new
  exact openEnvelope.trans contract

/-- Cell `(2,3)`: `AAABBBA -> BABB`. -/
theorem derivesAnchorSwitch23Core (old new : Word Nat) :
    Derives B16
      ((((((old ++ old) ++ old) ++ new) ++ new) ++ new) ++ old)
      (((new ++ old) ++ new) ++ new) := by
  have openEnvelope :
      Derives B16
        ((((((old ++ old) ++ old) ++ new) ++ new) ++ new) ++ old)
        ((((((old ++ old) ++ old) ++ new) ++ old) ++ new) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.prepend (old ++ old)
        (derivesAttachmentXYYZX old new new).symm
  have contract :
      Derives B16
        ((((((old ++ old) ++ old) ++ new) ++ old) ++ new) ++ new)
        (((new ++ old) ++ new) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesUnaryAnchorContraction old new) new
  exact openEnvelope.trans contract

/-! ## Nonempty retained-trailing word leaves -/

/-- Cell `(0,1)` with one retained nonempty interior block. -/
theorem derivesAnchorSwitch01WithTrailing
    (old new trailing : Word Nat) :
    Derives B16 (((old ++ new) ++ trailing) ++ old)
      ((((((new ++ new) ++ new) ++ old) ++ old) ++ trailing) ++ new) := by
  have expandBlock :
      Derives B16 (((old ++ new) ++ trailing) ++ old)
        (((((((((new ++ trailing) ++ new) ++ trailing) ++ new) ++
          trailing) ++ old) ++ new) ++ trailing) ++ old) := by
    simpa [Word.append_assoc] using
      (derivesUnaryAnchorContraction (new ++ trailing) old).symm
  have expandMiddle :
      Derives B16
        (((((((((new ++ trailing) ++ new) ++ trailing) ++ new) ++
          trailing) ++ old) ++ new) ++ trailing) ++ old)
        ((((((((((((new ++ new) ++ new) ++ new) ++ trailing) ++
          new) ++ trailing) ++ new) ++ trailing) ++ old) ++ new) ++
          trailing) ++ old) := by
    have core :=
      (derivesUnaryAnchorContraction new trailing).symm
    have withSuffix :=
      Derives.appendRight core
        (((((new ++ trailing) ++ old) ++ new) ++ trailing) ++ old)
    simpa [Word.append_assoc] using
      Derives.prepend new withSuffix
  have contractBlock :
      Derives B16
        ((((((((((((new ++ new) ++ new) ++ new) ++ trailing) ++
          new) ++ trailing) ++ new) ++ trailing) ++ old) ++ new) ++
          trailing) ++ old)
        ((((((new ++ new) ++ new) ++ old) ++ new) ++ trailing) ++ old) := by
    simpa [Word.append_assoc] using
      Derives.prepend (((new ++ new) ++ new))
        (derivesUnaryAnchorContraction (new ++ trailing) old)
  have finish :
      Derives B16
        ((((((new ++ new) ++ new) ++ old) ++ new) ++ trailing) ++ old)
        ((((((new ++ new) ++ new) ++ old) ++ old) ++ trailing) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.prepend (new ++ new)
        (derivesAttachmentXYYZX new old trailing)
  exact expandBlock.trans <|
    expandMiddle.trans <|
      contractBlock.trans finish

/-- Cell `(0,2)` with one retained nonempty interior block. -/
theorem derivesAnchorSwitch02WithTrailing
    (old new trailing : Word Nat) :
    Derives B16 ((((old ++ new) ++ new) ++ trailing) ++ old)
      ((((new ++ old) ++ old) ++ trailing) ++ new) :=
  (derivesAttachmentXYYZX old new trailing).symm.trans
    (derivesAttachmentYXXZY old new trailing)

/-- Cell `(0,3)` with one retained nonempty interior block. -/
theorem derivesAnchorSwitch03WithTrailing
    (old new trailing : Word Nat) :
    Derives B16 (((((old ++ new) ++ new) ++ new) ++ trailing) ++ old)
      (((((new ++ old) ++ old) ++ new) ++ trailing) ++ new) := by
  have openEnvelope :
      Derives B16
        (((((old ++ new) ++ new) ++ new) ++ trailing) ++ old)
        (((((old ++ new) ++ old) ++ new) ++ trailing) ++ new) := by
    simpa [Word.append_assoc] using
      (derivesAttachmentXYYZX old new (new ++ trailing)).symm
  have switch :
      Derives B16
        (((((old ++ new) ++ old) ++ new) ++ trailing) ++ new)
        (((((new ++ old) ++ old) ++ new) ++ trailing) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesSquareInitialSwitch old new) (trailing ++ new)
  exact openEnvelope.trans switch

/-- Cell `(1,1)` with one retained nonempty interior block. -/
theorem derivesAnchorSwitch11WithTrailing
    (old new trailing : Word Nat) :
    Derives B16 ((((old ++ new) ++ old) ++ trailing) ++ old)
      (((((((new ++ new) ++ new) ++ old) ++ old) ++ old) ++
        trailing) ++ new) := by
  have expand :
      Derives B16 ((((old ++ new) ++ old) ++ trailing) ++ old)
        (((((((new ++ new) ++ new) ++ old) ++ new) ++ old) ++
          trailing) ++ old) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesUnaryAnchorContraction new old).symm
        (trailing ++ old)
  have finish :
      Derives B16
        (((((((new ++ new) ++ new) ++ old) ++ new) ++ old) ++
          trailing) ++ old)
        (((((((new ++ new) ++ new) ++ old) ++ old) ++ old) ++
          trailing) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.prepend (new ++ new)
        (derivesAttachmentXYYZX new old (old ++ trailing))
  exact expand.trans finish

/-- Cell `(1,2)` with one retained nonempty interior block. -/
theorem derivesAnchorSwitch12WithTrailing
    (old new trailing : Word Nat) :
    Derives B16 (((((old ++ new) ++ old) ++ new) ++ trailing) ++ old)
      (((((new ++ old) ++ old) ++ old) ++ trailing) ++ new) := by
  have duplicate :
      Derives B16
        (((((old ++ new) ++ old) ++ new) ++ trailing) ++ old)
        (((((old ++ new) ++ old) ++ old) ++ trailing) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.prepend old
        (derivesAttachmentXYYZX new old trailing)
  have switch :
      Derives B16
        (((((old ++ new) ++ old) ++ old) ++ trailing) ++ new)
        (((((new ++ old) ++ old) ++ old) ++ trailing) ++ new) := by
    simpa [Word.append_assoc] using
      derivesAttachmentYXXZY old new (old ++ trailing)
  exact duplicate.trans switch

/-- Cell `(1,3)` with one retained nonempty interior block. -/
theorem derivesAnchorSwitch13WithTrailing
    (old new trailing : Word Nat) :
    Derives B16
      ((((((old ++ old) ++ new) ++ new) ++ new) ++ trailing) ++ old)
      ((((((new ++ old) ++ old) ++ old) ++ new) ++ trailing) ++ new) := by
  have openEnvelope :
      Derives B16
        ((((((old ++ old) ++ new) ++ new) ++ new) ++ trailing) ++ old)
        ((((((old ++ old) ++ new) ++ old) ++ new) ++ trailing) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.prepend old
        (derivesAttachmentXYYZX old new (new ++ trailing)).symm
  have switch :
      Derives B16
        ((((((old ++ old) ++ new) ++ old) ++ new) ++ trailing) ++ new)
        ((((((new ++ old) ++ old) ++ old) ++ new) ++ trailing) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesTripleHeadSwitch old new) (trailing ++ new)
  exact openEnvelope.trans switch

/-- Cell `(2,1)` with one retained nonempty interior block. -/
theorem derivesAnchorSwitch21WithTrailing
    (old new trailing : Word Nat) :
    Derives B16 (((((old ++ trailing) ++ old) ++ old) ++ new) ++ old)
      (((((new ++ trailing) ++ old) ++ new) ++ new) ++ new) := by
  simpa [Word.append_assoc] using
    (derivesThreeLetterAnchorRepair trailing old new).symm

/-- Cell `(2,2)` with one retained nonempty interior block. -/
theorem derivesAnchorSwitch22WithTrailing
    (old new trailing : Word Nat) :
    Derives B16
      ((((((old ++ old) ++ old) ++ new) ++ new) ++ trailing) ++ old)
      (((new ++ old) ++ trailing) ++ new) := by
  have openEnvelope :
      Derives B16
        ((((((old ++ old) ++ old) ++ new) ++ new) ++ trailing) ++ old)
        ((((((old ++ old) ++ old) ++ new) ++ old) ++ trailing) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.prepend (old ++ old)
        (derivesAttachmentXYYZX old new trailing).symm
  have expand :
      Derives B16
        ((((((old ++ old) ++ old) ++ new) ++ old) ++ trailing) ++ new)
        ((((((((((((old ++ old) ++ old) ++ old) ++ trailing) ++ old) ++
          trailing) ++ old) ++ trailing) ++ new) ++ old) ++ trailing) ++
          new) := by
    simpa [Word.append_assoc] using
      Derives.prepend (((old ++ old) ++ old))
        (derivesUnaryAnchorContraction (old ++ trailing) new).symm
  have contractMiddle :
      Derives B16
        ((((((((((((old ++ old) ++ old) ++ old) ++ trailing) ++ old) ++
          trailing) ++ old) ++ trailing) ++ new) ++ old) ++ trailing) ++
          new)
        (((((((((old ++ trailing) ++ old) ++ trailing) ++ old) ++
          trailing) ++ new) ++ old) ++ trailing) ++ new) := by
    have core := derivesUnaryAnchorContraction old trailing
    have withSuffix :=
      Derives.appendRight core
        (((((old ++ trailing) ++ new) ++ old) ++ trailing) ++ new)
    simpa [Word.append_assoc] using
      Derives.prepend old withSuffix
  have finish :
      Derives B16
        (((((((((old ++ trailing) ++ old) ++ trailing) ++ old) ++
          trailing) ++ new) ++ old) ++ trailing) ++ new)
        (((new ++ old) ++ trailing) ++ new) := by
    simpa [Word.append_assoc] using
      derivesUnaryAnchorContraction (old ++ trailing) new
  exact openEnvelope.trans <|
    expand.trans <|
      contractMiddle.trans finish

/-- Cell `(2,3)` with one retained nonempty interior block. -/
theorem derivesAnchorSwitch23WithTrailing
    (old new trailing : Word Nat) :
    Derives B16
      (((((((old ++ old) ++ old) ++ new) ++ new) ++ new) ++ trailing) ++
        old)
      ((((new ++ old) ++ new) ++ trailing) ++ new) := by
  have openEnvelope :
      Derives B16
        (((((((old ++ old) ++ old) ++ new) ++ new) ++ new) ++ trailing) ++
          old)
        (((((((old ++ old) ++ old) ++ new) ++ old) ++ new) ++ trailing) ++
          new) := by
    simpa [Word.append_assoc] using
      Derives.prepend (old ++ old)
        (derivesAttachmentXYYZX old new (new ++ trailing)).symm
  have contract :
      Derives B16
        (((((((old ++ old) ++ old) ++ new) ++ old) ++ new) ++ trailing) ++
          new)
        ((((new ++ old) ++ new) ++ trailing) ++ new) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesUnaryAnchorContraction old new) (trailing ++ new)
  exact openEnvelope.trans contract

/-! ## Optional-trailing list leaves -/

private theorem listDerivesOfWord {left right : Word Nat}
    (derivation : Derives B16 left right) :
    B16ListDerives left.toList right.toList :=
  S5_107.ListDerives.ofWord derivation

/-- Cell `(0,1)` with an arbitrary retained trailing interior list. -/
theorem listDerivesAnchorSwitch01
    (old new : Nat) (trailing : List Nat) :
    B16ListDerives
      (old :: new :: trailing ++ [old])
      (new :: new :: new :: old :: old :: trailing ++ [new]) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch01Core
              (Word.singleton old) (Word.singleton new))
  | cons trailingHead trailingTail =>
      let retained := S5_107.listWordOfCons trailingHead trailingTail
      simpa [retained, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch01WithTrailing
              (Word.singleton old) (Word.singleton new) retained)

/-- Cell `(0,2)` with an arbitrary retained trailing interior list. -/
theorem listDerivesAnchorSwitch02
    (old new : Nat) (trailing : List Nat) :
    B16ListDerives
      (old :: new :: new :: trailing ++ [old])
      (new :: old :: old :: trailing ++ [new]) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch02Core
              (Word.singleton old) (Word.singleton new))
  | cons trailingHead trailingTail =>
      let retained := S5_107.listWordOfCons trailingHead trailingTail
      simpa [retained, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch02WithTrailing
              (Word.singleton old) (Word.singleton new) retained)

/-- Cell `(0,3)` with an arbitrary retained trailing interior list. -/
theorem listDerivesAnchorSwitch03
    (old new : Nat) (trailing : List Nat) :
    B16ListDerives
      (old :: new :: new :: new :: trailing ++ [old])
      (new :: old :: old :: new :: trailing ++ [new]) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch03Core
              (Word.singleton old) (Word.singleton new))
  | cons trailingHead trailingTail =>
      let retained := S5_107.listWordOfCons trailingHead trailingTail
      simpa [retained, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch03WithTrailing
              (Word.singleton old) (Word.singleton new) retained)

/-- Cell `(1,1)` with an arbitrary retained trailing interior list. -/
theorem listDerivesAnchorSwitch11
    (old new : Nat) (trailing : List Nat) :
    B16ListDerives
      (old :: new :: old :: trailing ++ [old])
      (new :: new :: new :: old :: old :: old :: trailing ++ [new]) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch11Core
              (Word.singleton old) (Word.singleton new))
  | cons trailingHead trailingTail =>
      let retained := S5_107.listWordOfCons trailingHead trailingTail
      simpa [retained, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch11WithTrailing
              (Word.singleton old) (Word.singleton new) retained)

/-- Cell `(1,2)` with an arbitrary retained trailing interior list. -/
theorem listDerivesAnchorSwitch12
    (old new : Nat) (trailing : List Nat) :
    B16ListDerives
      (old :: new :: old :: new :: trailing ++ [old])
      (new :: old :: old :: old :: trailing ++ [new]) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch12Core
              (Word.singleton old) (Word.singleton new))
  | cons trailingHead trailingTail =>
      let retained := S5_107.listWordOfCons trailingHead trailingTail
      simpa [retained, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch12WithTrailing
              (Word.singleton old) (Word.singleton new) retained)

/-- Cell `(1,3)` with an arbitrary retained trailing interior list. -/
theorem listDerivesAnchorSwitch13
    (old new : Nat) (trailing : List Nat) :
    B16ListDerives
      (old :: old :: new :: new :: new :: trailing ++ [old])
      (new :: old :: old :: old :: new :: trailing ++ [new]) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch13Core
              (Word.singleton old) (Word.singleton new))
  | cons trailingHead trailingTail =>
      let retained := S5_107.listWordOfCons trailingHead trailingTail
      simpa [retained, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch13WithTrailing
              (Word.singleton old) (Word.singleton new) retained)

/-- Cell `(2,1)` with an arbitrary retained trailing interior list. -/
theorem listDerivesAnchorSwitch21
    (old new : Nat) (trailing : List Nat) :
    B16ListDerives
      ((old :: trailing) ++ old :: old :: new :: [old])
      ((new :: trailing) ++ old :: new :: new :: [new]) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch21Core
              (Word.singleton old) (Word.singleton new))
  | cons trailingHead trailingTail =>
      let retained := S5_107.listWordOfCons trailingHead trailingTail
      simpa [retained, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch21WithTrailing
              (Word.singleton old) (Word.singleton new) retained)

/-- Cell `(2,2)` with an arbitrary retained trailing interior list. -/
theorem listDerivesAnchorSwitch22
    (old new : Nat) (trailing : List Nat) :
    B16ListDerives
      (old :: old :: old :: new :: new :: trailing ++ [old])
      (new :: old :: trailing ++ [new]) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch22Core
              (Word.singleton old) (Word.singleton new))
  | cons trailingHead trailingTail =>
      let retained := S5_107.listWordOfCons trailingHead trailingTail
      simpa [retained, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch22WithTrailing
              (Word.singleton old) (Word.singleton new) retained)

/-- Cell `(2,3)` with an arbitrary retained trailing interior list. -/
theorem listDerivesAnchorSwitch23
    (old new : Nat) (trailing : List Nat) :
    B16ListDerives
      (old :: old :: old :: new :: new :: new :: trailing ++ [old])
      (new :: old :: new :: trailing ++ [new]) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch23Core
              (Word.singleton old) (Word.singleton new))
  | cons trailingHead trailingTail =>
      let retained := S5_107.listWordOfCons trailingHead trailingTail
      simpa [retained, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          listDerivesOfWord
            (derivesAnchorSwitch23WithTrailing
              (Word.singleton old) (Word.singleton new) retained)

end SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16

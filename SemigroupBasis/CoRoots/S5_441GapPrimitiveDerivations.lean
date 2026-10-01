import SemigroupBasis.CoRoots.S5_441ListDerives

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis

private theorem derivesRetainedCrossingBothNonempty
    (a b z u : Word Nat) :
    Derives basis
      (((((a ++ b) ++ z) ++ a) ++ u) ++ b)
      (((((a ++ b) ++ b) ++ z) ++ u) ++ a) := by
  have first :
      Derives basis
        (((((a ++ b) ++ z) ++ a) ++ u) ++ b)
        (((((a ++ b) ++ a) ++ u) ++ z) ++ b) := by
    simpa [Word.append_assoc] using
      Derives.prepend a
        (derivesInteriorSwap b z (a ++ u))
  have second :
      Derives basis
        (((((a ++ b) ++ a) ++ u) ++ z) ++ b)
        (((((a ++ a) ++ b) ++ u) ++ z) ++ b) := by
    simpa [Word.append_assoc] using
      (derivesAttachmentXYXZY a b (u ++ z)).symm
  have third :
      Derives basis
        (((((a ++ a) ++ b) ++ u) ++ z) ++ b)
        (((((a ++ a) ++ b) ++ z) ++ u) ++ b) := by
    simpa [Word.append_assoc] using
      Derives.prepend (a ++ a)
        (derivesInteriorSwap b u z)
  have fourth :
      Derives basis
        (((((a ++ a) ++ b) ++ z) ++ u) ++ b)
        (((((a ++ b) ++ b) ++ z) ++ u) ++ a) := by
    simpa [Word.append_assoc] using
      derivesAttachmentXYYZX a b (z ++ u)
  exact first.trans (second.trans (third.trans fourth))

private theorem derivesRetainedCrossingLeftEmpty
    (a b u : Word Nat) :
    Derives basis
      ((((a ++ b) ++ a) ++ u) ++ b)
      ((((a ++ b) ++ b) ++ u) ++ a) := by
  have first :
      Derives basis
        ((((a ++ b) ++ a) ++ u) ++ b)
        ((((a ++ a) ++ b) ++ u) ++ b) := by
    simpa [Word.append_assoc] using
      (derivesAttachmentXYXZY a b u).symm
  have second :
      Derives basis
        ((((a ++ a) ++ b) ++ u) ++ b)
        ((((a ++ b) ++ b) ++ u) ++ a) := by
    simpa [Word.append_assoc] using
      derivesAttachmentXYYZX a b u
  exact first.trans second

private theorem derivesRetainedCrossingRightEmpty
    (a b z : Word Nat) :
    Derives basis
      ((((a ++ b) ++ z) ++ a) ++ b)
      ((((a ++ b) ++ b) ++ z) ++ a) := by
  have first :
      Derives basis
        ((((a ++ b) ++ z) ++ a) ++ b)
        ((((a ++ b) ++ a) ++ z) ++ b) := by
    simpa [Word.append_assoc] using
      Derives.prepend a
        (derivesInteriorSwap b z a)
  have second :
      Derives basis
        ((((a ++ b) ++ a) ++ z) ++ b)
        ((((a ++ a) ++ b) ++ z) ++ b) := by
    simpa [Word.append_assoc] using
      (derivesAttachmentXYXZY a b z).symm
  have third :
      Derives basis
        ((((a ++ a) ++ b) ++ z) ++ b)
        ((((a ++ b) ++ b) ++ z) ++ a) := by
    simpa [Word.append_assoc] using
      derivesAttachmentXYYZX a b z
  exact first.trans (second.trans third)

private theorem derivesRetainedCrossingBothEmpty
    (a b : Word Nat) :
    Derives basis
      (((a ++ b) ++ a) ++ b)
      (((a ++ b) ++ b) ++ a) := by
  have first :
      Derives basis
        (((a ++ b) ++ a) ++ b)
        ((a ++ a) ++ (b ++ b)) := by
    simpa [Word.append_assoc] using
      (derivesSquareInterleave a b).symm
  have second :
      Derives basis
        ((a ++ a) ++ (b ++ b))
        (((a ++ b) ++ b) ++ a) := by
    simpa [Word.append_assoc] using
      derivesSquareFinalSwitch a b
  exact first.trans second

/-- Retain both crossing anchors while moving the second copy of `b` next
to the first. The filler lists may independently be empty. No occurrence is
deleted, so the transformation preserves every multiplicity exactly. -/
theorem listDerivesRetainedCrossing
    (a b : Word Nat) (z u : List Nat) :
    ListDerives
      (a.toList ++ b.toList ++ z ++ a.toList ++ u ++ b.toList)
      (a.toList ++ b.toList ++ b.toList ++ z ++ u ++ a.toList) := by
  cases z with
  | nil =>
      cases u with
      | nil =>
          simpa [Word.toList_append, List.append_assoc] using
            (ListDerives.ofWord
              (derivesRetainedCrossingBothEmpty a b))
      | cons uHead uTail =>
          let uWord :=
            S5_107.listWordOfCons uHead uTail
          simpa [uWord, S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              (ListDerives.ofWord
                (derivesRetainedCrossingLeftEmpty
                  a b uWord))
  | cons zHead zTail =>
      let zWord :=
        S5_107.listWordOfCons zHead zTail
      cases u with
      | nil =>
          simpa [zWord, S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              (ListDerives.ofWord
                (derivesRetainedCrossingRightEmpty
                  a b zWord))
      | cons uHead uTail =>
          let uWord :=
            S5_107.listWordOfCons uHead uTail
          simpa [zWord, uWord, S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              (ListDerives.ofWord
                (derivesRetainedCrossingBothNonempty
                  a b zWord uWord))

private theorem derivesRetainedEndpointBothNonempty
    (a z u : Word Nat) :
    Derives basis
      ((((a ++ z) ++ a) ++ u) ++ a)
      ((((a ++ z) ++ u) ++ a) ++ a) := by
  have first :
      Derives basis
        ((((a ++ z) ++ a) ++ u) ++ a)
        ((((a ++ u) ++ z) ++ a) ++ a) := by
    simpa [Word.append_assoc] using
      derivesInteriorSwap a (z ++ a) u
  have second :
      Derives basis
        ((((a ++ u) ++ z) ++ a) ++ a)
        ((((a ++ z) ++ u) ++ a) ++ a) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesInteriorSwap a u z) a
  exact first.trans second

/-- Move the middle copy of an endpoint to the final endpoint pair. The
two filler lists may independently be empty; in the empty-right case the
source and target coincide. -/
theorem listDerivesRetainedEndpoint
    (a : Word Nat) (z u : List Nat) :
    ListDerives
      (a.toList ++ z ++ a.toList ++ u ++ a.toList)
      (a.toList ++ z ++ u ++ a.toList ++ a.toList) := by
  cases u with
  | nil =>
      simpa [List.append_assoc] using
        (ListDerives.refl
          (a.toList ++ z ++ a.toList ++ a.toList))
  | cons uHead uTail =>
      let uWord :=
        S5_107.listWordOfCons uHead uTail
      cases z with
      | nil =>
          simpa [uWord, S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              (ListDerives.ofWord
                (derivesEndpointTransfer a uWord))
      | cons zHead zTail =>
          let zWord :=
            S5_107.listWordOfCons zHead zTail
          simpa [zWord, uWord, S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              (ListDerives.ofWord
                (derivesRetainedEndpointBothNonempty
                  a zWord uWord))

/-- Swap two adjacent nonempty interior blocks while retaining a nonempty
trailing block and matching nonempty envelope blocks. The temporary
expansions add and later remove two copies of the envelope block. -/
theorem derivesAdjacentInteriorBlockSwap
    (anchor left right trailing : Word Nat) :
    Derives basis
      ((((anchor ++ left) ++ right) ++ trailing) ++ anchor)
      ((((anchor ++ right) ++ left) ++ trailing) ++ anchor) := by
  have first :
      Derives basis
        ((((anchor ++ left) ++ right) ++ trailing) ++ anchor)
        ((((((anchor ++ anchor) ++ anchor) ++ left) ++ right) ++
          trailing) ++ anchor) := by
    simpa [Word.append_assoc] using
      derivesLeftEnvelopePower anchor
        ((left ++ right) ++ trailing)
  have second :
      Derives basis
        ((((((anchor ++ anchor) ++ anchor) ++ left) ++ right) ++
          trailing) ++ anchor)
        ((((((anchor ++ anchor) ++ trailing) ++ anchor) ++ left) ++
          right) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.prepend anchor
        (derivesInteriorSwap anchor
          ((anchor ++ left) ++ right) trailing)
  have third :
      Derives basis
        ((((((anchor ++ anchor) ++ trailing) ++ anchor) ++ left) ++
          right) ++ anchor)
        ((((((anchor ++ anchor) ++ trailing) ++ anchor) ++ right) ++
          left) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.prepend
        ((anchor ++ anchor) ++ trailing)
        (derivesInteriorSwap anchor left right)
  have fourth :
      Derives basis
        ((((((anchor ++ anchor) ++ trailing) ++ anchor) ++ right) ++
          left) ++ anchor)
        ((((((anchor ++ anchor) ++ anchor) ++ right) ++ left) ++
          trailing) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.prepend anchor
        (derivesInteriorSwap anchor trailing
          ((anchor ++ right) ++ left))
  have fifth :
      Derives basis
        ((((((anchor ++ anchor) ++ anchor) ++ right) ++ left) ++
          trailing) ++ anchor)
        ((((anchor ++ right) ++ left) ++ trailing) ++ anchor) := by
    simpa [Word.append_assoc] using
      (derivesLeftEnvelopePower anchor
        ((right ++ left) ++ trailing)).symm
  exact
    first.trans <|
      second.trans <|
        third.trans <|
          fourth.trans fifth

/-- List-level form of `derivesAdjacentInteriorBlockSwap`. All five blocks
are represented by nonempty semigroup words. -/
theorem listDerivesAdjacentInteriorBlockSwapWords
    (anchor left right trailing : Word Nat) :
    ListDerives
      (anchor.toList ++ left.toList ++ right.toList ++
        trailing.toList ++ anchor.toList)
      (anchor.toList ++ right.toList ++ left.toList ++
        trailing.toList ++ anchor.toList) := by
  simpa [Word.toList_append, List.append_assoc] using
    (ListDerives.ofWord
      (derivesAdjacentInteriorBlockSwap
        anchor left right trailing))

/-- Apply the adjacent interior block swap inside arbitrary list prefix and
suffix contexts. -/
theorem listDerivesAdjacentInteriorBlockSwapContext
    (pre suffix : List Nat)
    (anchor left right trailing : Word Nat) :
    ListDerives
      (pre ++ anchor.toList ++ left.toList ++ right.toList ++
        trailing.toList ++ anchor.toList ++ suffix)
      (pre ++ anchor.toList ++ right.toList ++ left.toList ++
        trailing.toList ++ anchor.toList ++ suffix) := by
  simpa [List.append_assoc] using
    ListDerives.context pre suffix
      (listDerivesAdjacentInteriorBlockSwapWords
        anchor left right trailing)

/-- Swap two singleton interior letters before a retained nonempty trailing
list, under arbitrary outer list contexts. -/
theorem listDerivesAdjacentInteriorSingletonSwapContext
    (pre suffix : List Nat)
    (anchor first second trailingHead : Nat)
    (trailingTail : List Nat) :
    ListDerives
      (pre ++ [anchor, first, second] ++
        (trailingHead :: trailingTail) ++ [anchor] ++ suffix)
      (pre ++ [anchor, second, first] ++
        (trailingHead :: trailingTail) ++ [anchor] ++ suffix) := by
  let trailing :=
    S5_107.listWordOfCons trailingHead trailingTail
  simpa [trailing, S5_107.listWordOfCons, Word.toList,
    Word.toList_singleton, List.append_assoc] using
      listDerivesAdjacentInteriorBlockSwapContext
        pre suffix
        (Word.singleton anchor)
        (Word.singleton first)
        (Word.singleton second)
        trailing

end SemigroupBasis.CoRoots.S5_441

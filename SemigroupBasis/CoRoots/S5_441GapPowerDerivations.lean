import SemigroupBasis.CoRoots.S5_441GapPrimitiveDerivations

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis

/-- Contract four adjacent copies of a nonempty block to two copies.
Every letter count changes by twice its count in `block`, so parity is
preserved coordinatewise. -/
theorem derivesBlockFourToTwo (block : Word Nat) :
    Derives basis
      (((block ++ block) ++ block) ++ block)
      (block ++ block) :=
  (derivesBlockSquarePower block).symm

/-- Word-level four-to-two contraction under nonempty outer contexts.
The only multiplicity change is the removal of two copies of `block`. -/
theorem derivesBlockFourToTwoContext
    (pre block suffix : Word Nat) :
    Derives basis
      ((pre ++ (((block ++ block) ++ block) ++ block)) ++ suffix)
      ((pre ++ (block ++ block)) ++ suffix) :=
  Derives.appendRight
    (Derives.prepend pre (derivesBlockFourToTwo block))
    suffix

/-- Flattened list form of the parity-preserving four-to-two contraction. -/
theorem listDerivesBlockFourToTwo (block : Word Nat) :
    ListDerives
      (block.toList ++ block.toList ++ block.toList ++ block.toList)
      (block.toList ++ block.toList) := by
  simpa [Word.toList_append, List.append_assoc] using
    (ListDerives.ofWord (derivesBlockFourToTwo block))

/-- Apply the four-to-two contraction under arbitrary, possibly empty,
list contexts. The context is unchanged and two block copies are removed. -/
theorem listDerivesBlockFourToTwoContext
    (pre suffix : List Nat) (block : Word Nat) :
    ListDerives
      (pre ++ block.toList ++ block.toList ++ block.toList ++
        block.toList ++ suffix)
      (pre ++ block.toList ++ block.toList ++ suffix) := by
  simpa [List.append_assoc] using
    ListDerives.context pre suffix
      (listDerivesBlockFourToTwo block)

/-- Contract three adjacent copies of `block` to one between matching
nonempty anchors. This is the empty-filler case of the envelope contraction
and removes exactly two block copies. -/
theorem derivesEnvelopeBlockThreeToOne
    (anchor block : Word Nat) :
    Derives basis
      ((((anchor ++ block) ++ block) ++ block) ++ anchor)
      ((anchor ++ block) ++ anchor) :=
  (derivesEnvelopePower anchor block).symm

/-- Contract three copies of `block` to one inside an anchor envelope while
retaining a nonempty trailing filler. The audited route is
`A V V V T A -> A V V T V A -> A V T V T V T A -> A V T A`.
It removes two copies of `block` and otherwise only reorders retained
material, hence preserves every letter count modulo two. -/
theorem derivesEnvelopeBlockThreeToOneWithTrailing
    (anchor block trailing : Word Nat) :
    Derives basis
      (((((anchor ++ block) ++ block) ++ block) ++ trailing) ++ anchor)
      (((anchor ++ block) ++ trailing) ++ anchor) := by
  have first :
      Derives basis
        (((((anchor ++ block) ++ block) ++ block) ++ trailing) ++ anchor)
        (((((anchor ++ block) ++ block) ++ trailing) ++ block) ++ anchor) := by
    simpa [Word.append_assoc] using
      derivesInteriorSwap anchor block
        ((block ++ block) ++ trailing)
  have second :
      Derives basis
        (((((anchor ++ block) ++ block) ++ trailing) ++ block) ++ anchor)
        (((((((anchor ++ block) ++ trailing) ++ block) ++ trailing) ++
          block) ++ trailing) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend (anchor ++ block)
          (derivesXYXToYXYXY block trailing))
        anchor
  have third :
      Derives basis
        (((((((anchor ++ block) ++ trailing) ++ block) ++ trailing) ++
          block) ++ trailing) ++ anchor)
        (((anchor ++ block) ++ trailing) ++ anchor) := by
    simpa [Word.append_assoc] using
      (derivesEnvelopePower anchor (block ++ trailing)).symm
  exact first.trans (second.trans third)

/-- List-level three-to-one envelope contraction with an optional filler.
The empty filler uses `derivesEnvelopeBlockThreeToOne`; a nonempty filler
uses the parity-preserving audited route. -/
theorem listDerivesEnvelopeBlockThreeToOne
    (anchor block : Word Nat) (trailing : List Nat) :
    ListDerives
      (anchor.toList ++ block.toList ++ block.toList ++ block.toList ++
        trailing ++ anchor.toList)
      (anchor.toList ++ block.toList ++ trailing ++ anchor.toList) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, List.append_assoc] using
        (ListDerives.ofWord
          (derivesEnvelopeBlockThreeToOne anchor block))
  | cons trailingHead trailingTail =>
      let trailingWord :=
        S5_107.listWordOfCons trailingHead trailingTail
      simpa [trailingWord, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, List.append_assoc] using
          (ListDerives.ofWord
            (derivesEnvelopeBlockThreeToOneWithTrailing
              anchor block trailingWord))

/-- Apply the optional-filler three-to-one envelope contraction under
arbitrary list contexts. Only two copies of `block` are removed. -/
theorem listDerivesEnvelopeBlockThreeToOneContext
    (pre suffix : List Nat)
    (anchor block : Word Nat) (trailing : List Nat) :
    ListDerives
      (pre ++ anchor.toList ++ block.toList ++ block.toList ++
        block.toList ++ trailing ++ anchor.toList ++ suffix)
      (pre ++ anchor.toList ++ block.toList ++ trailing ++
        anchor.toList ++ suffix) := by
  simpa [List.append_assoc] using
    ListDerives.context pre suffix
      (listDerivesEnvelopeBlockThreeToOne
        anchor block trailing)

/-- Switch an odd/odd anchor profile with no trailing filler:
`A A B A -> B A B B`. Two copies move from `A` to `B`, so the parity
of every letter count is unchanged. -/
theorem derivesOddOddAnchorSwitch
    (oldAnchor newAnchor : Word Nat) :
    Derives basis
      (((oldAnchor ++ oldAnchor) ++ newAnchor) ++ oldAnchor)
      (((newAnchor ++ oldAnchor) ++ newAnchor) ++ newAnchor) :=
  derivesEnvelopeSwitch oldAnchor newAnchor

/-- Switch an odd/odd anchor profile while retaining a nonempty filler:
`A A B C A -> B A B C B`. The old and new anchor multiplicities change
by two in opposite directions. -/
theorem derivesOddOddAnchorSwitchWithTrailing
    (oldAnchor newAnchor trailing : Word Nat) :
    Derives basis
      ((((oldAnchor ++ oldAnchor) ++ newAnchor) ++ trailing) ++ oldAnchor)
      ((((newAnchor ++ oldAnchor) ++ newAnchor) ++ trailing) ++ newAnchor) :=
  derivesExtendedEnvelopeSwitch oldAnchor newAnchor trailing

/-- List-level odd/odd anchor switch with an optional filler. This theorem
states only the local parity-preserving rewrite, not normalization
completeness. -/
theorem listDerivesOddOddAnchorSwitch
    (oldAnchor newAnchor : Word Nat) (trailing : List Nat) :
    ListDerives
      (oldAnchor.toList ++ oldAnchor.toList ++ newAnchor.toList ++
        trailing ++ oldAnchor.toList)
      (newAnchor.toList ++ oldAnchor.toList ++ newAnchor.toList ++
        trailing ++ newAnchor.toList) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, List.append_assoc] using
        (ListDerives.ofWord
          (derivesOddOddAnchorSwitch oldAnchor newAnchor))
  | cons trailingHead trailingTail =>
      let trailingWord :=
        S5_107.listWordOfCons trailingHead trailingTail
      simpa [trailingWord, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, List.append_assoc] using
          (ListDerives.ofWord
            (derivesOddOddAnchorSwitchWithTrailing
              oldAnchor newAnchor trailingWord))

/-- Switch an even/even anchor profile with no trailing filler:
`A B B A -> B A A B`. Both sides contain exactly two copies of each
anchor block. -/
theorem derivesEvenEvenAnchorSwitch
    (oldAnchor newAnchor : Word Nat) :
    Derives basis
      (((oldAnchor ++ newAnchor) ++ newAnchor) ++ oldAnchor)
      (((newAnchor ++ oldAnchor) ++ oldAnchor) ++ newAnchor) := by
  have first :
      Derives basis
        (((oldAnchor ++ newAnchor) ++ newAnchor) ++ oldAnchor)
        ((oldAnchor ++ oldAnchor) ++ (newAnchor ++ newAnchor)) :=
    (derivesSquareFinalSwitch oldAnchor newAnchor).symm
  have second :
      Derives basis
        ((oldAnchor ++ oldAnchor) ++ (newAnchor ++ newAnchor))
        (((newAnchor ++ oldAnchor) ++ oldAnchor) ++ newAnchor) :=
    derivesSquareInitialSwitch oldAnchor newAnchor
  exact first.trans second

/-- Switch an even/even anchor profile while retaining a nonempty filler:
`A B B C A -> B A A C B`. The intermediate attachment rewrites preserve
the two copies of each anchor block exactly. -/
theorem derivesEvenEvenAnchorSwitchWithTrailing
    (oldAnchor newAnchor trailing : Word Nat) :
    Derives basis
      ((((oldAnchor ++ newAnchor) ++ newAnchor) ++ trailing) ++ oldAnchor)
      ((((newAnchor ++ oldAnchor) ++ oldAnchor) ++ trailing) ++ newAnchor) := by
  have first :
      Derives basis
        ((((oldAnchor ++ newAnchor) ++ newAnchor) ++ trailing) ++ oldAnchor)
        ((((oldAnchor ++ oldAnchor) ++ newAnchor) ++ trailing) ++ newAnchor) :=
    (derivesAttachmentXYYZX
      oldAnchor newAnchor trailing).symm
  have second :
      Derives basis
        ((((oldAnchor ++ oldAnchor) ++ newAnchor) ++ trailing) ++ newAnchor)
        ((((newAnchor ++ oldAnchor) ++ oldAnchor) ++ trailing) ++ newAnchor) :=
    derivesAttachmentYXXZY
      oldAnchor newAnchor trailing
  exact first.trans second

/-- List-level even/even anchor switch with an optional filler. It preserves
the complete multiplicity vector, not merely its parity. -/
theorem listDerivesEvenEvenAnchorSwitch
    (oldAnchor newAnchor : Word Nat) (trailing : List Nat) :
    ListDerives
      (oldAnchor.toList ++ newAnchor.toList ++ newAnchor.toList ++
        trailing ++ oldAnchor.toList)
      (newAnchor.toList ++ oldAnchor.toList ++ oldAnchor.toList ++
        trailing ++ newAnchor.toList) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, List.append_assoc] using
        (ListDerives.ofWord
          (derivesEvenEvenAnchorSwitch oldAnchor newAnchor))
  | cons trailingHead trailingTail =>
      let trailingWord :=
        S5_107.listWordOfCons trailingHead trailingTail
      simpa [trailingWord, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, List.append_assoc] using
          (ListDerives.ofWord
            (derivesEvenEvenAnchorSwitchWithTrailing
              oldAnchor newAnchor trailingWord))

end SemigroupBasis.CoRoots.S5_441

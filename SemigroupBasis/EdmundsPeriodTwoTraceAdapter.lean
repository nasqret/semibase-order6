import SemigroupBasis.BlockTraceDerives
import SemigroupBasis.CoRoots.S5_443CanonicalSyntax

namespace SemigroupBasis.EdmundsPeriodTwoTraceAdapter

open SemigroupBasis.BlockTrace
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.S5_443Family.CanonicalSyntax
open SemigroupBasis.Examples

/-! ## Public first-occurrence parser -/

/-- The syntax-only normal-form data needed by a block-trace certificate. -/
structure ParserSpec (source : Word Nat) where
  normalWord : Word Nat
  normalBlocks : List RetainedBlock
  renderNormal :
    renderRetainedBlocks normalBlocks = normalWord.toList
  labelsNodup : RetainedLabelsNodup normalBlocks
  sourceDerivesNormal :
    Derives edmundsPeriodTwoBlocksBasis source normalWord

private theorem normalList_ne_nil (source : Word Nat) :
    edmundsPeriodTwoBlocksNormalList source.toList ≠ [] := by
  cases source with
  | mk head tail =>
      simpa [Word.toList] using
        edmundsPeriodTwoBlocksNormalList_cons_ne_nil head tail

/-- The word represented by the unrestricted period-two normal list. The empty
branch makes the definition total and is unreachable for a semigroup word. -/
def normalWord (source : Word Nat) : Word Nat :=
  match edmundsPeriodTwoBlocksNormalList source.toList with
  | [] => source
  | head :: tail => edmundsPeriodTwoBlocksWordOfCons head tail

/-- Parse the unrestricted period-two normal list into retained blocks. -/
def normalBlocks (source : Word Nat) : List RetainedBlock :=
  edmundsPeriodTwoBlocksOfNormalList
    (edmundsPeriodTwoBlocksNormalList source.toList)

theorem normalWord_toList (source : Word Nat) :
    (normalWord source).toList =
      edmundsPeriodTwoBlocksNormalList source.toList := by
  cases source with
  | mk sourceHead sourceTail =>
      cases normalEq :
          edmundsPeriodTwoBlocksNormalList
            (Word.mk sourceHead sourceTail).toList with
      | nil =>
          exact False.elim
            (normalList_ne_nil (Word.mk sourceHead sourceTail) normalEq)
      | cons head tail =>
          change
            edmundsPeriodTwoBlocksNormalList
                (sourceHead :: sourceTail) = head :: tail at normalEq
          simp [normalWord, normalEq,
            edmundsPeriodTwoBlocksWordOfCons, Word.toList]

theorem render_normalBlocks (source : Word Nat) :
    renderRetainedBlocks (normalBlocks source) =
      (normalWord source).toList := by
  exact
    (render_edmundsPeriodTwoBlocksOfNormalList
      (edmundsPeriodTwoBlocksNormalList_normal source.toList)).trans
        (normalWord_toList source).symm

theorem normalBlocks_labelsNodup (source : Word Nat) :
    RetainedLabelsNodup (normalBlocks source) := by
  simpa [normalBlocks, RetainedLabelsNodup] using
    edmundsPeriodTwoBlocksOfNormalList_labels_nodup
      (edmundsPeriodTwoBlocksNormalList_normal source.toList)

theorem derives_normalWord (source : Word Nat) :
    Derives edmundsPeriodTwoBlocksBasis source (normalWord source) := by
  have derivation := edmundsPeriodTwoBlocksDerivesNormal source
  cases normalEq : edmundsPeriodTwoBlocksNormalList source.toList with
  | nil =>
      exact False.elim (normalList_ne_nil source normalEq)
  | cons head tail =>
      rw [normalEq] at derivation
      simpa [normalWord, normalEq,
        edmundsPeriodTwoBlocksWordOfCons] using derivation

/-- The complete mechanical parser package for any nonempty word. -/
def parserSpec (source : Word Nat) : ParserSpec source where
  normalWord := normalWord source
  normalBlocks := normalBlocks source
  renderNormal := render_normalBlocks source
  labelsNodup := normalBlocks_labelsNodup source
  sourceDerivesNormal := derives_normalWord source

/-! ## Derivation transport -/

/-- Derivability of the three Edmunds syntax laws in a target basis. -/
structure SyntaxLawsDerivable (basis : List (Identity Nat)) where
  power : Derives basis
    edmundsPeriodTwoBlocksPowerLaw.lhs
    edmundsPeriodTwoBlocksPowerLaw.rhs
  gather : Derives basis
    edmundsPeriodTwoBlocksGatherLaw.lhs
    edmundsPeriodTwoBlocksGatherLaw.rhs
  squareCommutation : Derives basis
    edmundsPeriodTwoBlocksCommutationLaw.lhs
    edmundsPeriodTwoBlocksCommutationLaw.rhs

theorem SyntaxLawsDerivable.axiomDerives
    {basis : List (Identity Nat)}
    (laws : SyntaxLawsDerivable basis) :
    ∀ identity : Identity Nat,
      identity ∈ edmundsPeriodTwoBlocksBasis →
        Derives basis identity.lhs identity.rhs := by
  intro identity member
  simp only [edmundsPeriodTwoBlocksBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact laws.power
  · exact laws.gather
  · exact laws.squareCommutation

/-- Convert the custom Edmunds list derivation to the shared, basis-indexed
`ListDerives` relation. No semantic hypothesis is used. -/
theorem transportListDerives
    {basis : List (Identity Nat)}
    (axiomDerives : ∀ identity : Identity Nat,
      identity ∈ edmundsPeriodTwoBlocksBasis →
        Derives basis identity.lhs identity.rhs)
    {source target : List Nat}
    (derivation :
      EdmundsPeriodTwoBlocksListDerives source target) :
    ListDerives basis source target := by
  cases derivation with
  | empty =>
      exact .empty
  | words wordDerivation =>
      exact .words <| by
        simpa [listWordOfCons,
          edmundsPeriodTwoBlocksWordOfCons] using
            wordDerivation.transport axiomDerives

theorem SyntaxLawsDerivable.transportListDerives
    {basis : List (Identity Nat)}
    (laws : SyntaxLawsDerivable basis)
    {source target : List Nat}
    (derivation :
      EdmundsPeriodTwoBlocksListDerives source target) :
    ListDerives basis source target :=
  SemigroupBasis.EdmundsPeriodTwoTraceAdapter.transportListDerives
    laws.axiomDerives derivation

theorem ParserSpec.derivesNormalIn
    {source : Word Nat} (spec : ParserSpec source)
    {basis : List (Identity Nat)}
    (laws : SyntaxLawsDerivable basis) :
    Derives basis source spec.normalWord :=
  spec.sourceDerivesNormal.transport laws.axiomDerives

/-! ## Class 54 orientation and adjacent swaps -/

def class54XYY : Word Nat :=
  edmundsPeriodTwoBlocksWordOfCons 0 [1, 1]

def class54YYX : Word Nat :=
  edmundsPeriodTwoBlocksWordOfCons 1 [1, 0]

def class54XYYY : Word Nat :=
  edmundsPeriodTwoBlocksWordOfCons 0 [1, 1, 1]

def class54YYYX : Word Nat :=
  edmundsPeriodTwoBlocksWordOfCons 1 [1, 1, 0]

/-- The class54 basis records gather and square commutation opposite to the
syntax engine, plus the two mixed singleton/repeated commutations. -/
structure Class54OrientedLaws (basis : List (Identity Nat)) where
  power : Derives basis
    edmundsPeriodTwoBlocksPowerLaw.lhs
    edmundsPeriodTwoBlocksPowerLaw.rhs
  gatherReversed : Derives basis
    edmundsPeriodTwoBlocksGatherLaw.rhs
    edmundsPeriodTwoBlocksGatherLaw.lhs
  squareCommutationReversed : Derives basis
    edmundsPeriodTwoBlocksCommutationLaw.rhs
    edmundsPeriodTwoBlocksCommutationLaw.lhs
  singleDouble : Derives basis class54XYY class54YYX
  singleTriple : Derives basis class54XYYY class54YYYX

/-- Reorient the two reversed class54 laws for the Edmunds syntax engine. -/
def Class54OrientedLaws.toSyntaxLaws
    {basis : List (Identity Nat)}
    (laws : Class54OrientedLaws basis) :
    SyntaxLawsDerivable basis where
  power := laws.power
  gather := laws.gatherReversed.symm
  squareCommutation := laws.squareCommutationReversed.symm

private def instantiateTwoWords
    (left right : Word Nat) : Nat → Word Nat
  | 0 => left
  | 1 => right
  | n + 2 => Word.singleton (n + 2)

theorem Class54OrientedLaws.derivesSingleDouble
    {basis : List (Identity Nat)}
    (laws : Class54OrientedLaws basis) (x y : Nat) :
    Derives basis
      (edmundsPeriodTwoBlocksWordOfCons x [y, y])
      (edmundsPeriodTwoBlocksWordOfCons y [y, x]) := by
  have derivation :=
    Derives.subst laws.singleDouble
      (instantiateTwoWords (Word.singleton x) (Word.singleton y))
  simpa [class54XYY, class54YYX, instantiateTwoWords,
    edmundsPeriodTwoBlocksWordOfCons, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using derivation

theorem Class54OrientedLaws.derivesSingleTriple
    {basis : List (Identity Nat)}
    (laws : Class54OrientedLaws basis) (x y : Nat) :
    Derives basis
      (edmundsPeriodTwoBlocksWordOfCons x [y, y, y])
      (edmundsPeriodTwoBlocksWordOfCons y [y, y, x]) := by
  have derivation :=
    Derives.subst laws.singleTriple
      (instantiateTwoWords (Word.singleton x) (Word.singleton y))
  simpa [class54XYYY, class54YYYX, instantiateTwoWords,
    edmundsPeriodTwoBlocksWordOfCons, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using derivation

/-- Class54 permits every retained-state crossing except singleton/singleton. -/
def class54Commutes (left right : Nat) : Prop :=
  ¬ (left = 1 ∧ right = 1)

private theorem Class54OrientedLaws.repeatedSwap
    {basis : List (Identity Nat)}
    (laws : Class54OrientedLaws basis)
    (left right : EdmundsPeriodTwoRepeatedBlock) :
    ListDerives basis
      (left.render ++ right.render)
      (right.render ++ left.render) :=
  laws.toSyntaxLaws.transportListDerives
    (edmundsPeriodTwoBlocksDerivesRepeatedBlockCommutation left right)

/-- All eight class54-authorized adjacent retained-block swaps follow from the
five oriented basis laws. The excluded ninth case is singleton/singleton. -/
theorem Class54OrientedLaws.adjacentSwap
    {basis : List (Identity Nat)}
    (laws : Class54OrientedLaws basis) :
    AdjacentSwapDerivable basis class54Commutes := by
  intro left right allowed
  cases left with
  | single x =>
      cases right with
      | single y =>
          exact False.elim (allowed ⟨rfl, rfl⟩)
      | double y =>
          simpa [EdmundsPeriodTwoBlock.render,
            edmundsPeriodTwoBlocksWordOfCons, Word.toList] using
              ListDerives.ofWord (laws.derivesSingleDouble x y)
      | triple y =>
          simpa [EdmundsPeriodTwoBlock.render,
            edmundsPeriodTwoBlocksWordOfCons, Word.toList] using
              ListDerives.ofWord (laws.derivesSingleTriple x y)
  | double x =>
      cases right with
      | single y =>
          simpa [EdmundsPeriodTwoBlock.render,
            edmundsPeriodTwoBlocksWordOfCons, Word.toList] using
              ListDerives.ofWord (laws.derivesSingleDouble y x).symm
      | double y =>
          simpa [EdmundsPeriodTwoBlock.render,
            EdmundsPeriodTwoRepeatedBlock.render,
            EdmundsPeriodTwoRepeatedBlock.toBlock] using
              laws.repeatedSwap (.double x) (.double y)
      | triple y =>
          simpa [EdmundsPeriodTwoBlock.render,
            EdmundsPeriodTwoRepeatedBlock.render,
            EdmundsPeriodTwoRepeatedBlock.toBlock] using
              laws.repeatedSwap (.double x) (.triple y)
  | triple x =>
      cases right with
      | single y =>
          simpa [EdmundsPeriodTwoBlock.render,
            edmundsPeriodTwoBlocksWordOfCons, Word.toList] using
              ListDerives.ofWord (laws.derivesSingleTriple y x).symm
      | double y =>
          simpa [EdmundsPeriodTwoBlock.render,
            EdmundsPeriodTwoRepeatedBlock.render,
            EdmundsPeriodTwoRepeatedBlock.toBlock] using
              laws.repeatedSwap (.triple x) (.double y)
      | triple y =>
          simpa [EdmundsPeriodTwoBlock.render,
            EdmundsPeriodTwoRepeatedBlock.render,
            EdmundsPeriodTwoRepeatedBlock.toBlock] using
              laws.repeatedSwap (.triple x) (.triple y)

end SemigroupBasis.EdmundsPeriodTwoTraceAdapter

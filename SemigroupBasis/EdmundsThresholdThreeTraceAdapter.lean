import SemigroupBasis.BlockTraceDerives
import SemigroupBasis.CoRoots.S5_530Normalization
import SemigroupBasis.Opposite
import SemigroupBasis.RetainedStateFourNormalizer

namespace SemigroupBasis.EdmundsThresholdThreeTraceAdapter

open SemigroupBasis.BlockTrace
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.S5_530
open SemigroupBasis.Examples

/-! ## Threshold-three retained-block parser -/

/-- Parse consecutive runs of length one, two, or at least three into retained
blocks. The normal-form theorem proves that the saturating branch is only used
for a run of exactly three. -/
private def blocksOfNormalList : List Nat → List RetainedBlock
  | [] => []
  | [x] => [.single x]
  | [x, y] =>
      if x = y then [.double x] else [.single x, .single y]
  | x :: y :: z :: xs =>
      if x = y then
        if x = z then
          .triple x :: blocksOfNormalList xs
        else
          .double x :: blocksOfNormalList (z :: xs)
      else
        .single x :: blocksOfNormalList (y :: z :: xs)
termination_by letters => letters.length

private theorem render_blocksOfNormalList
    {letters : List Nat} (normal : S5_530Normal letters) :
    renderRetainedBlocks (blocksOfNormalList letters) = letters := by
  induction normal with
  | nil =>
      simp [blocksOfNormalList, renderRetainedBlocks,
        renderEdmundsPeriodTwoBlocks]
  | single x xs normal xNotMem ih =>
      cases xs with
      | nil =>
          simp [blocksOfNormalList, renderRetainedBlocks,
            renderEdmundsPeriodTwoBlocks, EdmundsPeriodTwoBlock.render]
      | cons y ys =>
          have xNeY : x ≠ y := by
            intro equal
            subst y
            exact xNotMem (List.Mem.head ys)
          cases ys with
          | nil =>
              simp [blocksOfNormalList, xNeY, renderRetainedBlocks,
                renderEdmundsPeriodTwoBlocks,
                EdmundsPeriodTwoBlock.render]
          | cons z zs =>
              simp only [blocksOfNormalList, xNeY, ↓reduceIte,
                renderRetainedBlocks, renderEdmundsPeriodTwoBlocks,
                List.flatMap_cons, EdmundsPeriodTwoBlock.render]
              change
                [x] ++
                    renderRetainedBlocks
                      (blocksOfNormalList (y :: z :: zs)) =
                  x :: y :: z :: zs
              rw [ih]
              rfl
  | double x xs normal xNotMem ih =>
      cases xs with
      | nil =>
          simp [blocksOfNormalList, renderRetainedBlocks,
            renderEdmundsPeriodTwoBlocks, EdmundsPeriodTwoBlock.render]
      | cons y ys =>
          have xNeY : x ≠ y := by
            intro equal
            subst y
            exact xNotMem (List.Mem.head ys)
          simp only [blocksOfNormalList, xNeY, ↓reduceIte,
            renderRetainedBlocks, renderEdmundsPeriodTwoBlocks,
            List.flatMap_cons, EdmundsPeriodTwoBlock.render]
          change
            [x, x] ++
                renderRetainedBlocks (blocksOfNormalList (y :: ys)) =
              x :: x :: y :: ys
          rw [ih]
          rfl
  | triple x xs normal xNotMem ih =>
      simp only [blocksOfNormalList, ↓reduceIte,
        renderRetainedBlocks, renderEdmundsPeriodTwoBlocks,
        List.flatMap_cons, EdmundsPeriodTwoBlock.render]
      change
        [x, x, x] ++ renderRetainedBlocks (blocksOfNormalList xs) =
          x :: x :: x :: xs
      rw [ih]
      rfl

private theorem label_mem_blocksOfNormalList_iff
    {letters : List Nat} (normal : S5_530Normal letters) (label : Nat) :
    label ∈
        (blocksOfNormalList letters).map EdmundsPeriodTwoBlock.label ↔
      label ∈ letters := by
  induction normal with
  | nil =>
      simp [blocksOfNormalList]
  | single x xs normal xNotMem ih =>
      cases xs with
      | nil =>
          simp [blocksOfNormalList, EdmundsPeriodTwoBlock.label]
      | cons y ys =>
          have xNeY : x ≠ y := by
            intro equal
            subst y
            exact xNotMem (List.Mem.head ys)
          cases ys with
          | nil =>
              simp [blocksOfNormalList, xNeY,
                EdmundsPeriodTwoBlock.label]
          | cons z zs =>
              simp [blocksOfNormalList, xNeY,
                EdmundsPeriodTwoBlock.label, ih]
  | double x xs normal xNotMem ih =>
      cases xs with
      | nil =>
          simp [blocksOfNormalList, EdmundsPeriodTwoBlock.label]
      | cons y ys =>
          have xNeY : x ≠ y := by
            intro equal
            subst y
            exact xNotMem (List.Mem.head ys)
          simp [blocksOfNormalList, xNeY,
            EdmundsPeriodTwoBlock.label, ih]
  | triple x xs normal xNotMem ih =>
      simp [blocksOfNormalList, EdmundsPeriodTwoBlock.label, ih]

private theorem blocksOfNormalList_labelsNodup
    {letters : List Nat} (normal : S5_530Normal letters) :
    RetainedLabelsNodup (blocksOfNormalList letters) := by
  induction normal with
  | nil =>
      simp [blocksOfNormalList, RetainedLabelsNodup]
  | single x xs normal xNotMem ih =>
      cases xs with
      | nil =>
          simp [blocksOfNormalList, RetainedLabelsNodup,
            EdmundsPeriodTwoBlock.label]
      | cons y ys =>
          have xNeY : x ≠ y := by
            intro equal
            subst y
            exact xNotMem (List.Mem.head ys)
          cases ys with
          | nil =>
              simp [blocksOfNormalList, xNeY, RetainedLabelsNodup,
                EdmundsPeriodTwoBlock.label]
          | cons z zs =>
              unfold RetainedLabelsNodup at ih ⊢
              simp only [blocksOfNormalList, xNeY, ↓reduceIte,
                List.map_cons, EdmundsPeriodTwoBlock.label]
              exact List.nodup_cons.mpr
                (And.intro
                  (fun member =>
                    xNotMem
                      ((label_mem_blocksOfNormalList_iff normal x).mp
                        member))
                  ih)
  | double x xs normal xNotMem ih =>
      cases xs with
      | nil =>
          simp [blocksOfNormalList, RetainedLabelsNodup,
            EdmundsPeriodTwoBlock.label]
      | cons y ys =>
          have xNeY : x ≠ y := by
            intro equal
            subst y
            exact xNotMem (List.Mem.head ys)
          unfold RetainedLabelsNodup at ih ⊢
          simp only [blocksOfNormalList, xNeY, ↓reduceIte,
            List.map_cons, EdmundsPeriodTwoBlock.label]
          exact List.nodup_cons.mpr
            (And.intro
              (fun member =>
                xNotMem
                  ((label_mem_blocksOfNormalList_iff normal x).mp member))
              ih)
  | triple x xs normal xNotMem ih =>
      unfold RetainedLabelsNodup at ih ⊢
      simp only [blocksOfNormalList]
      exact List.nodup_cons.mpr
        (And.intro
          (fun member =>
            xNotMem
              ((label_mem_blocksOfNormalList_iff normal x).mp member))
          ih)

/-- The syntax-only normal-form data needed by a forward block-trace
certificate. -/
structure ParserSpec (source : Word Nat) where
  normalWord : Word Nat
  normalBlocks : List RetainedBlock
  renderNormal :
    renderRetainedBlocks normalBlocks = normalWord.toList
  labelsNodup : RetainedLabelsNodup normalBlocks
  sourceDerivesNormal : Derives s5_530Basis source normalWord

private theorem normalList_ne_nil (source : Word Nat) :
    s5_530NormalList source.toList ≠ [] := by
  cases source with
  | mk head tail =>
      simpa [Word.toList] using s5_530NormalList_cons_ne_nil head tail

/-- The word represented by the threshold-three first-occurrence normal list.
The empty branch is unreachable for a semigroup word. -/
def normalWord (source : Word Nat) : Word Nat :=
  match s5_530NormalList source.toList with
  | [] => source
  | head :: tail => s5_530WordOfCons head tail

/-- Parse the threshold-three first-occurrence normal list into retained
blocks. -/
def normalBlocks (source : Word Nat) : List RetainedBlock :=
  blocksOfNormalList (s5_530NormalList source.toList)

theorem normalWord_toList (source : Word Nat) :
    (normalWord source).toList = s5_530NormalList source.toList := by
  cases source with
  | mk sourceHead sourceTail =>
      cases normalEq :
          s5_530NormalList (Word.mk sourceHead sourceTail).toList with
      | nil =>
          exact False.elim
            (normalList_ne_nil (Word.mk sourceHead sourceTail) normalEq)
      | cons head tail =>
          change
            s5_530NormalList (sourceHead :: sourceTail) =
              head :: tail at normalEq
          simp [normalWord, normalEq, s5_530WordOfCons, Word.toList]

theorem render_normalBlocks (source : Word Nat) :
    renderRetainedBlocks (normalBlocks source) =
      (normalWord source).toList := by
  exact
    (render_blocksOfNormalList
      (s5_530NormalList_normal source.toList)).trans
        (normalWord_toList source).symm

theorem normalBlocks_labelsNodup (source : Word Nat) :
    RetainedLabelsNodup (normalBlocks source) :=
  blocksOfNormalList_labelsNodup
    (s5_530NormalList_normal source.toList)

theorem derives_normalWord (source : Word Nat) :
    Derives s5_530Basis source (normalWord source) := by
  have derivation := s5_530DerivesNormal source
  cases normalEq : s5_530NormalList source.toList with
  | nil =>
      exact False.elim (normalList_ne_nil source normalEq)
  | cons head tail =>
      rw [normalEq] at derivation
      simpa [normalWord, normalEq, s5_530WordOfCons] using derivation

/-- Complete mechanical parser data for the forward first-occurrence
orientation. -/
def parserSpec (source : Word Nat) : ParserSpec source where
  normalWord := normalWord source
  normalBlocks := normalBlocks source
  renderNormal := render_normalBlocks source
  labelsNodup := normalBlocks_labelsNodup source
  sourceDerivesNormal := derives_normalWord source

/-! ## Forward derivation transport -/

/-- Derivability of the two threshold-three syntax laws in a target basis. -/
structure SyntaxLawsDerivable (basis : List (Identity Nat)) where
  power : Derives basis s5_530PowerLaw.lhs s5_530PowerLaw.rhs
  gather : Derives basis s5_530GatherLaw.lhs s5_530GatherLaw.rhs

theorem SyntaxLawsDerivable.axiomDerives
    {basis : List (Identity Nat)}
    (laws : SyntaxLawsDerivable basis) :
    ∀ identity : Identity Nat,
      identity ∈ s5_530Basis →
        Derives basis identity.lhs identity.rhs := by
  intro identity member
  simp only [s5_530Basis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl
  · exact laws.power
  · exact laws.gather

theorem SyntaxLawsDerivable.transport
    {basis : List (Identity Nat)}
    (laws : SyntaxLawsDerivable basis)
    {source target : Word Nat}
    (derivation : Derives s5_530Basis source target) :
    Derives basis source target :=
  derivation.transport laws.axiomDerives

theorem ParserSpec.derivesNormalIn
    {source : Word Nat} (spec : ParserSpec source)
    {basis : List (Identity Nat)}
    (laws : SyntaxLawsDerivable basis) :
    Derives basis source spec.normalWord :=
  laws.transport spec.sourceDerivesNormal

/-! ## Reversed threshold-three parser and transport -/

/-- Rendering commutes with reversing a retained-block list because every
individual retained block is a constant-letter word. -/
theorem renderRetainedBlocks_reverse (blocks : List RetainedBlock) :
    renderRetainedBlocks blocks.reverse =
      (renderRetainedBlocks blocks).reverse := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      cases block <;>
        simpa [renderRetainedBlocks, renderEdmundsPeriodTwoBlocks,
          EdmundsPeriodTwoBlock.render] using ih

private theorem nodup_reverse
    {alpha : Type} {items : List alpha}
    (nodup : items.Nodup) : items.reverse.Nodup := by
  change items.reverse.Pairwise (fun left right : alpha => left ≠ right)
  rw [List.pairwise_reverse]
  exact nodup.imp fun different => Ne.symm different

/-- Normal-form data for the opposite, last-occurrence orientation. -/
structure ReversedParserSpec (source : Word Nat) where
  normalWord : Word Nat
  normalBlocks : List RetainedBlock
  renderNormal :
    renderRetainedBlocks normalBlocks = normalWord.toList
  labelsNodup : RetainedLabelsNodup normalBlocks
  sourceDerivesNormal :
    Derives (reversedBasis s5_530Basis) source normalWord

/-- Reverse the first-occurrence normal form of the reversed source word. -/
def reversedNormalWord (source : Word Nat) : Word Nat :=
  (normalWord source.reverse).reverse

/-- Reverse the retained-block parse of the reversed source word. -/
def reversedNormalBlocks (source : Word Nat) : List RetainedBlock :=
  (normalBlocks source.reverse).reverse

theorem reversedNormalWord_toList (source : Word Nat) :
    (reversedNormalWord source).toList =
      (s5_530NormalList source.reverse.toList).reverse := by
  simp [reversedNormalWord, normalWord_toList]

theorem render_reversedNormalBlocks (source : Word Nat) :
    renderRetainedBlocks (reversedNormalBlocks source) =
      (reversedNormalWord source).toList := by
  simp [reversedNormalBlocks, reversedNormalWord,
    renderRetainedBlocks_reverse, render_normalBlocks]

theorem reversedNormalBlocks_labelsNodup (source : Word Nat) :
    RetainedLabelsNodup (reversedNormalBlocks source) := by
  simpa [reversedNormalBlocks, RetainedLabelsNodup] using
    nodup_reverse (normalBlocks_labelsNodup source.reverse)

theorem derives_reversedNormalWord (source : Word Nat) :
    Derives (reversedBasis s5_530Basis)
      source (reversedNormalWord source) := by
  have derivation := (derives_normalWord source.reverse).reverse
  simpa [reversedNormalWord] using derivation

/-- Complete mechanical parser data for the reversed orientation. -/
def reversedParserSpec (source : Word Nat) : ReversedParserSpec source where
  normalWord := reversedNormalWord source
  normalBlocks := reversedNormalBlocks source
  renderNormal := render_reversedNormalBlocks source
  labelsNodup := reversedNormalBlocks_labelsNodup source
  sourceDerivesNormal := derives_reversedNormalWord source

/-- Derivability of the reversed threshold-three syntax laws in a target
basis. -/
structure ReversedSyntaxLawsDerivable
    (basis : List (Identity Nat)) where
  power : Derives basis
    s5_530PowerLaw.lhs.reverse s5_530PowerLaw.rhs.reverse
  gather : Derives basis
    s5_530GatherLaw.lhs.reverse s5_530GatherLaw.rhs.reverse

theorem ReversedSyntaxLawsDerivable.axiomDerives
    {basis : List (Identity Nat)}
    (laws : ReversedSyntaxLawsDerivable basis) :
    ∀ identity : Identity Nat,
      identity ∈ reversedBasis s5_530Basis →
        Derives basis identity.lhs identity.rhs := by
  intro identity member
  simp only [reversedBasis, s5_530Basis, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simpa [Identity.reversed] using laws.power
  · simpa [Identity.reversed] using laws.gather

theorem ReversedSyntaxLawsDerivable.transport
    {basis : List (Identity Nat)}
    (laws : ReversedSyntaxLawsDerivable basis)
    {source target : Word Nat}
    (derivation :
      Derives (reversedBasis s5_530Basis) source target) :
    Derives basis source target :=
  derivation.transport laws.axiomDerives

theorem ReversedParserSpec.derivesNormalIn
    {source : Word Nat} (spec : ReversedParserSpec source)
    {basis : List (Identity Nat)}
    (laws : ReversedSyntaxLawsDerivable basis) :
    Derives basis source spec.normalWord :=
  laws.transport spec.sourceDerivesNormal

/-! ## Repeated retained-block swaps -/

def doubleDoubleXY : Word Nat :=
  s5_530WordOfCons 0 [0, 1, 1]

def doubleDoubleYX : Word Nat :=
  s5_530WordOfCons 1 [1, 0, 0]

def doubleTripleXY : Word Nat :=
  s5_530WordOfCons 0 [0, 1, 1, 1]

def doubleTripleYX : Word Nat :=
  s5_530WordOfCons 1 [1, 1, 0, 0]

def tripleTripleXY : Word Nat :=
  s5_530WordOfCons 0 [0, 0, 1, 1, 1]

def tripleTripleYX : Word Nat :=
  s5_530WordOfCons 1 [1, 1, 0, 0, 0]

/-- The three canonical laws needed to commute any two retained repeated
blocks. -/
structure RepeatedSwapLaws (basis : List (Identity Nat)) where
  doubleDouble : Derives basis doubleDoubleXY doubleDoubleYX
  doubleTriple : Derives basis doubleTripleXY doubleTripleYX
  tripleTriple : Derives basis tripleTripleXY tripleTripleYX

private def instantiateTwoWords
    (left right : Word Nat) : Nat → Word Nat
  | 0 => left
  | 1 => right
  | n + 2 => Word.singleton (n + 2)

/-- Canonical double/double commutation with arbitrary nonempty words in
place of the two block labels. -/
theorem RepeatedSwapLaws.derivesDoubleDoubleWords
    {basis : List (Identity Nat)}
    (laws : RepeatedSwapLaws basis) (left right : Word Nat) :
    Derives basis
      ((left ++ left) ++ (right ++ right))
      ((right ++ right) ++ (left ++ left)) := by
  have derivation :=
    Derives.subst laws.doubleDouble (instantiateTwoWords left right)
  simpa [doubleDoubleXY, doubleDoubleYX, instantiateTwoWords,
    s5_530WordOfCons, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using derivation

/-- Canonical double/triple commutation with arbitrary nonempty words in
place of the two block labels. -/
theorem RepeatedSwapLaws.derivesDoubleTripleWords
    {basis : List (Identity Nat)}
    (laws : RepeatedSwapLaws basis) (left right : Word Nat) :
    Derives basis
      ((left ++ left) ++ ((right ++ right) ++ right))
      (((right ++ right) ++ right) ++ (left ++ left)) := by
  have derivation :=
    Derives.subst laws.doubleTriple (instantiateTwoWords left right)
  simpa [doubleTripleXY, doubleTripleYX, instantiateTwoWords,
    s5_530WordOfCons, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using derivation

/-- Canonical triple/triple commutation with arbitrary nonempty words in
place of the two block labels. -/
theorem RepeatedSwapLaws.derivesTripleTripleWords
    {basis : List (Identity Nat)}
    (laws : RepeatedSwapLaws basis) (left right : Word Nat) :
    Derives basis
      (((left ++ left) ++ left) ++ ((right ++ right) ++ right))
      (((right ++ right) ++ right) ++ ((left ++ left) ++ left)) := by
  have derivation :=
    Derives.subst laws.tripleTriple (instantiateTwoWords left right)
  simpa [tripleTripleXY, tripleTripleYX, instantiateTwoWords,
    s5_530WordOfCons, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using derivation

theorem RepeatedSwapLaws.derivesDoubleDouble
    {basis : List (Identity Nat)}
    (laws : RepeatedSwapLaws basis) (x y : Nat) :
    Derives basis
      (s5_530WordOfCons x [x, y, y])
      (s5_530WordOfCons y [y, x, x]) := by
  have derivation :=
    Derives.subst laws.doubleDouble
      (instantiateTwoWords (Word.singleton x) (Word.singleton y))
  simpa [doubleDoubleXY, doubleDoubleYX, instantiateTwoWords,
    s5_530WordOfCons, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using derivation

theorem RepeatedSwapLaws.derivesDoubleTriple
    {basis : List (Identity Nat)}
    (laws : RepeatedSwapLaws basis) (x y : Nat) :
    Derives basis
      (s5_530WordOfCons x [x, y, y, y])
      (s5_530WordOfCons y [y, y, x, x]) := by
  have derivation :=
    Derives.subst laws.doubleTriple
      (instantiateTwoWords (Word.singleton x) (Word.singleton y))
  simpa [doubleTripleXY, doubleTripleYX, instantiateTwoWords,
    s5_530WordOfCons, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using derivation

theorem RepeatedSwapLaws.derivesTripleTriple
    {basis : List (Identity Nat)}
    (laws : RepeatedSwapLaws basis) (x y : Nat) :
    Derives basis
      (s5_530WordOfCons x [x, x, y, y, y])
      (s5_530WordOfCons y [y, y, x, x, x]) := by
  have derivation :=
    Derives.subst laws.tripleTriple
      (instantiateTwoWords (Word.singleton x) (Word.singleton y))
  simpa [tripleTripleXY, tripleTripleYX, instantiateTwoWords,
    s5_530WordOfCons, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using derivation

private def doubleWord (x : Nat) : Word Nat :=
  s5_530WordOfCons x [x]

theorem RepeatedSwapLaws.derivesDoubleFour
    {basis : List (Identity Nat)}
    (laws : RepeatedSwapLaws basis) (x y : Nat) :
    Derives basis
      (s5_530WordOfCons x [x, y, y, y, y])
      (s5_530WordOfCons y [y, y, y, x, x]) := by
  have derivation :=
    laws.derivesDoubleDoubleWords
      (Word.singleton x) (doubleWord y)
  simpa [doubleWord, s5_530WordOfCons, Word.append,
    Word.singleton, Word.append_assoc] using derivation

theorem RepeatedSwapLaws.derivesFourTriple
    {basis : List (Identity Nat)}
    (laws : RepeatedSwapLaws basis) (x y : Nat) :
    Derives basis
      (s5_530WordOfCons x [x, x, x, y, y, y])
      (s5_530WordOfCons y [y, y, x, x, x, x]) := by
  have derivation :=
    laws.derivesDoubleTripleWords
      (doubleWord x) (Word.singleton y)
  simpa [doubleWord, s5_530WordOfCons, Word.append,
    Word.singleton, Word.append_assoc] using derivation

theorem RepeatedSwapLaws.derivesFourFour
    {basis : List (Identity Nat)}
    (laws : RepeatedSwapLaws basis) (x y : Nat) :
    Derives basis
      (s5_530WordOfCons x [x, x, x, y, y, y, y])
      (s5_530WordOfCons y [y, y, y, x, x, x, x]) := by
  have derivation :=
    laws.derivesDoubleDoubleWords (doubleWord x) (doubleWord y)
  simpa [doubleWord, s5_530WordOfCons, Word.append,
    Word.singleton, Word.append_assoc] using derivation

/-- A dependent pair has a singleton state at one of its endpoints. -/
def stateOneDependent (left right : Nat) : Prop :=
  left = 1 ∨ right = 1

/-- Repeated states within a fixed finite state count commute. -/
def repeatedCommutesWithin
    (stateCount left right : Nat) : Prop :=
  left ≠ 1 ∧ right ≠ 1 ∧
    left ≤ stateCount ∧ right ≤ stateCount

/-- The three-state relation used by the threshold-three parser. -/
def repeatedCommutes : Nat → Nat → Prop :=
  repeatedCommutesWithin 3

/-- The four-state relation consumed by `RetainedStateFour` profiles. -/
def stateFourRepeatedCommutes : Nat → Nat → Prop :=
  repeatedCommutesWithin 4

theorem not_repeatedCommutesWithin_iff_stateOneDependent
    {stateCount left right : Nat}
    (leftBound : left ≤ stateCount)
    (rightBound : right ≤ stateCount) :
    ¬ repeatedCommutesWithin stateCount left right ↔
      stateOneDependent left right := by
  constructor
  · intro blocked
    by_cases leftOne : left = 1
    · exact Or.inl leftOne
    · by_cases rightOne : right = 1
      · exact Or.inr rightOne
      · exact False.elim <|
          blocked ⟨leftOne, rightOne, leftBound, rightBound⟩
  · intro dependent allowed
    rcases dependent with leftOne | rightOne
    · exact allowed.1 leftOne
    · exact allowed.2.1 rightOne

/-- The three repeated-block laws derive all four authorized adjacent swaps
between exponent states two and three. -/
theorem RepeatedSwapLaws.adjacentSwap
    {basis : List (Identity Nat)}
    (laws : RepeatedSwapLaws basis) :
    AdjacentSwapDerivable basis repeatedCommutes := by
  intro left right allowed
  cases left with
  | single x =>
      cases right <;>
        simp [BlocksIndependent, repeatedCommutes,
          repeatedCommutesWithin,
          EdmundsPeriodTwoBlock.exponent] at allowed
  | double x =>
      cases right with
      | single y =>
          simp [BlocksIndependent, repeatedCommutes,
            repeatedCommutesWithin,
            EdmundsPeriodTwoBlock.exponent] at allowed
      | double y =>
          simpa [EdmundsPeriodTwoBlock.render,
            s5_530WordOfCons, Word.toList] using
              ListDerives.ofWord (laws.derivesDoubleDouble x y)
      | triple y =>
          simpa [EdmundsPeriodTwoBlock.render,
            s5_530WordOfCons, Word.toList] using
              ListDerives.ofWord (laws.derivesDoubleTriple x y)
  | triple x =>
      cases right with
      | single y =>
          simp [BlocksIndependent, repeatedCommutes,
            repeatedCommutesWithin,
            EdmundsPeriodTwoBlock.exponent] at allowed
      | double y =>
          simpa [EdmundsPeriodTwoBlock.render,
            s5_530WordOfCons, Word.toList] using
              ListDerives.ofWord
                (laws.derivesDoubleTriple y x).symm
      | triple y =>
          simpa [EdmundsPeriodTwoBlock.render,
            s5_530WordOfCons, Word.toList] using
              ListDerives.ofWord (laws.derivesTripleTriple x y)

/-- To establish dependent-order preservation for threshold-three traces, it
is enough to handle pairs with a singleton endpoint. -/
theorem sameDependentOrder_of_stateOne
    {source target : List RetainedBlock}
    (stateOneOrder :
      ∀ left right,
        left ∈ source →
        right ∈ source →
        stateOneDependent left.exponent right.exponent →
        (Precedes left right source ↔ Precedes left right target)) :
    SameDependentOrder repeatedCommutes source target := by
  intro left right leftMember rightMember blocked
  have leftBound : left.exponent ≤ 3 := by
    cases left <;> simp [EdmundsPeriodTwoBlock.exponent]
  have rightBound : right.exponent ≤ 3 := by
    cases right <;> simp [EdmundsPeriodTwoBlock.exponent]
  apply stateOneOrder left right leftMember rightMember
  apply
    (not_repeatedCommutesWithin_iff_stateOneDependent
      leftBound rightBound).mp
  simpa [BlocksIndependent, repeatedCommutes] using blocked

/-! ## State-four reuse -/

/-- The same three canonical block laws commute every pair of repeated states
two, three, and four. State four is obtained by substituting a double word
into the double/double or double/triple law. -/
theorem RepeatedSwapLaws.stateFourAdjacentSwap
    {basis : List (Identity Nat)}
    (laws : RepeatedSwapLaws basis) :
    SemigroupBasis.RetainedStateFour.AdjacentSwapDerivable
      basis stateFourRepeatedCommutes := by
  intro left right allowed
  rcases left with ⟨x, leftState⟩
  rcases right with ⟨y, rightState⟩
  cases leftState with
  | one =>
      cases rightState <;>
        simp [SemigroupBasis.RetainedStateFour.BlocksIndependent,
          stateFourRepeatedCommutes, repeatedCommutesWithin,
          SemigroupBasis.RetainedStateFour.State.exponent] at allowed
  | two =>
      cases rightState with
      | one =>
          simp [SemigroupBasis.RetainedStateFour.BlocksIndependent,
            stateFourRepeatedCommutes, repeatedCommutesWithin,
            SemigroupBasis.RetainedStateFour.State.exponent] at allowed
      | two =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            SemigroupBasis.RetainedStateFour.State.exponent,
            s5_530WordOfCons, Word.toList] using
              ListDerives.ofWord (laws.derivesDoubleDouble x y)
      | three =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            SemigroupBasis.RetainedStateFour.State.exponent,
            s5_530WordOfCons, Word.toList] using
              ListDerives.ofWord (laws.derivesDoubleTriple x y)
      | four =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            SemigroupBasis.RetainedStateFour.State.exponent,
            s5_530WordOfCons, Word.toList] using
              ListDerives.ofWord (laws.derivesDoubleFour x y)
  | three =>
      cases rightState with
      | one =>
          simp [SemigroupBasis.RetainedStateFour.BlocksIndependent,
            stateFourRepeatedCommutes, repeatedCommutesWithin,
            SemigroupBasis.RetainedStateFour.State.exponent] at allowed
      | two =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            SemigroupBasis.RetainedStateFour.State.exponent,
            s5_530WordOfCons, Word.toList] using
              ListDerives.ofWord
                (laws.derivesDoubleTriple y x).symm
      | three =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            SemigroupBasis.RetainedStateFour.State.exponent,
            s5_530WordOfCons, Word.toList] using
              ListDerives.ofWord (laws.derivesTripleTriple x y)
      | four =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            SemigroupBasis.RetainedStateFour.State.exponent,
            s5_530WordOfCons, Word.toList] using
              ListDerives.ofWord
                (laws.derivesFourTriple y x).symm
  | four =>
      cases rightState with
      | one =>
          simp [SemigroupBasis.RetainedStateFour.BlocksIndependent,
            stateFourRepeatedCommutes, repeatedCommutesWithin,
            SemigroupBasis.RetainedStateFour.State.exponent] at allowed
      | two =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            SemigroupBasis.RetainedStateFour.State.exponent,
            s5_530WordOfCons, Word.toList] using
              ListDerives.ofWord
                (laws.derivesDoubleFour y x).symm
      | three =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            SemigroupBasis.RetainedStateFour.State.exponent,
            s5_530WordOfCons, Word.toList] using
              ListDerives.ofWord (laws.derivesFourTriple x y)
      | four =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            SemigroupBasis.RetainedStateFour.State.exponent,
            s5_530WordOfCons, Word.toList] using
              ListDerives.ofWord (laws.derivesFourFour x y)

/-- Profile-generic dependent-order reducer for state-four normal forms. A
future semantic separator only has to preserve order when either endpoint is
in state one. -/
theorem retainedStateFourSameDependentOrder_of_stateOne
    {source target : List SemigroupBasis.RetainedStateFour.Block}
    (stateOneOrder :
      ∀ left right,
        left ∈ source →
        right ∈ source →
        stateOneDependent
          left.state.exponent right.state.exponent →
        (SemigroupBasis.RetainedStateFour.Precedes left right source ↔
          SemigroupBasis.RetainedStateFour.Precedes
            left right target)) :
    SemigroupBasis.RetainedStateFour.SameDependentOrder
      stateFourRepeatedCommutes source target := by
  intro left right leftMember rightMember blocked
  have leftBound : left.state.exponent ≤ 4 := by
    cases left.state <;>
      simp [SemigroupBasis.RetainedStateFour.State.exponent]
  have rightBound : right.state.exponent ≤ 4 := by
    cases right.state <;>
      simp [SemigroupBasis.RetainedStateFour.State.exponent]
  apply stateOneOrder left right leftMember rightMember
  apply
    (not_repeatedCommutesWithin_iff_stateOneDependent
      leftBound rightBound).mp
  simpa [SemigroupBasis.RetainedStateFour.BlocksIndependent,
    stateFourRepeatedCommutes] using blocked

/-- Complete forward mechanical laws: threshold-three normalization plus
repeated-block crossings. -/
structure ForwardTraceLaws (basis : List (Identity Nat)) where
  syntaxLaws : SyntaxLawsDerivable basis
  swapLaws : RepeatedSwapLaws basis

/-- Complete reversed mechanical laws: opposite threshold-three normalization
plus the same repeated-block crossings. -/
structure ReversedTraceLaws (basis : List (Identity Nat)) where
  syntaxLaws : ReversedSyntaxLawsDerivable basis
  swapLaws : RepeatedSwapLaws basis

end SemigroupBasis.EdmundsThresholdThreeTraceAdapter

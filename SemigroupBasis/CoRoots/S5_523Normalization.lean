import SemigroupBasis.Examples.LeftRegularBandThree
import SemigroupBasis.Opposite
import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_530Normalization

namespace SemigroupBasis.CoRoots.S5_523

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxx : Word Nat := w 0 [0, 0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def xyy : Word Nat := w 0 [1, 1]
def xxxy : Word Nat := w 0 [0, 0, 1]
def xyz : Word Nat := w 0 [1, 2]
def xxyz : Word Nat := w 0 [0, 1, 2]

def powerLaw : Identity Nat := ⟨xxx, xxxx⟩
def gatherLaw : Identity Nat := ⟨xxy, xyx⟩
def transferLaw : Identity Nat := ⟨xxy, xyy⟩
def prefixCapLaw : Identity Nat := ⟨xxy, xxxy⟩
def longInsertionLaw : Identity Nat := ⟨xyz, xxyz⟩

/-- The exact five-law basis shared by `S5_523` and `S5_539`. -/
def basis : List (Identity Nat) :=
  [powerLaw, gatherLaw, transferLaw, prefixCapLaw,
    longInsertionLaw]

def yxx : Word Nat := w 1 [0, 0]
def yyx : Word Nat := w 1 [1, 0]
def yxxx : Word Nat := w 1 [0, 0, 0]
def zyx : Word Nat := w 2 [1, 0]
def zyxx : Word Nat := w 2 [1, 0, 0]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def expectedOppositeBasis : List (Identity Nat) :=
  [⟨xxx, xxxx⟩, ⟨yxx, xyx⟩, ⟨yxx, yyx⟩,
    ⟨yxx, yxxx⟩, ⟨zyx, zyxx⟩]

theorem oppositeBasis_eq_expected :
    oppositeBasis = expectedOppositeBasis := by
  rfl

private def instantiateThree
    (u v q : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => q
  | n + 3 => Word.singleton (n + 3)

/-- Contract four consecutive copies of a nonempty block to three. -/
theorem derivesPowerContraction (u : Word Nat) :
    Derives basis
      (((u ++ u) ++ u) ++ u)
      ((u ++ u) ++ u) := by
  have base : Derives basis xxxx xxx :=
    Derives.symm <|
      Derives.fromBasis (e := powerLaw) <| by
        simp [basis]
  have substituted :=
    Derives.subst base (instantiateThree u u u)
  simpa [powerLaw, xxxx, xxx, w, instantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Gather a later copy of a block next to its first copy. -/
theorem derivesGather (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ u)
      ((u ++ u) ++ v) := by
  have base : Derives basis xyx xxy :=
    Derives.symm <|
      Derives.fromBasis (e := gatherLaw) <| by
        simp [basis]
  have substituted :=
    Derives.subst base (instantiateThree u v v)
  simpa [gatherLaw, xyx, xxy, w, instantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Transfer one copy between adjacent nonempty blocks. -/
theorem derivesTransfer (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ v)
      ((u ++ v) ++ v) := by
  have base : Derives basis xxy xyy :=
    Derives.fromBasis (e := transferLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThree u v v)
  simpa [transferLaw, xxy, xyy, w, instantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Cap a repeated first block before a nonempty suffix. -/
theorem derivesPrefixCap (u v : Word Nat) :
    Derives basis
      (((u ++ u) ++ u) ++ v)
      ((u ++ u) ++ v) := by
  have base : Derives basis xxxy xxy :=
    Derives.symm <|
      Derives.fromBasis (e := prefixCapLaw) <| by
        simp [basis]
  have substituted :=
    Derives.subst base (instantiateThree u v v)
  simpa [prefixCapLaw, xxxy, xxy, w, instantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Remove a duplicate first block from a product with two later blocks. -/
theorem derivesLongContraction (u v q : Word Nat) :
    Derives basis
      (((u ++ u) ++ v) ++ q)
      ((u ++ v) ++ q) := by
  have base : Derives basis xxyz xyz :=
    Derives.symm <|
      Derives.fromBasis (e := longInsertionLaw) <| by
        simp [basis]
  have substituted :=
    Derives.subst base (instantiateThree u v q)
  simpa [longInsertionLaw, xxyz, xyz, w, instantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Canonical list from the published long first-occurrence certificate.
Lengths one and two are literal. Longer unary words become a cube, longer
two-variable words become `xxy`, and words with at least three distinct
variables become their duplicate-free first-occurrence sequence. -/
def longFirstOccurrenceNormalList : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | [x, y] => [x, y]
  | x :: y :: z :: rest =>
      match firstOccurrenceSequence (x :: y :: z :: rest) with
      | [a] => [a, a, a]
      | [a, b] => [a, a, b]
      | order => order

def longFirstOccurrenceSignature (word : Word Nat) : List Nat :=
  longFirstOccurrenceNormalList word.toList

private theorem longFirstOccurrenceNormalList_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    longFirstOccurrenceNormalList (x :: xs) ≠ [] := by
  cases xs with
  | nil => simp [longFirstOccurrenceNormalList]
  | cons y ys =>
      cases ys with
      | nil => simp [longFirstOccurrenceNormalList]
      | cons z zs =>
          have sourceNonempty :
              firstOccurrenceSequence (x :: y :: z :: zs) ≠ [] := by
            simp [firstOccurrenceSequence]
          cases h : firstOccurrenceSequence (x :: y :: z :: zs) with
          | nil => exact False.elim (sourceNonempty h)
          | cons a as =>
              cases as with
              | nil => simp [longFirstOccurrenceNormalList, h]
              | cons b bs =>
                  cases bs with
                  | nil => simp [longFirstOccurrenceNormalList, h]
                  | cons c cs => simp [longFirstOccurrenceNormalList, h]

def SameLongFirstOccurrenceSignature
    (left right : Word Nat) : Prop :=
  longFirstOccurrenceSignature left =
    longFirstOccurrenceSignature right

/-- The exact unrestricted normalization interface. The conditional API is
kept stable; `longFirstOccurrenceDerivationalCompleteness` below constructs
it from the five-law block normalizer. -/
def LongFirstOccurrenceDerivationalCompleteness : Prop :=
  ∀ left right : Word Nat,
    SameLongFirstOccurrenceSignature left right →
      Derives basis left right

private theorem s5_530AxiomDerives
    (identity : Identity Nat)
    (member :
      identity ∈
        SemigroupBasis.CoRoots.S5_530.s5_530Basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_530.s5_530Basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simpa [SemigroupBasis.CoRoots.S5_530.s5_530PowerLaw,
      SemigroupBasis.CoRoots.S5_530.s5_530XXX,
      SemigroupBasis.CoRoots.S5_530.s5_530XXXX,
      powerLaw, xxx, xxxx, w] using
        (Derives.fromBasis (basis := basis) (e := powerLaw) (by
          simp [basis]))
  · simpa [SemigroupBasis.CoRoots.S5_530.s5_530GatherLaw,
      SemigroupBasis.CoRoots.S5_530.s5_530XXY,
      SemigroupBasis.CoRoots.S5_530.s5_530XYX,
      gatherLaw, xxy, xyx, w] using
        (Derives.fromBasis (basis := basis) (e := gatherLaw) (by
          simp [basis]))

/-- The established two-law block normalizer, transported into the exact
five-law basis. -/
theorem derivesGatheredBlockNormal (word : Word Nat) :
    match
        SemigroupBasis.CoRoots.S5_530.s5_530NormalList word.toList with
    | [] => False
    | x :: xs =>
        Derives basis word
          (SemigroupBasis.CoRoots.S5_530.s5_530WordOfCons x xs) := by
  have sourceNormal :=
    SemigroupBasis.CoRoots.S5_530.s5_530DerivesNormal word
  cases normalEq :
      SemigroupBasis.CoRoots.S5_530.s5_530NormalList word.toList with
  | nil =>
      rw [normalEq] at sourceNormal
      exact sourceNormal
  | cons normalHead normalTail =>
      rw [normalEq] at sourceNormal
      exact sourceNormal.transport s5_530AxiomDerives

/-- Remove one doubled interior block. The transfer law moves the duplicate
onto the nonempty prefix, where the long insertion law contracts it. -/
theorem derivesInteriorContraction (pre block suffix : Word Nat) :
    Derives basis
      (((pre ++ block) ++ block) ++ suffix)
      ((pre ++ block) ++ suffix) := by
  have shifted :=
    Derives.appendRight
      (Derives.symm (derivesTransfer pre block)) suffix
  exact Derives.trans
    (by simpa [Word.append_assoc] using shifted)
    (derivesLongContraction pre block suffix)

/-- Remove one doubled final block when two nonempty blocks precede it. -/
theorem derivesFinalContraction
    (first second block : Word Nat) :
    Derives basis
      (((first ++ second) ++ block) ++ block)
      ((first ++ second) ++ block) := by
  have shifted :=
    Derives.prepend first <|
      Derives.symm (derivesTransfer second block)
  exact Derives.trans
    (by simpa [Word.append_assoc] using shifted)
    (derivesInteriorContraction first second block)

private def listWord (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private theorem listDerivesTransferReverse (x y : Nat) :
    ListDerives basis [x, y, y] [x, x, y] := by
  exact ListDerives.ofWord <| by
    simpa [listWord, Word.singleton, Word.append, Word.append_assoc] using
      Derives.symm
        (derivesTransfer (Word.singleton x) (Word.singleton y))

private theorem listDerivesPrefixCap (x y : Nat) :
    ListDerives basis [x, x, x, y] [x, x, y] := by
  exact ListDerives.ofWord <| by
    simpa [listWord, Word.singleton, Word.append, Word.append_assoc] using
      derivesPrefixCap (Word.singleton x) (Word.singleton y)

private theorem listDerivesOneThree (x y : Nat) :
    ListDerives basis [x, y, y, y] [x, x, y] := by
  have first := (listDerivesTransferReverse x y).append [y]
  have second := (listDerivesTransferReverse x y).prepend [x]
  exact first.trans (second.trans (listDerivesPrefixCap x y))

private theorem listDerivesTwoTwo (x y : Nat) :
    ListDerives basis [x, x, y, y] [x, x, y] := by
  exact
    ((listDerivesTransferReverse x y).prepend [x]).trans
      (listDerivesPrefixCap x y)

private theorem listDerivesTwoThree (x y : Nat) :
    ListDerives basis [x, x, y, y, y] [x, x, y] := by
  have reduced := (listDerivesOneThree x y).prepend [x]
  exact reduced.trans (listDerivesPrefixCap x y)

private theorem listDerivesThreeTwo (x y : Nat) :
    ListDerives basis [x, x, x, y, y] [x, x, y] := by
  exact
    ((listDerivesPrefixCap x y).append [y]).trans
      (listDerivesTwoTwo x y)

private theorem listDerivesThreeThree (x y : Nat) :
    ListDerives basis [x, x, x, y, y, y] [x, x, y] := by
  exact
    ((listDerivesPrefixCap x y).append [y, y]).trans
      (listDerivesTwoThree x y)

private inductive BlockSize : Type where
  | one
  | two
  | three

private def renderBlock : BlockSize → Nat → List Nat
  | .one, x => [x]
  | .two, x => [x, x]
  | .three, x => [x, x, x]

private theorem renderBlock_ne_nil
    (size : BlockSize) (x : Nat) :
    renderBlock size x ≠ [] := by
  cases size <;> simp [renderBlock]

private theorem listDerivesTwoBlock
    (firstSize secondSize : BlockSize) (x y : Nat)
    (notBothOne :
      firstSize ≠ .one ∨ secondSize ≠ .one) :
    ListDerives basis
      (renderBlock firstSize x ++ renderBlock secondSize y)
      [x, x, y] := by
  cases firstSize <;> cases secondSize
  · exact False.elim <| notBothOne.elim (fun h => h rfl) (fun h => h rfl)
  · simpa [renderBlock] using listDerivesTransferReverse x y
  · simpa [renderBlock] using listDerivesOneThree x y
  · exact ListDerives.refl [x, x, y]
  · simpa [renderBlock] using listDerivesTwoTwo x y
  · simpa [renderBlock] using listDerivesTwoThree x y
  · simpa [renderBlock] using listDerivesPrefixCap x y
  · simpa [renderBlock] using listDerivesThreeTwo x y
  · simpa [renderBlock] using listDerivesThreeThree x y

private theorem mem_firstOccurrenceSequence_iff
    (letter : Nat) :
    ∀ letters : List Nat,
      letter ∈ firstOccurrenceSequence letters ↔ letter ∈ letters
  | [] => by simp [firstOccurrenceSequence]
  | x :: xs => by
      by_cases equal : letter = x
      · subst letter
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal,
          mem_firstOccurrenceSequence_iff letter xs]

private theorem firstOccurrences_single
    {x : Nat} {xs : List Nat} (notMem : x ∉ xs) :
    firstOccurrenceSequence (x :: xs) =
      x :: firstOccurrenceSequence xs := by
  simp only [firstOccurrenceSequence]
  congr 1
  apply List.filter_eq_self.mpr
  intro y member
  simp only [decide_eq_true_eq]
  intro equal
  subst y
  exact notMem <|
    (mem_firstOccurrenceSequence_iff x xs).mp member

private theorem firstOccurrences_double
    {x : Nat} {xs : List Nat} (notMem : x ∉ xs) :
    firstOccurrenceSequence (x :: x :: xs) =
      x :: firstOccurrenceSequence xs := by
  have filtered :
      (firstOccurrenceSequence xs).filter
          (fun y => decide (y ≠ x)) = firstOccurrenceSequence xs := by
    apply List.filter_eq_self.mpr
    intro y member
    simp only [decide_eq_true_eq]
    intro equal
    subst y
    exact notMem <|
      (mem_firstOccurrenceSequence_iff x xs).mp member
  rw [firstOccurrenceSequence, firstOccurrences_single notMem]
  rw [List.filter_cons_of_neg (by simp)]
  exact congrArg (List.cons x) filtered

private theorem firstOccurrences_triple
    {x : Nat} {xs : List Nat} (notMem : x ∉ xs) :
    firstOccurrenceSequence (x :: x :: x :: xs) =
      x :: firstOccurrenceSequence xs := by
  have filtered :
      (firstOccurrenceSequence xs).filter
          (fun y => decide (y ≠ x)) = firstOccurrenceSequence xs := by
    apply List.filter_eq_self.mpr
    intro y member
    simp only [decide_eq_true_eq]
    intro equal
    subst y
    exact notMem <|
      (mem_firstOccurrenceSequence_iff x xs).mp member
  rw [firstOccurrenceSequence, firstOccurrences_double notMem]
  rw [List.filter_cons_of_neg (by simp)]
  exact congrArg (List.cons x) filtered

private theorem firstOccurrences_renderBlock
    (size : BlockSize) {x : Nat} {xs : List Nat}
    (notMem : x ∉ xs) :
    firstOccurrenceSequence (renderBlock size x ++ xs) =
      x :: firstOccurrenceSequence xs := by
  cases size
  · simpa [renderBlock] using firstOccurrences_single notMem
  · simpa [renderBlock] using firstOccurrences_double notMem
  · simpa [renderBlock] using firstOccurrences_triple notMem

private theorem normal_count_le_three
    {letters : List Nat}
    (normal :
      SemigroupBasis.CoRoots.S5_530.S5_530Normal letters)
    (tested : Nat) :
    letters.count tested ≤ 3 := by
  induction normal with
  | nil => simp
  | single x xs _ xNotMem ih =>
      by_cases equal : tested = x
      · subst tested
        simp [List.count_eq_zero.mpr xNotMem]
      · simpa [List.count_cons_of_ne (Ne.symm equal)] using ih
  | double x xs _ xNotMem ih =>
      by_cases equal : tested = x
      · subst tested
        simp [List.count_eq_zero.mpr xNotMem]
      · simpa [List.count_cons_of_ne (Ne.symm equal)] using ih
  | triple x xs _ xNotMem ih =>
      by_cases equal : tested = x
      · subst tested
        simp [List.count_eq_zero.mpr xNotMem]
      · simpa [List.count_cons_of_ne (Ne.symm equal)] using ih

private theorem normal_count_pos_of_mem_firstOccurrences
    {letters : List Nat}
    (normal :
      SemigroupBasis.CoRoots.S5_530.S5_530Normal letters)
    {tested : Nat}
    (member : tested ∈ firstOccurrenceSequence letters) :
    0 < letters.count tested := by
  exact List.count_pos_iff.mpr <|
    (mem_firstOccurrenceSequence_iff tested letters).mp member

private def blockSizeExponent : BlockSize → Nat
  | .one => 1
  | .two => 2
  | .three => 3

private theorem count_renderBlock_self
    (size : BlockSize) (x : Nat) :
    (renderBlock size x).count x = blockSizeExponent size := by
  cases size <;> simp [renderBlock, blockSizeExponent]

private theorem count_renderBlock_of_ne
    (size : BlockSize) {x tested : Nat}
    (notEqual : tested ≠ x) :
    (renderBlock size x).count tested = 0 := by
  cases size <;> simp [renderBlock, notEqual, Ne.symm notEqual]

private theorem renderBlock_normal
    (size : BlockSize) (x : Nat) :
    SemigroupBasis.CoRoots.S5_530.S5_530Normal
      (renderBlock size x) := by
  cases size
  · simpa [renderBlock] using
      SemigroupBasis.CoRoots.S5_530.S5_530Normal.single
        x []
        SemigroupBasis.CoRoots.S5_530.S5_530Normal.nil (by simp)
  · simpa [renderBlock] using
      SemigroupBasis.CoRoots.S5_530.S5_530Normal.double
        x []
        SemigroupBasis.CoRoots.S5_530.S5_530Normal.nil (by simp)
  · simpa [renderBlock] using
      SemigroupBasis.CoRoots.S5_530.S5_530Normal.triple
        x []
        SemigroupBasis.CoRoots.S5_530.S5_530Normal.nil (by simp)

private theorem renderTwoBlocks_normal
    (firstSize secondSize : BlockSize) {x y : Nat}
    (notEqual : x ≠ y) :
    SemigroupBasis.CoRoots.S5_530.S5_530Normal
      (renderBlock firstSize x ++ renderBlock secondSize y) := by
  have tailNormal := renderBlock_normal secondSize y
  have xNotMem : x ∉ renderBlock secondSize y := by
    cases secondSize <;> simp [renderBlock, notEqual]
  cases firstSize
  · simpa [renderBlock] using
      SemigroupBasis.CoRoots.S5_530.S5_530Normal.single
        x _ tailNormal xNotMem
  · simpa [renderBlock] using
      SemigroupBasis.CoRoots.S5_530.S5_530Normal.double
        x _ tailNormal xNotMem
  · simpa [renderBlock] using
      SemigroupBasis.CoRoots.S5_530.S5_530Normal.triple
        x _ tailNormal xNotMem

private theorem normal_eq_renderTwoBlocks
    {letters : List Nat}
    (normal :
      SemigroupBasis.CoRoots.S5_530.S5_530Normal letters)
    (firstSize secondSize : BlockSize) {x y : Nat}
    (order : firstOccurrenceSequence letters = [x, y])
    (xCount : letters.count x = blockSizeExponent firstSize)
    (yCount : letters.count y = blockSizeExponent secondSize) :
    letters = renderBlock firstSize x ++ renderBlock secondSize y := by
  have nodup := firstOccurrenceSequence_nodup letters
  rw [order] at nodup
  have notEqual : x ≠ y := by simpa using nodup
  apply
    SemigroupBasis.CoRoots.S5_530.s5_530Normal_eq_of_invariants
      normal (renderTwoBlocks_normal firstSize secondSize notEqual)
  · rw [order]
    rw [firstOccurrences_renderBlock firstSize]
    · have secondOrder :
          firstOccurrenceSequence (renderBlock secondSize y) = [y] := by
        simpa [firstOccurrenceSequence] using
          (firstOccurrences_renderBlock secondSize
            (x := y) (xs := []) (by simp))
      rw [secondOrder]
    · cases secondSize <;> simp [renderBlock, notEqual]
  · intro tested
    by_cases testedX : tested = x
    · subst tested
      rw [xCount, List.count_append, count_renderBlock_self]
      rw [count_renderBlock_of_ne secondSize notEqual]
      omega
    · by_cases testedY : tested = y
      · subst tested
        rw [yCount, List.count_append]
        rw [count_renderBlock_of_ne firstSize (Ne.symm notEqual)]
        rw [count_renderBlock_self]
        omega
      · have absent : tested ∉ letters := by
          intro member
          have inOrder : tested ∈ [x, y] := by
            rw [← order]
            exact (mem_firstOccurrenceSequence_iff tested letters).mpr member
          simp [testedX, testedY] at inOrder
        rw [List.count_eq_zero.mpr absent, List.count_append]
        rw [count_renderBlock_of_ne firstSize testedX,
          count_renderBlock_of_ne secondSize testedY]

private theorem listDerivesTwoBlockNormal
    {letters : List Nat}
    (normal :
      SemigroupBasis.CoRoots.S5_530.S5_530Normal letters)
    {x y : Nat}
    (order : firstOccurrenceSequence letters = [x, y])
    (notLiteral : letters ≠ [x, y]) :
    ListDerives basis letters [x, x, y] := by
  have xPositive : 0 < letters.count x :=
    normal_count_pos_of_mem_firstOccurrences normal <| by
      rw [order]
      simp
  have yPositive : 0 < letters.count y :=
    normal_count_pos_of_mem_firstOccurrences normal <| by
      rw [order]
      simp
  have xBound := normal_count_le_three normal x
  have yBound := normal_count_le_three normal y
  have xCases :
      letters.count x = 1 ∨ letters.count x = 2 ∨
        letters.count x = 3 := by omega
  have yCases :
      letters.count y = 1 ∨ letters.count y = 2 ∨
        letters.count y = 3 := by omega
  rcases xCases with xOne | xTwo | xThree <;>
    rcases yCases with yOne | yTwo | yThree
  · have equal := normal_eq_renderTwoBlocks normal .one .one order xOne yOne
    exact False.elim <| notLiteral (by simpa [renderBlock] using equal)
  · have equal := normal_eq_renderTwoBlocks normal .one .two order xOne yTwo
    rw [equal]
    exact listDerivesTwoBlock .one .two x y
      (Or.inr (by intro h; cases h))
  · have equal := normal_eq_renderTwoBlocks normal .one .three order xOne yThree
    rw [equal]
    exact listDerivesTwoBlock .one .three x y
      (Or.inr (by intro h; cases h))
  · have equal := normal_eq_renderTwoBlocks normal .two .one order xTwo yOne
    rw [equal]
    exact listDerivesTwoBlock .two .one x y
      (Or.inl (by intro h; cases h))
  · have equal := normal_eq_renderTwoBlocks normal .two .two order xTwo yTwo
    rw [equal]
    exact listDerivesTwoBlock .two .two x y
      (Or.inl (by intro h; cases h))
  · have equal := normal_eq_renderTwoBlocks normal .two .three order xTwo yThree
    rw [equal]
    exact listDerivesTwoBlock .two .three x y
      (Or.inl (by intro h; cases h))
  · have equal := normal_eq_renderTwoBlocks normal .three .one order xThree yOne
    rw [equal]
    exact listDerivesTwoBlock .three .one x y
      (Or.inl (by intro h; cases h))
  · have equal := normal_eq_renderTwoBlocks normal .three .two order xThree yTwo
    rw [equal]
    exact listDerivesTwoBlock .three .two x y
      (Or.inl (by intro h; cases h))
  · have equal := normal_eq_renderTwoBlocks normal .three .three order xThree yThree
    rw [equal]
    exact listDerivesTwoBlock .three .three x y
      (Or.inl (by intro h; cases h))

private theorem listDerivesLeadingBlock
    (size : BlockSize) (x : Nat)
    {middle suffix : List Nat}
    (middleNonempty : middle ≠ [])
    (suffixNonempty : suffix ≠ []) :
    ListDerives basis
      (renderBlock size x ++ middle ++ suffix)
      (x :: middle ++ suffix) := by
  cases middle with
  | nil => exact False.elim (middleNonempty rfl)
  | cons middleHead middleTail =>
      cases suffix with
      | nil => exact False.elim (suffixNonempty rfl)
      | cons suffixHead suffixTail =>
          let middleWord := listWord middleHead middleTail
          let suffixWord := listWord suffixHead suffixTail
          cases size with
          | one => exact ListDerives.refl _
          | two =>
              exact ListDerives.ofWord <| by
                simpa [renderBlock, listWord, middleWord, suffixWord,
                  Word.singleton, Word.append, Word.append_assoc,
                  List.append_assoc] using
                    derivesLongContraction
                      (Word.singleton x) middleWord suffixWord
          | three =>
              have first :=
                derivesPrefixCap (Word.singleton x)
                  (middleWord ++ suffixWord)
              have second :=
                derivesLongContraction
                  (Word.singleton x) middleWord suffixWord
              exact ListDerives.ofWord <| first.trans <| by
                simpa [renderBlock, listWord, middleWord, suffixWord,
                  Word.singleton, Word.append, Word.append_assoc,
                  List.append_assoc] using second

private theorem listDerivesInteriorBlock
    (size : BlockSize) (pre : List Nat) (x : Nat)
    {suffix : List Nat}
    (prefixNonempty : pre ≠ [])
    (suffixNonempty : suffix ≠ []) :
    ListDerives basis
      (pre ++ renderBlock size x ++ suffix)
      (pre ++ x :: suffix) := by
  cases pre with
  | nil => exact False.elim (prefixNonempty rfl)
  | cons prefixHead prefixTail =>
      cases suffix with
      | nil => exact False.elim (suffixNonempty rfl)
      | cons suffixHead suffixTail =>
          let prefixWord := listWord prefixHead prefixTail
          let suffixWord := listWord suffixHead suffixTail
          cases size with
          | one =>
              simpa [renderBlock, List.append_assoc] using
                (ListDerives.refl (basis := basis)
                  (prefixHead :: prefixTail ++ x :: suffixHead :: suffixTail))
          | two =>
              have core := ListDerives.ofWord <|
                derivesInteriorContraction
                  prefixWord (Word.singleton x) suffixWord
              simpa [renderBlock, listWord, prefixWord, suffixWord,
                Word.singleton, Word.toList, Word.toList_append,
                List.append_assoc] using core
          | three =>
              have first :=
                Derives.prepend prefixWord <|
                  derivesPrefixCap (Word.singleton x) suffixWord
              have second :=
                derivesInteriorContraction
                  prefixWord (Word.singleton x) suffixWord
              have aligned := first.trans <| by
                simpa [Word.append_assoc] using second
              have core := ListDerives.ofWord aligned
              simpa [renderBlock, listWord, prefixWord, suffixWord,
                Word.singleton, Word.toList, Word.toList_append,
                List.append_assoc] using core

private theorem listDerivesFinalBlock
    (size : BlockSize) (pre : List Nat) (first second x : Nat) :
    ListDerives basis
      (pre ++ [first, second] ++ renderBlock size x)
      (pre ++ [first, second, x]) := by
  cases size with
  | one =>
      simpa [renderBlock, List.append_assoc] using
        (ListDerives.refl (basis := basis)
          (pre ++ [first, second, x]))
  | two =>
      have core :=
        ListDerives.ofWord <|
          derivesFinalContraction
            (Word.singleton first) (Word.singleton second)
              (Word.singleton x)
      simpa [renderBlock, listWord, Word.singleton, Word.append,
        Word.append_assoc, List.append_assoc] using core.prepend pre
  | three =>
      have firstStep :=
        ListDerives.ofWord <|
          derivesFinalContraction
            (listWord first [second]) (Word.singleton x)
              (Word.singleton x)
      have secondStep :=
        ListDerives.ofWord <|
          derivesFinalContraction
            (Word.singleton first) (Word.singleton second)
              (Word.singleton x)
      exact by
        simpa [renderBlock, listWord, Word.singleton, Word.append,
          Word.append_assoc, List.append_assoc] using
            (firstStep.prepend pre).trans (secondStep.prepend pre)

private theorem listDerivesCurrentBlockAfterTwo
    (size : BlockSize) (pre : List Nat) (first second x : Nat)
    (suffix : List Nat) :
    ListDerives basis
      (pre ++ [first, second] ++ renderBlock size x ++ suffix)
      (pre ++ [first, second, x] ++ suffix) := by
  cases suffix with
  | nil =>
      simpa [List.append_assoc] using
        listDerivesFinalBlock size pre first second x
  | cons suffixHead suffixTail =>
      have collapsed :=
        listDerivesInteriorBlock size
          (pre ++ [first, second]) x
          (suffix := suffixHead :: suffixTail)
          (prefixNonempty := by simp)
          (suffixNonempty := by simp)
      simpa [List.append_assoc] using collapsed

private theorem listDerivesCollapseAfterTwo :
    ∀ {letters : List Nat},
      SemigroupBasis.CoRoots.S5_530.S5_530Normal letters →
      ∀ (pre : List Nat) (first second : Nat),
        ListDerives basis
          (pre ++ [first, second] ++ letters)
          (pre ++ [first, second] ++
            firstOccurrenceSequence letters)
  | _, .nil, pre, first, second => by
      exact ListDerives.refl _
  | _, .single x xs normal xNotMem, pre, first, second => by
      have remaining :=
        listDerivesCollapseAfterTwo normal
          (pre ++ [first]) second x
      rw [firstOccurrences_single xNotMem]
      simpa [List.append_assoc] using remaining
  | _, .double x xs normal xNotMem, pre, first, second => by
      have collapsed :=
        listDerivesCurrentBlockAfterTwo .two pre first second x xs
      have remaining :=
        listDerivesCollapseAfterTwo normal
          (pre ++ [first]) second x
      rw [firstOccurrences_double xNotMem]
      have combined := collapsed.trans <| by
        simpa [renderBlock, List.append_assoc] using remaining
      simpa [renderBlock, List.append_assoc] using combined
  | _, .triple x xs normal xNotMem, pre, first, second => by
      have collapsed :=
        listDerivesCurrentBlockAfterTwo .three pre first second x xs
      have remaining :=
        listDerivesCollapseAfterTwo normal
          (pre ++ [first]) second x
      rw [firstOccurrences_triple xNotMem]
      have combined := collapsed.trans <| by
        simpa [renderBlock, List.append_assoc] using remaining
      simpa [renderBlock, List.append_assoc] using combined

private theorem listDerivesThreeBlockTail
    (firstSize secondSize : BlockSize) (x y : Nat)
    {rest : List Nat}
    (restNormal :
      SemigroupBasis.CoRoots.S5_530.S5_530Normal rest)
    (restNonempty : rest ≠ [])
    (xNotMem : x ∉ renderBlock secondSize y ++ rest)
    (yNotMem : y ∉ rest) :
    ListDerives basis
      (renderBlock firstSize x ++ renderBlock secondSize y ++ rest)
      (firstOccurrenceSequence
        (renderBlock firstSize x ++ renderBlock secondSize y ++ rest)) := by
  have first :=
    listDerivesLeadingBlock firstSize x
      (middle := renderBlock secondSize y) (suffix := rest)
      (middleNonempty := renderBlock_ne_nil secondSize y)
      (suffixNonempty := restNonempty)
  have second :=
    listDerivesInteriorBlock secondSize [x] y (suffix := rest)
      (prefixNonempty := by simp)
      (suffixNonempty := restNonempty)
  have remaining := listDerivesCollapseAfterTwo restNormal [] x y
  have orderEq :
      firstOccurrenceSequence
          (renderBlock firstSize x ++ renderBlock secondSize y ++ rest) =
        x :: y :: firstOccurrenceSequence rest := by
    rw [List.append_assoc]
    rw [firstOccurrences_renderBlock firstSize xNotMem]
    rw [firstOccurrences_renderBlock secondSize yNotMem]
  rw [orderEq]
  exact first.trans <| second.trans <| by
    simpa [List.append_assoc] using remaining

private theorem listDerivesTwoBlockHead
    (firstSize secondSize : BlockSize) (x y : Nat)
    {rest : List Nat}
    (restNormal :
      SemigroupBasis.CoRoots.S5_530.S5_530Normal rest)
    (xNotMem : x ∉ renderBlock secondSize y ++ rest)
    (yNotMem : y ∉ rest)
    (atLeastThree :
      3 ≤
        (firstOccurrenceSequence
          (renderBlock firstSize x ++ renderBlock secondSize y ++ rest)).length) :
    ListDerives basis
      (renderBlock firstSize x ++ renderBlock secondSize y ++ rest)
      (firstOccurrenceSequence
        (renderBlock firstSize x ++ renderBlock secondSize y ++ rest)) := by
  have restNonempty : rest ≠ [] := by
    intro empty
    subst rest
    simp only [List.append_nil] at xNotMem atLeastThree
    rw [firstOccurrences_renderBlock firstSize xNotMem] at atLeastThree
    have secondOrder :
        firstOccurrenceSequence (renderBlock secondSize y) = [y] := by
      simpa [firstOccurrenceSequence] using
        (firstOccurrences_renderBlock secondSize
          (x := y) (xs := []) (by simp))
    rw [secondOrder] at atLeastThree
    simp at atLeastThree
  exact listDerivesThreeBlockTail firstSize secondSize x y
    restNormal restNonempty xNotMem yNotMem

private theorem listDerivesNormalHead
    (firstSize : BlockSize) (x : Nat) {tail : List Nat}
    (tailNormal :
      SemigroupBasis.CoRoots.S5_530.S5_530Normal tail)
    (xNotMem : x ∉ tail)
    (atLeastThree :
      3 ≤
        (firstOccurrenceSequence
          (renderBlock firstSize x ++ tail)).length) :
    ListDerives basis
      (renderBlock firstSize x ++ tail)
      (firstOccurrenceSequence (renderBlock firstSize x ++ tail)) := by
  cases tailNormal with
  | nil =>
      rw [firstOccurrences_renderBlock firstSize] at atLeastThree
      · simp [firstOccurrenceSequence] at atLeastThree
      · simp
  | single y ys restNormal yNotMem =>
      simpa [renderBlock] using
        listDerivesTwoBlockHead firstSize .one x y
          restNormal (by simpa [renderBlock] using xNotMem) yNotMem <| by
            simpa [renderBlock] using atLeastThree
  | double y ys restNormal yNotMem =>
      simpa [renderBlock] using
        listDerivesTwoBlockHead firstSize .two x y
          restNormal (by simpa [renderBlock] using xNotMem) yNotMem <| by
            simpa [renderBlock] using atLeastThree
  | triple y ys restNormal yNotMem =>
      simpa [renderBlock] using
        listDerivesTwoBlockHead firstSize .three x y
          restNormal (by simpa [renderBlock] using xNotMem) yNotMem <| by
            simpa [renderBlock] using atLeastThree

/-- A gathered block normal form with at least three first-occurrence blocks
contracts to its duplicate-free first-occurrence sequence. -/
theorem listDerivesLongSupportNormal
    {letters : List Nat}
    (normal :
      SemigroupBasis.CoRoots.S5_530.S5_530Normal letters)
    (atLeastThree :
      3 ≤ (firstOccurrenceSequence letters).length) :
    ListDerives basis letters (firstOccurrenceSequence letters) := by
  cases normal with
  | nil => simp [firstOccurrenceSequence] at atLeastThree
  | single x xs tailNormal xNotMem =>
      simpa [renderBlock] using
        listDerivesNormalHead .one x tailNormal xNotMem <| by
          simpa [renderBlock] using atLeastThree
  | double x xs tailNormal xNotMem =>
      simpa [renderBlock] using
        listDerivesNormalHead .two x tailNormal xNotMem <| by
          simpa [renderBlock] using atLeastThree
  | triple x xs tailNormal xNotMem =>
      simpa [renderBlock] using
        listDerivesNormalHead .three x tailNormal xNotMem <| by
          simpa [renderBlock] using atLeastThree

private theorem normal_eq_triple
    {letters : List Nat}
    (normal :
      SemigroupBasis.CoRoots.S5_530.S5_530Normal letters)
    (x : Nat)
    (order : firstOccurrenceSequence letters = [x])
    (count : letters.count x = 3) :
    letters = [x, x, x] := by
  apply
    SemigroupBasis.CoRoots.S5_530.s5_530Normal_eq_of_invariants
      normal
      (SemigroupBasis.CoRoots.S5_530.S5_530Normal.triple
        x [] SemigroupBasis.CoRoots.S5_530.S5_530Normal.nil (by simp))
  · simpa [firstOccurrenceSequence] using order
  · intro tested
    by_cases equal : tested = x
    · subst tested
      simpa using count
    · have absent : tested ∉ letters := by
        intro member
        have inOrder : tested ∈ [x] := by
          rw [← order]
          exact
            (mem_firstOccurrenceSequence_iff tested letters).mpr member
        simpa [equal] using inOrder
      rw [List.count_eq_zero.mpr absent]
      simp [Ne.symm equal]

private theorem count_eq_length_of_all_eq
    (x : Nat) :
    ∀ (letters : List Nat),
      (∀ y, y ∈ letters → y = x) →
      letters.count x = letters.length
  | [], _ => rfl
  | y :: ys, allEqual => by
      have headEqual := allEqual y (List.Mem.head ys)
      subst y
      have tailEqual : ∀ z, z ∈ ys → z = x := by
        intro z member
        exact allEqual z (List.Mem.tail x member)
      rw [List.count_cons_self, List.length_cons,
        count_eq_length_of_all_eq x ys tailEqual]

private theorem count_pair_eq_length
    (x y : Nat) (notEqual : x ≠ y) :
    ∀ (letters : List Nat),
      (∀ z, z ∈ letters → z = x ∨ z = y) →
      letters.count x + letters.count y = letters.length
  | [], _ => by simp
  | z :: zs, allIn => by
      have head := allIn z (List.Mem.head zs)
      have tail : ∀ q, q ∈ zs → q = x ∨ q = y := by
        intro q member
        exact allIn q (List.Mem.tail z member)
      have induction := count_pair_eq_length x y notEqual zs tail
      rcases head with rfl | rfl
      · simp only [List.count_cons_self,
          List.count_cons_of_ne notEqual, List.length_cons]
        omega
      · simp only [List.count_cons_self,
          List.count_cons_of_ne (Ne.symm notEqual), List.length_cons]
        omega

private theorem s5_530NormalList_not_literal_pair
    (word : Word Nat) {x y : Nat}
    (long : 3 ≤ word.toList.length)
    (order : firstOccurrenceSequence word.toList = [x, y]) :
    SemigroupBasis.CoRoots.S5_530.s5_530NormalList word.toList ≠
      [x, y] := by
  intro equal
  have nodup := firstOccurrenceSequence_nodup word.toList
  rw [order] at nodup
  have notEqual : x ≠ y := by simpa using nodup
  have xCount :=
    SemigroupBasis.CoRoots.S5_530.s5_530NormalList_count x word.toList
  have yCount :=
    SemigroupBasis.CoRoots.S5_530.s5_530NormalList_count y word.toList
  rw [equal] at xCount yCount
  have xSourceCount : word.toList.count x = 1 := by
    simp [notEqual, Ne.symm notEqual,
      SemigroupBasis.CoRoots.S5_530.s5_530Exponent] at xCount
    omega
  have ySourceCount : word.toList.count y = 1 := by
    simp [notEqual, Ne.symm notEqual,
      SemigroupBasis.CoRoots.S5_530.s5_530Exponent] at yCount
    omega
  have allIn :
      ∀ z, z ∈ word.toList → z = x ∨ z = y := by
    intro z member
    have inOrder : z ∈ [x, y] := by
      rw [← order]
      exact (mem_firstOccurrenceSequence_iff z word.toList).mpr member
    simpa using inOrder
  have lengthEq := count_pair_eq_length x y notEqual word.toList allIn
  rw [xSourceCount, ySourceCount] at lengthEq
  omega

/-- Every word derives to the published long first-occurrence normal form. -/
theorem derivesLongFirstOccurrenceNormal (word : Word Nat) :
    match longFirstOccurrenceNormalList word.toList with
    | [] => False
    | x :: xs => Derives basis word (listWord x xs) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          exact Derives.refl _
      | cons second rest =>
          cases rest with
          | nil =>
              exact Derives.refl _
          | cons third more =>
              let source : Word Nat :=
                listWord head (second :: third :: more)
              have sourceLong : 3 ≤ source.toList.length := by
                simp [source, listWord, Word.toList]
              have gathered := derivesGatheredBlockNormal source
              have sourceGathered :=
                SemigroupBasis.CoRoots.S5_530.s5_530DerivesNormal source
              cases normalEq :
                  SemigroupBasis.CoRoots.S5_530.s5_530NormalList
                    source.toList with
              | nil =>
                  exact False.elim <|
                    SemigroupBasis.CoRoots.S5_530.s5_530NormalList_cons_ne_nil
                      source.head source.tail <| by
                        simpa [Word.toList] using normalEq
              | cons normalHead normalTail =>
                  rw [normalEq] at gathered sourceGathered
                  have normalShape :=
                    SemigroupBasis.CoRoots.S5_530.s5_530NormalList_normal
                      source.toList
                  rw [normalEq] at normalShape
                  have orderEq :
                      firstOccurrenceSequence source.toList =
                        firstOccurrenceSequence
                          (normalHead :: normalTail) := by
                    simpa [SemigroupBasis.CoRoots.S5_530.s5_530WordOfCons,
                      Word.toList] using
                        SemigroupBasis.CoRoots.S5_530.s5_530Derives_firstOccurrenceSequence_eq
                          sourceGathered
                  cases orderSource :
                      firstOccurrenceSequence source.toList with
                  | nil =>
                      have impossible :
                          firstOccurrenceSequence source.toList ≠ [] := by
                        cases source
                        simp [Word.toList, firstOccurrenceSequence]
                      exact False.elim (impossible orderSource)
                  | cons first orderTail =>
                      cases orderTail with
                      | nil =>
                          have orderSourceList :
                              firstOccurrenceSequence
                                  (head :: second :: third :: more) =
                                [first] := by
                            simpa [source, listWord, Word.toList] using
                              orderSource
                          have normalOrder :
                              firstOccurrenceSequence
                                  (normalHead :: normalTail) = [first] := by
                            rw [← orderEq, orderSource]
                          have allSource :
                              ∀ z, z ∈ source.toList → z = first := by
                            intro z member
                            have inOrder : z ∈ [first] := by
                              rw [← orderSource]
                              exact
                                (mem_firstOccurrenceSequence_iff
                                  z source.toList).mpr member
                            simpa using inOrder
                          have sourceCount :
                              source.toList.count first =
                                source.toList.length :=
                            count_eq_length_of_all_eq
                              first source.toList allSource
                          have normalCount :=
                            SemigroupBasis.CoRoots.S5_530.s5_530NormalList_count
                              first source.toList
                          rw [normalEq, sourceCount] at normalCount
                          have normalCountThree :
                              (normalHead :: normalTail).count first = 3 := by
                            simpa [SemigroupBasis.CoRoots.S5_530.s5_530Exponent,
                              Nat.min_eq_right sourceLong] using
                                normalCount
                          have exactNormal :=
                            normal_eq_triple normalShape first normalOrder
                              normalCountThree
                          have collapsed :
                              Derives basis
                                (listWord normalHead normalTail)
                                (listWord first [first, first]) := by
                            rw [show listWord normalHead normalTail =
                                listWord first [first, first] by
                              apply Word.toList_injective
                              simpa [listWord, Word.toList] using exactNormal]
                            exact Derives.refl _
                          have combined := gathered.trans <| by
                            simpa [source, listWord,
                              SemigroupBasis.CoRoots.S5_530.s5_530WordOfCons]
                              using collapsed
                          simpa [source, listWord, Word.toList,
                            longFirstOccurrenceNormalList, orderSourceList] using
                              combined
                      | cons secondOrder remainingOrder =>
                          cases remainingOrder with
                          | nil =>
                              have orderSourceList :
                                  firstOccurrenceSequence
                                      (head :: second :: third :: more) =
                                    [first, secondOrder] := by
                                simpa [source, listWord, Word.toList] using
                                  orderSource
                              have normalOrder :
                                  firstOccurrenceSequence
                                      (normalHead :: normalTail) =
                                    [first, secondOrder] := by
                                rw [← orderEq, orderSource]
                              have notLiteral :
                                  normalHead :: normalTail ≠
                                    [first, secondOrder] := by
                                intro literal
                                apply
                                  s5_530NormalList_not_literal_pair
                                    source sourceLong orderSource
                                simpa [normalEq] using literal
                              have collapsedList :=
                                listDerivesTwoBlockNormal normalShape
                                  normalOrder notLiteral
                              have collapsed :=
                                ListDerives.toWord collapsedList
                              have combined := gathered.trans <| by
                                simpa [source, listWord,
                                  SemigroupBasis.CoRoots.S5_530.s5_530WordOfCons]
                                  using collapsed
                              simpa [source, listWord, Word.toList,
                                longFirstOccurrenceNormalList,
                                orderSourceList] using
                                  combined
                          | cons thirdOrder furtherOrder =>
                              have orderSourceList :
                                  firstOccurrenceSequence
                                      (head :: second :: third :: more) =
                                    first :: secondOrder ::
                                      thirdOrder :: furtherOrder := by
                                simpa [source, listWord, Word.toList] using
                                  orderSource
                              have normalOrder :
                                  firstOccurrenceSequence
                                      (normalHead :: normalTail) =
                                    first :: secondOrder ::
                                      thirdOrder :: furtherOrder := by
                                rw [← orderEq, orderSource]
                              have atLeastThree :
                                  3 ≤
                                    (firstOccurrenceSequence
                                      (normalHead :: normalTail)).length := by
                                rw [normalOrder]
                                simp
                              have collapsedList :=
                                listDerivesLongSupportNormal
                                  normalShape atLeastThree
                              rw [normalOrder] at collapsedList
                              have collapsed :=
                                ListDerives.toWord collapsedList
                              have combined := gathered.trans <| by
                                simpa [source, listWord,
                                  SemigroupBasis.CoRoots.S5_530.s5_530WordOfCons]
                                  using collapsed
                              simpa [source, listWord, Word.toList,
                                longFirstOccurrenceNormalList,
                                orderSourceList] using combined

/-- Constructive closure of the unrestricted derivational obligation. -/
theorem longFirstOccurrenceDerivationalCompleteness :
    LongFirstOccurrenceDerivationalCompleteness := by
  intro left right same
  have leftNormal := derivesLongFirstOccurrenceNormal left
  have rightNormal := derivesLongFirstOccurrenceNormal right
  cases leftEq : longFirstOccurrenceNormalList left.toList with
  | nil =>
      exact False.elim <|
        longFirstOccurrenceNormalList_cons_ne_nil left.head left.tail <| by
          simpa [Word.toList] using leftEq
  | cons leftHead leftTail =>
      cases rightEq : longFirstOccurrenceNormalList right.toList with
      | nil =>
          exact False.elim <|
            longFirstOccurrenceNormalList_cons_ne_nil right.head right.tail <| by
              simpa [Word.toList] using rightEq
      | cons rightHead rightTail =>
          rw [leftEq] at leftNormal
          rw [rightEq] at rightNormal
          have normalLists :
              leftHead :: leftTail = rightHead :: rightTail := by
            simpa [SameLongFirstOccurrenceSignature,
              longFirstOccurrenceSignature, leftEq, rightEq] using same
          cases normalLists
          exact leftNormal.trans rightNormal.symm
end SemigroupBasis.CoRoots.S5_523

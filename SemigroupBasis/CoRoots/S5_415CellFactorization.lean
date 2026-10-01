import SemigroupBasis.CoRoots.S5_415RepeatedExpansion
import SemigroupBasis.CoRoots.S5_415Regularity

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-- Proof-relevant data for one of Volkov's cells `y p y`.  The interior is
allowed to be empty. -/
structure CellFactor where
  boundary : Nat
  interior : List Nat

namespace CellFactor

/-- The nonempty word displayed by a cell factor. -/
def word (factor : CellFactor) : Word Nat :=
  ⟨factor.boundary, factor.interior ++ [factor.boundary]⟩

@[simp]
theorem word_toList (factor : CellFactor) :
    factor.word.toList =
      factor.boundary :: (factor.interior ++ [factor.boundary]) :=
  rfl

/-- Every cell factor carries the explicit inverse supplied by the regularity
module.  Empty interiors use the square witness; nonempty interiors use the
`A B A` witness. -/
def inverseWitness (factor : CellFactor) :
    InverseWitness factor.word := by
  rcases factor with ⟨boundary, interior⟩
  cases interior with
  | nil =>
      change InverseWitness
        (emptyGapSquare (Word.singleton boundary))
      exact emptyGapSquareInverseWitness (Word.singleton boundary)
  | cons interiorHead interiorTail =>
      change InverseWitness
        (cell (Word.singleton boundary)
          (⟨interiorHead, interiorTail⟩ : Word Nat))
      exact cellInverseWitness (Word.singleton boundary)
        (⟨interiorHead, interiorTail⟩ : Word Nat)

end CellFactor

/-- A proof-relevant, finite, nonempty product of cells.  `snoc` matches the
left-to-right greedy construction while retaining every factor. -/
inductive CellProduct : Type
  | single (factor : CellFactor)
  | snoc (priorProduct : CellProduct) (factor : CellFactor)

namespace CellProduct

/-- The word represented by a nonempty product of cells. -/
def word : CellProduct → Word Nat
  | single factor => factor.word
  | snoc priorProduct factor => priorProduct.word ++ factor.word

/-- The cells retained by a product, in their multiplication order. -/
def factors : CellProduct → List CellFactor
  | single factor => [factor]
  | snoc priorProduct factor => priorProduct.factors ++ [factor]

/-- Boundary letters in the order in which the greedy construction processes
them. -/
def boundaries : CellProduct → List Nat
  | single factor => [factor.boundary]
  | snoc priorProduct factor => priorProduct.boundaries ++ [factor.boundary]

/-- The unprocessed remainder contains none of the boundary letters already
used by the cell product.  This is Volkov's decreasing-support invariant. -/
def RemainderOmitsBoundaries
    (product : CellProduct) (remainder : List Nat) : Prop :=
  ∀ boundary, boundary ∈ product.boundaries → boundary ∉ remainder

theorem factors_ne_nil (product : CellProduct) :
    product.factors ≠ [] := by
  induction product with
  | single factor => simp [factors]
  | snoc priorProduct factor induction => simp [factors]

/-- Finite products of cells inherit an explicit inverse witness by repeatedly
using `InverseWitness.append`. -/
def inverseWitness : (product : CellProduct) →
    InverseWitness product.word
  | single factor => factor.inverseWitness
  | snoc priorProduct factor =>
      priorProduct.inverseWitness.append factor.inverseWitness

end CellProduct

/-- Proof-relevant output of the greedy factorization: a cell product, the
derivation to it, and its explicit inverse witness. -/
structure WitnessedCellProduct (source : Word Nat) where
  product : CellProduct
  derivation : Derives basis source product.word
  inverseWitness : InverseWitness product.word

/-- An inverse witness can be pulled back along a derivation.  This records at
word level that regularity depends only on the derivation class. -/
def InverseWitness.pullback
    {source target : Word Nat}
    (witness : InverseWitness target)
    (derivation : Derives basis source target) :
    InverseWitness source where
  inverse := witness.inverse
  word_inverse_word := by
    have changeLeft :
        Derives basis
          ((source ++ witness.inverse) ++ source)
          ((target ++ witness.inverse) ++ source) :=
      Derives.appendRight
        (Derives.appendRight derivation witness.inverse) source
    have changeRight :
        Derives basis
          ((target ++ witness.inverse) ++ source)
          ((target ++ witness.inverse) ++ target) :=
      Derives.prepend (target ++ witness.inverse) derivation
    exact changeLeft.trans <| changeRight.trans <|
      witness.word_inverse_word.trans derivation.symm
  inverse_word_inverse := by
    have changeMiddle :
        Derives basis
          ((witness.inverse ++ source) ++ witness.inverse)
          ((witness.inverse ++ target) ++ witness.inverse) :=
      Derives.appendRight
        (Derives.prepend witness.inverse derivation) witness.inverse
    exact changeMiddle.trans witness.inverse_word_inverse

/-- Contextual cell expansion preserves the absence of singleton letters. -/
theorem ContextualCellExpansion.noSingletonLetters
    {word expanded : Word Nat} {tested : Nat}
    {selected : CellContains word tested}
    (step : ContextualCellExpansion selected expanded)
    (sourceNoSingleton : NoSingletonLetters word) :
    NoSingletonLetters expanded := by
  intro letter targetMember targetCount
  have sourceMember : letter ∈ word.toList :=
    (step.sameLetterSupport letter).mpr targetMember
  exact sourceNoSingleton letter sourceMember
    (step.noNewSingleton letter targetCount)

/-- A supported value has a rightmost occurrence.  The returned suffix omits
that value, which is the finite-list form used by the greedy construction. -/
private theorem exists_rightmost_split
    {value : Nat} {letters : List Nat}
    (member : value ∈ letters) :
    ∃ before after,
      letters = before ++ value :: after ∧ value ∉ after := by
  induction letters with
  | nil => simp at member
  | cons head tail induction =>
      by_cases inTail : value ∈ tail
      · obtain ⟨before, after, shape, notAfter⟩ := induction inTail
        exact ⟨head :: before, after, by simp [shape], notAfter⟩
      · have equal : value = head := by
          simpa [inTail] using member
        subst head
        exact ⟨[], tail, by simp, inTail⟩

/-- In a no-singleton word, the initial letter occurs again in its tail. -/
private theorem head_mem_tail_of_noSingletonLetters
    (word : Word Nat) (noSingleton : NoSingletonLetters word) :
    word.head ∈ word.tail := by
  apply Decidable.byContradiction
  intro absent
  have tailCount : word.tail.count word.head = 0 :=
    List.count_eq_zero.mpr absent
  have countOne : word.toList.count word.head = 1 := by
    simp [Word.toList, tailCount]
  exact noSingleton word.head (by simp [Word.toList]) countOne

/-- Greedy continuation from an already-built cell prefix.  If the remainder
head repeats inside the remainder, its rightmost occurrence closes the next
cell directly.  Otherwise the no-singleton hypothesis supplies an earlier
occurrence in the processed prefix; expanding the spanning cell preserves the
prefix and appends a new cell. -/
private theorem exists_derives_cellProduct_of_prefix
    (current : Word Nat) (builtProduct : CellProduct) (remainder : List Nat)
    (shape : current.toList = builtProduct.word.toList ++ remainder)
    (remainderOmits : builtProduct.RemainderOmitsBoundaries remainder)
    (noSingleton : NoSingletonLetters current) :
    ∃ product : CellProduct, Derives basis current product.word := by
  have closeAtLength :
      ∀ bound remainder,
        remainder.length = bound →
          ∀ (current : Word Nat) (builtProduct : CellProduct),
            current.toList = builtProduct.word.toList ++ remainder →
              builtProduct.RemainderOmitsBoundaries remainder →
              NoSingletonLetters current →
                ∃ product : CellProduct,
                  Derives basis current product.word := by
    intro bound
    refine Nat.strongRecOn
      (motive := fun currentBound =>
        ∀ remainder,
          remainder.length = currentBound →
            ∀ (current : Word Nat) (builtProduct : CellProduct),
              current.toList = builtProduct.word.toList ++ remainder →
                builtProduct.RemainderOmitsBoundaries remainder →
                  NoSingletonLetters current →
                    ∃ product : CellProduct,
                      Derives basis current product.word)
      bound ?_
    intro currentBound induction remainder lengthEq current builtProduct shape
      remainderOmits noSingleton
    cases remainder with
    | nil =>
        have currentEq : current = builtProduct.word :=
          Word.toList_injective (by simpa using shape)
        subst current
        exact ⟨builtProduct, Derives.refl builtProduct.word⟩
    | cons tested tail =>
        by_cases repeatedInTail : tested ∈ tail
        · obtain ⟨interior, nextRemainder, tailShape,
              testedNotNext⟩ :=
            exists_rightmost_split repeatedInTail
          let nextFactor : CellFactor := ⟨tested, interior⟩
          let nextPrefix : CellProduct :=
            CellProduct.snoc builtProduct nextFactor
          have nextShape :
              current.toList =
                nextPrefix.word.toList ++ nextRemainder := by
            rw [shape, tailShape]
            simp [nextPrefix, nextFactor, CellProduct.word,
              CellFactor.word, Word.toList, Word.toList_append,
              List.append_assoc]
          have nextRemainderOmits :
              nextPrefix.RemainderOmitsBoundaries
                nextRemainder := by
            intro boundary boundaryMember
            simp [nextPrefix, nextFactor,
              CellProduct.RemainderOmitsBoundaries,
              CellProduct.boundaries] at boundaryMember
            rcases boundaryMember with oldBoundary | equal
            · intro boundaryInNext
              apply remainderOmits boundary oldBoundary
              rw [tailShape]
              exact List.Mem.tail tested <|
                List.mem_append_right interior <|
                  List.Mem.tail tested boundaryInNext
            · subst boundary
              exact testedNotNext
          have remainderSmaller :
              nextRemainder.length < (tested :: tail).length := by
            rw [tailShape]
            simp only [List.length_cons, List.length_append]
            omega
          have smaller : nextRemainder.length < currentBound := by
            calc
              nextRemainder.length < (tested :: tail).length :=
                remainderSmaller
              _ = currentBound := lengthEq
          exact induction nextRemainder.length smaller
            nextRemainder rfl current nextPrefix nextShape
              nextRemainderOmits noSingleton
        · have currentMember : tested ∈ current.toList := by
            rw [shape]
            simp
          have remainderCount :
              (tested :: tail).count tested = 1 := by
            have tailCount : tail.count tested = 0 :=
              List.count_eq_zero.mpr repeatedInTail
            simp [tailCount]
          have countShape :
              current.toList.count tested =
                builtProduct.word.toList.count tested +
                  (tested :: tail).count tested := by
            rw [shape, List.count_append]
          have prefixPositive :
              0 < builtProduct.word.toList.count tested := by
            have notSingleton :=
              noSingleton tested currentMember
            rw [countShape, remainderCount] at notSingleton
            omega
          have prefixMember : tested ∈ builtProduct.word.toList :=
            List.count_pos_iff.mp prefixPositive
          obtain ⟨left, right, prefixShape, _testedNotRight⟩ :=
            exists_rightmost_split prefixMember
          let crossingCell : CellContains current tested :=
            { y := tested
              leadingContext := left
              p := right
              suffix := tail
              factorization := by
                rw [shape, prefixShape]
                simp [List.append_assoc]
              tested_mem := by simp }
          obtain ⟨expanded, step⟩ :=
            crossingCell.exists_contextualCellExpansion
          let nextFactor : CellFactor := ⟨tested, right⟩
          let nextPrefix : CellProduct :=
            CellProduct.snoc builtProduct nextFactor
          have expandedShape :
              expanded.toList = nextPrefix.word.toList ++ tail := by
            rw [step.expanded_toList]
            simp only [crossingCell, nextPrefix, nextFactor,
              CellContains.cellLetters, CellContains.expansionCopy,
              CellProduct.word, Word.toList_append,
              CellFactor.word_toList]
            rw [prefixShape]
            simp [List.append_assoc]
          have nextRemainderOmits :
              nextPrefix.RemainderOmitsBoundaries tail := by
            intro boundary boundaryMember
            simp [nextPrefix, nextFactor,
              CellProduct.RemainderOmitsBoundaries,
              CellProduct.boundaries] at boundaryMember
            rcases boundaryMember with oldBoundary | equal
            · intro boundaryInTail
              exact remainderOmits boundary oldBoundary
                (List.Mem.tail tested boundaryInTail)
            · subst boundary
              exact repeatedInTail
          have smaller : tail.length < currentBound := by
            calc
              tail.length < (tested :: tail).length := by simp
              _ = currentBound := lengthEq
          obtain ⟨product, remainderDerivation⟩ :=
            induction tail.length smaller tail rfl expanded nextPrefix
              expandedShape nextRemainderOmits
              (step.noSingletonLetters noSingleton)
          exact ⟨product, step.derives.trans remainderDerivation⟩
  exact closeAtLength remainder.length remainder rfl current builtProduct shape
    remainderOmits noSingleton

/-- Every nonempty word with no singleton letters derives to a finite,
nonempty product of Volkov cells. -/
theorem noSingletonLetters_derives_cellProduct
    {word : Word Nat} (noSingleton : NoSingletonLetters word) :
    ∃ product : CellProduct, Derives basis word product.word := by
  have repeatedHead :=
    head_mem_tail_of_noSingletonLetters word noSingleton
  obtain ⟨interior, remainder, tailShape, headNotRemainder⟩ :=
    exists_rightmost_split repeatedHead
  let firstFactor : CellFactor := ⟨word.head, interior⟩
  let firstProduct : CellProduct := CellProduct.single firstFactor
  have initialShape :
      word.toList = firstProduct.word.toList ++ remainder := by
    simp [Word.toList, firstProduct, firstFactor, CellProduct.word,
      CellFactor.word, tailShape, List.append_assoc]
  have initialRemainderOmits :
      firstProduct.RemainderOmitsBoundaries remainder := by
    intro boundary boundaryMember
    have equal : boundary = word.head := by
      simpa [firstProduct, firstFactor, CellProduct.boundaries] using
        boundaryMember
    subst boundary
    exact headNotRemainder
  exact exists_derives_cellProduct_of_prefix
    word firstProduct remainder initialShape initialRemainderOmits noSingleton

/-- The product produced by the greedy construction comes with an explicit
inverse witness. -/
noncomputable def noSingletonLetters_derives_witnessedCellProduct
    {word : Word Nat} (noSingleton : NoSingletonLetters word) :
    WitnessedCellProduct word := by
  let existence := noSingletonLetters_derives_cellProduct noSingleton
  let product := Classical.choose existence
  exact
    { product := product
      derivation := Classical.choose_spec existence
      inverseWitness := product.inverseWitness }

/-- A no-singleton word itself has an inverse witness, obtained by pulling the
product witness back along the greedy derivation. -/
noncomputable def noSingletonLetters_inverseWitness
    {word : Word Nat} (noSingleton : NoSingletonLetters word) :
    InverseWitness word :=
  let witnessed :=
    noSingletonLetters_derives_witnessedCellProduct noSingleton
  witnessed.inverseWitness.pullback witnessed.derivation

/-- Volkov's two finite steps compose: a repeated word first loses all
singleton letters and then derives to a witnessed nonempty product of cells. -/
noncomputable def repeatedWord_derives_witnessedCellProduct
    {word : Word Nat} (repeated : RepeatedWord word) :
    WitnessedCellProduct word := by
  let existence := repeatedWord_derives_noSingletonLetters repeated
  let withoutSingletons := Classical.choose existence
  have properties :
      Derives basis word withoutSingletons ∧
        SameLetterSupport word withoutSingletons ∧
          NoSingletonLetters withoutSingletons :=
    Classical.choose_spec existence
  let witnessed :=
    noSingletonLetters_derives_witnessedCellProduct properties.2.2
  exact
    { product := witnessed.product
      derivation := properties.1.trans witnessed.derivation
      inverseWitness := witnessed.inverseWitness }

/-- Every repeated word has a proof-relevant inverse modulo the `S5_415`
basis. -/
noncomputable def repeatedWord_inverseWitness
    {word : Word Nat} (repeated : RepeatedWord word) :
    InverseWitness word :=
  let witnessed := repeatedWord_derives_witnessedCellProduct repeated
  witnessed.inverseWitness.pullback witnessed.derivation

end SemigroupBasis.CoRoots.S5_415

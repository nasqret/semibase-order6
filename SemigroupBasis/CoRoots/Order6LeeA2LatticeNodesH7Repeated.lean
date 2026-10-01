import SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7

/-!
# Repeated-word reduction for the Lee A2 H7 system

This module does not assert the outstanding repeated-word theorem.  It
separates that theorem into two independently checkable obligations and
discharges the first:

* a constructive exposure of every repeated word as a finite product of
  Volkov cells, with the exposure carried out in the H7 basis; and
* equality in the two original-orientation right Schutzenberger projections
  selected by the repeated words.

The remaining premise is canonical equality in the original-orientation
right Schutzenberger projections.  In particular, products of H7-regular
words are regular because the only idempotent exchange in the usual inverse
calculation occurs behind a permanent nonempty guard.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7Repeated

open SemigroupBasis

namespace H7

export SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7
  (LeftGuardedIdempotentsCommute RootedRepeatedCompleteness
    SameRootedBrandtSignature basis
    derivesGuardedCommuteIdempotents derivesPowerContraction
    derivesPowerExpansion derivesSandwichContraction
    derivesSandwichExpansion
    termSemigroup_leftGuardedIdempotentsCommute)

end H7

namespace Brandt

export SemigroupBasis.CoRoots.S5_415
  (CellContains CellFactor CellProduct ContextualCellExpansion
    NoSingletonLetters RepeatedWord SameLetterSupport
    mem_singletonLetters_iff singletonLetters singletonMeasure)

end Brandt

namespace Brandt.CellContains

export SemigroupBasis.CoRoots.S5_415.CellContains
  (cellLetters expansionCopy)

end Brandt.CellContains

namespace Brandt.CellFactor

export SemigroupBasis.CoRoots.S5_415.CellFactor
  (word word_toList)

end Brandt.CellFactor

namespace Brandt.CellProduct

export SemigroupBasis.CoRoots.S5_415.CellProduct
  (RemainderOmitsBoundaries boundaries single snoc word)

end Brandt.CellProduct

namespace Brandt.ContextualCellExpansion

export SemigroupBasis.CoRoots.S5_415.ContextualCellExpansion
  (noSingletonLetters repeatedWord sameLetterSupport
    singletonMeasure_lt)

end Brandt.ContextualCellExpansion

namespace Brandt.SameLetterSupport

export SemigroupBasis.CoRoots.S5_415.SameLetterSupport (refl)

end Brandt.SameLetterSupport

abbrev basis : List (Identity Nat) := H7.basis

/-! ## H7 inverse witnesses -/

/-- Proof-relevant regularity modulo the H7 presentation. -/
structure InverseWitness (word : Word Nat) where
  inverse : Word Nat
  word_inverse_word :
    Derives basis ((word ++ inverse) ++ word) word
  inverse_word_inverse :
    Derives basis ((inverse ++ word) ++ inverse) inverse

/-- The product of a word and its chosen inverse is derivably idempotent. -/
theorem InverseWitness.derivesWordInverseIdempotent
    {word : Word Nat} (witness : InverseWitness word) :
    Derives basis
      ((word ++ witness.inverse) ++ (word ++ witness.inverse))
      (word ++ witness.inverse) := by
  simpa [Word.append_assoc] using
    Derives.appendRight witness.word_inverse_word witness.inverse

/-- The reverse product is derivably idempotent as well. -/
theorem InverseWitness.derivesInverseWordIdempotent
    {word : Word Nat} (witness : InverseWitness word) :
    Derives basis
      ((witness.inverse ++ word) ++ (witness.inverse ++ word))
      (witness.inverse ++ word) := by
  simpa [Word.append_assoc] using
    Derives.appendRight witness.inverse_word_inverse word

/-- Pull a regularity witness back along an H7 derivation. -/
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

private def cell (A B : Word Nat) : Word Nat :=
  (A ++ B) ++ A

private theorem derivesCellInverseLaw (A B : Word Nat) :
    Derives basis
      ((cell A B ++ cell B A) ++ cell A B)
      (cell A B) := by
  have step1 :
      Derives basis
        ((cell A B ++ cell B A) ++ cell A B)
        ((((((A ++ B) ++ A) ++ B) ++ A) ++ B) ++ A) := by
    simpa [cell, Word.append_assoc] using
      Derives.appendRight (H7.derivesSandwichContraction A B)
        (((B ++ A) ++ B) ++ A)
  have step2 :
      Derives basis
        ((((((A ++ B) ++ A) ++ B) ++ A) ++ B) ++ A)
        ((((A ++ B) ++ A) ++ B) ++ A) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (H7.derivesSandwichContraction A B)
        (B ++ A)
  have step3 :
      Derives basis
        ((((A ++ B) ++ A) ++ B) ++ A)
        (cell A B) := by
    simpa [cell] using H7.derivesSandwichContraction A B
  exact step1.trans <| step2.trans step3

private def cellInverseWitness (A B : Word Nat) :
    InverseWitness (cell A B) where
  inverse := cell B A
  word_inverse_word := derivesCellInverseLaw A B
  inverse_word_inverse := derivesCellInverseLaw B A

private def emptyGapSquare (A : Word Nat) : Word Nat :=
  A ++ A

private theorem derivesEmptyGapSquareIdempotent (A : Word Nat) :
    Derives basis
      (emptyGapSquare A ++ emptyGapSquare A)
      (emptyGapSquare A) := by
  have first :
      Derives basis
        ((A ++ A) ++ (A ++ A))
        ((A ++ A) ++ A) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (H7.derivesPowerContraction A) A
  simpa [emptyGapSquare] using
    first.trans (H7.derivesPowerContraction A)

private theorem derivesEmptyGapSquareInverseLaw (A : Word Nat) :
    Derives basis
      ((emptyGapSquare A ++ emptyGapSquare A) ++ emptyGapSquare A)
      (emptyGapSquare A) := by
  have first :=
    Derives.appendRight (derivesEmptyGapSquareIdempotent A)
      (emptyGapSquare A)
  exact first.trans (derivesEmptyGapSquareIdempotent A)

private def emptyGapSquareInverseWitness (A : Word Nat) :
    InverseWitness (emptyGapSquare A) where
  inverse := emptyGapSquare A
  word_inverse_word := derivesEmptyGapSquareInverseLaw A
  inverse_word_inverse := derivesEmptyGapSquareInverseLaw A

/-- Guarded idempotent commutation is exactly enough to multiply inverse
witnesses.  The two guards are respectively `u` and `vInv`; no unguarded
square exchange occurs. -/
def InverseWitness.append
    {u v : Word Nat}
    (uWitness : InverseWitness u)
    (vWitness : InverseWitness v) :
    InverseWitness (u ++ v) where
  inverse := vWitness.inverse ++ uWitness.inverse
  word_inverse_word := by
    have commuteMiddle :=
      H7.derivesGuardedCommuteIdempotents
        u
        (v ++ vWitness.inverse)
        (uWitness.inverse ++ u)
        vWitness.derivesWordInverseIdempotent
        uWitness.derivesInverseWordIdempotent
    have step1 :
        Derives basis
          (((u ++ v) ++
              (vWitness.inverse ++ uWitness.inverse)) ++ (u ++ v))
          (((((u ++ uWitness.inverse) ++ u) ++ v) ++
              vWitness.inverse) ++ v) := by
      simpa [Word.append_assoc] using
        Derives.appendRight commuteMiddle v
    have step2 :
        Derives basis
          (((((u ++ uWitness.inverse) ++ u) ++ v) ++
              vWitness.inverse) ++ v)
          (((u ++ v) ++ vWitness.inverse) ++ v) := by
      simpa [Word.append_assoc] using
        Derives.appendRight uWitness.word_inverse_word
          ((v ++ vWitness.inverse) ++ v)
    have step3 :
        Derives basis
          (((u ++ v) ++ vWitness.inverse) ++ v)
          (u ++ v) := by
      simpa [Word.append_assoc] using
        Derives.prepend u vWitness.word_inverse_word
    exact step1.trans <| step2.trans step3
  inverse_word_inverse := by
    have commuteMiddle :=
      H7.derivesGuardedCommuteIdempotents
        vWitness.inverse
        (uWitness.inverse ++ u)
        (v ++ vWitness.inverse)
        uWitness.derivesInverseWordIdempotent
        vWitness.derivesWordInverseIdempotent
    have step1 :
        Derives basis
          (((vWitness.inverse ++ uWitness.inverse) ++ (u ++ v)) ++
              (vWitness.inverse ++ uWitness.inverse))
          (((((vWitness.inverse ++ v) ++ vWitness.inverse) ++
              uWitness.inverse) ++ u) ++ uWitness.inverse) := by
      simpa [Word.append_assoc] using
        Derives.appendRight commuteMiddle uWitness.inverse
    have step2 :
        Derives basis
          (((((vWitness.inverse ++ v) ++ vWitness.inverse) ++
              uWitness.inverse) ++ u) ++ uWitness.inverse)
          (((vWitness.inverse ++ uWitness.inverse) ++ u) ++
              uWitness.inverse) := by
      simpa [Word.append_assoc] using
        Derives.appendRight vWitness.inverse_word_inverse
          ((uWitness.inverse ++ u) ++ uWitness.inverse)
    have step3 :
        Derives basis
          (((vWitness.inverse ++ uWitness.inverse) ++ u) ++
              uWitness.inverse)
          (vWitness.inverse ++ uWitness.inverse) := by
      simpa [Word.append_assoc] using
        Derives.prepend vWitness.inverse
          uWitness.inverse_word_inverse
    exact step1.trans <| step2.trans step3

/-- Every Volkov cell has an H7 inverse witness. -/
def cellFactorInverseWitness (factor : Brandt.CellFactor) :
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

/-- Finite products of Volkov cells are regular in the H7 presentation. -/
def cellProductInverseWitness :
    (product : Brandt.CellProduct) →
      InverseWitness product.word
  | .single factor => cellFactorInverseWitness factor
  | .snoc prior factor =>
      (cellProductInverseWitness prior).append
        (cellFactorInverseWitness factor)

/-! ## Replaying the expansion-only cell factorization in H7 -/

private theorem derivesInListContext
    {source target localSource localTarget : Word Nat}
    (derivation : Derives basis localSource localTarget)
    (leftContext suffix : List Nat)
    (sourceShape :
      source.toList = leftContext ++ localSource.toList ++ suffix)
    (targetShape :
      target.toList = leftContext ++ localTarget.toList ++ suffix) :
    Derives basis source target := by
  cases leftContext with
  | nil =>
      cases suffix with
      | nil =>
          have sourceEq : source = localSource :=
            Word.toList_injective (by simpa using sourceShape)
          have targetEq : target = localTarget :=
            Word.toList_injective (by simpa using targetShape)
          subst source
          subst target
          exact derivation
      | cons suffixHead suffixTail =>
          let suffixWord : Word Nat := ⟨suffixHead, suffixTail⟩
          have sourceEq : source = localSource ++ suffixWord :=
            Word.toList_injective (by
              rw [Word.toList_append]
              simpa [suffixWord] using sourceShape)
          have targetEq : target = localTarget ++ suffixWord :=
            Word.toList_injective (by
              rw [Word.toList_append]
              simpa [suffixWord] using targetShape)
          subst source
          subst target
          exact Derives.appendRight derivation suffixWord
  | cons prefixHead prefixTail =>
      let prefixWord : Word Nat := ⟨prefixHead, prefixTail⟩
      cases suffix with
      | nil =>
          have sourceEq : source = prefixWord ++ localSource :=
            Word.toList_injective (by
              rw [Word.toList_append]
              simpa [prefixWord] using sourceShape)
          have targetEq : target = prefixWord ++ localTarget :=
            Word.toList_injective (by
              rw [Word.toList_append]
              simpa [prefixWord] using targetShape)
          subst source
          subst target
          exact Derives.prepend prefixWord derivation
      | cons suffixHead suffixTail =>
          let suffixWord : Word Nat := ⟨suffixHead, suffixTail⟩
          have sourceEq :
              source = (prefixWord ++ localSource) ++ suffixWord :=
            Word.toList_injective (by
              simp only [Word.toList_append]
              simpa [prefixWord, suffixWord, List.append_assoc] using
                sourceShape)
          have targetEq :
              target = (prefixWord ++ localTarget) ++ suffixWord :=
            Word.toList_injective (by
              simp only [Word.toList_append]
              simpa [prefixWord, suffixWord, List.append_assoc] using
                targetShape)
          subst source
          subst target
          exact Derives.appendRight
            (Derives.prepend prefixWord derivation) suffixWord

/-- An H7 derivation attached to the already-proved combinatorial
certificate for one contextual cell expansion. -/
structure ContextualCellExpansion
    {word : Word Nat} {tested : Nat}
    (selected : Brandt.CellContains word tested)
    (expanded : Word Nat) : Prop where
  derives : Derives basis word expanded
  brandtStep : Brandt.ContextualCellExpansion selected expanded

theorem ContextualCellExpansion.expanded_toList
    {word expanded : Word Nat} {tested : Nat}
    {selected : Brandt.CellContains word tested}
    (step : ContextualCellExpansion selected expanded) :
    expanded.toList =
      selected.leadingContext ++ selected.cellLetters ++
        selected.expansionCopy ++ selected.suffix :=
  step.brandtStep.expanded_toList

theorem ContextualCellExpansion.sameLetterSupport
    {word expanded : Word Nat} {tested : Nat}
    {selected : Brandt.CellContains word tested}
    (step : ContextualCellExpansion selected expanded) :
    Brandt.SameLetterSupport word expanded :=
  Brandt.ContextualCellExpansion.sameLetterSupport
    step.brandtStep

theorem ContextualCellExpansion.repeatedWord
    {word expanded : Word Nat} {tested : Nat}
    {selected : Brandt.CellContains word tested}
    (step : ContextualCellExpansion selected expanded)
    (repeated : Brandt.RepeatedWord word) :
    Brandt.RepeatedWord expanded :=
  Brandt.ContextualCellExpansion.repeatedWord
    step.brandtStep repeated

theorem ContextualCellExpansion.singletonMeasure_lt
    {word expanded : Word Nat} {tested : Nat}
    {selected : Brandt.CellContains word tested}
    (step : ContextualCellExpansion selected expanded)
    (testedSingleton : word.toList.count tested = 1) :
    Brandt.singletonMeasure expanded <
      Brandt.singletonMeasure word :=
  Brandt.ContextualCellExpansion.singletonMeasure_lt
    step.brandtStep testedSingleton

theorem ContextualCellExpansion.noSingletonLetters
    {word expanded : Word Nat} {tested : Nat}
    {selected : Brandt.CellContains word tested}
    (step : ContextualCellExpansion selected expanded)
    (sourceNoSingleton : Brandt.NoSingletonLetters word) :
    Brandt.NoSingletonLetters expanded :=
  Brandt.ContextualCellExpansion.noSingletonLetters
    step.brandtStep sourceNoSingleton

/-- Every cell expansion used by Volkov's finite recursion replays in H7:
the empty interior is power expansion and the nonempty interior is sandwich
expansion.  Neither case uses square commutation. -/
theorem existsContextualCellExpansion
    {word : Word Nat} {tested : Nat}
    (selected : Brandt.CellContains word tested) :
    ∃ expanded, ContextualCellExpansion selected expanded := by
  obtain ⟨expanded, brandtStep⟩ :=
    selected.exists_contextualCellExpansion
  refine ⟨expanded, { derives := ?_, brandtStep := brandtStep }⟩
  cases interiorShape : selected.p with
  | nil =>
      let boundaryWord := Word.singleton selected.y
      apply derivesInListContext
        (H7.derivesPowerExpansion boundaryWord)
        selected.leadingContext selected.suffix
      · simpa [Brandt.CellContains.cellLetters, boundaryWord,
          interiorShape, Word.toList_append, List.append_assoc] using
          selected.toList_eq_context
      · simpa [Brandt.CellContains.cellLetters,
          Brandt.CellContains.expansionCopy, boundaryWord,
          interiorShape, Word.toList_append, List.append_assoc] using
          brandtStep.expanded_toList
  | cons interiorHead interiorTail =>
      let boundaryWord := Word.singleton selected.y
      let interiorWord : Word Nat := ⟨interiorHead, interiorTail⟩
      apply derivesInListContext
        (H7.derivesSandwichExpansion boundaryWord interiorWord)
        selected.leadingContext selected.suffix
      · simpa [Brandt.CellContains.cellLetters, boundaryWord,
          interiorWord, interiorShape, Word.toList_append,
          List.append_assoc] using selected.toList_eq_context
      · simpa [Brandt.CellContains.cellLetters,
          Brandt.CellContains.expansionCopy, boundaryWord,
          interiorWord, interiorShape, Word.toList_append,
          List.append_assoc] using brandtStep.expanded_toList

private theorem existsRepeatedContextualExpansion
    {word : Word Nat} (repeated : Brandt.RepeatedWord word)
    {tested : Nat} (testedSingleton : word.toList.count tested = 1) :
    ∃ expanded,
      Derives basis word expanded ∧
        Brandt.SameLetterSupport word expanded ∧
        Brandt.RepeatedWord expanded ∧
        Brandt.singletonMeasure expanded <
          Brandt.singletonMeasure word := by
  have testedMember : tested ∈ word.toList :=
    List.count_pos_iff.mp (by omega)
  let selected := repeated tested testedMember
  obtain ⟨expanded, step⟩ :=
    existsContextualCellExpansion selected
  exact
    ⟨expanded, step.derives, step.sameLetterSupport,
      step.repeatedWord repeated,
      step.singletonMeasure_lt testedSingleton⟩

/-- The singleton-elimination phase of the repeated-word construction,
replayed with H7 derivations. -/
theorem repeatedWord_derives_noSingletonLetters
    {word : Word Nat} (repeated : Brandt.RepeatedWord word) :
    ∃ target,
      Derives basis word target ∧
        Brandt.SameLetterSupport word target ∧
          Brandt.NoSingletonLetters target := by
  have closeAtMeasure :
      ∀ bound current,
        Brandt.singletonMeasure current = bound →
          Brandt.RepeatedWord current →
            ∃ target,
              Derives basis current target ∧
                Brandt.SameLetterSupport current target ∧
                  Brandt.NoSingletonLetters target := by
    intro bound
    exact Nat.strongRecOn
      (motive := fun currentBound =>
        ∀ current,
          Brandt.singletonMeasure current = currentBound →
            Brandt.RepeatedWord current →
              ∃ target,
                Derives basis current target ∧
                  Brandt.SameLetterSupport current target ∧
                    Brandt.NoSingletonLetters target)
      bound (by
        intro currentBound induction current measureEq currentRepeated
        cases singletonShape : Brandt.singletonLetters current with
        | nil =>
            refine
              ⟨current, Derives.refl current,
                Brandt.SameLetterSupport.refl current, ?_⟩
            intro letter _ countOne
            have member :
                letter ∈ Brandt.singletonLetters current :=
              (Brandt.mem_singletonLetters_iff current letter).mpr
                countOne
            rw [singletonShape] at member
            simp at member
        | cons tested rest =>
            have testedInSingletons :
                tested ∈ Brandt.singletonLetters current := by
              rw [singletonShape]
              simp
            have testedSingleton :
                current.toList.count tested = 1 :=
              (Brandt.mem_singletonLetters_iff current tested).mp
                testedInSingletons
            obtain ⟨expanded, expansion, sameSupport,
                expandedRepeated, smaller⟩ :=
              existsRepeatedContextualExpansion
                currentRepeated testedSingleton
            have smallerBound :
                Brandt.singletonMeasure expanded < currentBound := by
              simpa [measureEq] using smaller
            obtain ⟨target, remainder, finalSupport, noSingletons⟩ :=
              induction (Brandt.singletonMeasure expanded)
                smallerBound expanded rfl expandedRepeated
            exact
              ⟨target, expansion.trans remainder,
                sameSupport.trans finalSupport, noSingletons⟩)
  exact closeAtMeasure
    (Brandt.singletonMeasure word) word rfl repeated

private theorem existsRightmostSplit
    {value : Nat} {letters : List Nat}
    (member : value ∈ letters) :
    ∃ before after,
      letters = before ++ value :: after ∧ value ∉ after := by
  induction letters with
  | nil =>
      simp at member
  | cons head tail induction =>
      by_cases inTail : value ∈ tail
      · obtain ⟨before, after, shape, notAfter⟩ :=
          induction inTail
        exact
          ⟨head :: before, after, by simp [shape], notAfter⟩
      · have equal : value = head := by
          simpa [inTail] using member
        subst head
        exact ⟨[], tail, by simp, inTail⟩

/-- Greedy continuation from a cell-product prefix.  This is the
proof-relevant S5 construction with its only algebraic step replaced by
`existsContextualCellExpansion`. -/
private theorem existsDerivesCellProductOfPrefix
    (current : Word Nat)
    (builtProduct : Brandt.CellProduct)
    (remainder : List Nat)
    (shape :
      current.toList = builtProduct.word.toList ++ remainder)
    (remainderOmits :
      builtProduct.RemainderOmitsBoundaries remainder)
    (noSingleton : Brandt.NoSingletonLetters current) :
    ∃ product : Brandt.CellProduct,
      Derives basis current product.word := by
  have closeAtLength :
      ∀ bound remainder,
        remainder.length = bound →
          ∀ (current : Word Nat)
              (builtProduct : Brandt.CellProduct),
            current.toList =
                builtProduct.word.toList ++ remainder →
              builtProduct.RemainderOmitsBoundaries remainder →
                Brandt.NoSingletonLetters current →
                  ∃ product : Brandt.CellProduct,
                    Derives basis current product.word := by
    intro bound
    refine Nat.strongRecOn
      (motive := fun currentBound =>
        ∀ remainder,
          remainder.length = currentBound →
            ∀ (current : Word Nat)
                (builtProduct : Brandt.CellProduct),
              current.toList =
                  builtProduct.word.toList ++ remainder →
                builtProduct.RemainderOmitsBoundaries remainder →
                  Brandt.NoSingletonLetters current →
                    ∃ product : Brandt.CellProduct,
                      Derives basis current product.word)
      bound ?_
    intro currentBound induction remainder lengthEq
      current builtProduct shape remainderOmits noSingleton
    cases remainder with
    | nil =>
        have currentEq : current = builtProduct.word :=
          Word.toList_injective (by simpa using shape)
        subst current
        exact ⟨builtProduct, Derives.refl builtProduct.word⟩
    | cons tested tail =>
        by_cases repeatedInTail : tested ∈ tail
        · obtain
            ⟨interior, nextRemainder, tailShape,
              testedNotNext⟩ :=
            existsRightmostSplit repeatedInTail
          let nextFactor : Brandt.CellFactor :=
            ⟨tested, interior⟩
          let nextPrefix : Brandt.CellProduct :=
            Brandt.CellProduct.snoc builtProduct nextFactor
          have nextShape :
              current.toList =
                nextPrefix.word.toList ++ nextRemainder := by
            rw [shape, tailShape]
            simp [nextPrefix, nextFactor,
              Brandt.CellProduct.word, Brandt.CellFactor.word,
              Word.toList, Word.toList_append, List.append_assoc]
          have nextRemainderOmits :
              nextPrefix.RemainderOmitsBoundaries
                nextRemainder := by
            intro boundary boundaryMember
            simp [nextPrefix, nextFactor,
              Brandt.CellProduct.RemainderOmitsBoundaries,
              Brandt.CellProduct.boundaries] at boundaryMember
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
              nextRemainder.length <
                (tested :: tail).length := by
            rw [tailShape]
            simp only [List.length_cons, List.length_append]
            omega
          have smaller :
              nextRemainder.length < currentBound := by
            calc
              nextRemainder.length <
                  (tested :: tail).length :=
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
          have prefixMember :
              tested ∈ builtProduct.word.toList :=
            List.count_pos_iff.mp prefixPositive
          obtain
              ⟨left, right, prefixShape, _testedNotRight⟩ :=
            existsRightmostSplit prefixMember
          let crossingCell : Brandt.CellContains current tested :=
            { y := tested
              leadingContext := left
              p := right
              suffix := tail
              factorization := by
                rw [shape, prefixShape]
                simp [List.append_assoc]
              tested_mem := by simp }
          obtain ⟨expanded, step⟩ :=
            existsContextualCellExpansion crossingCell
          let nextFactor : Brandt.CellFactor :=
            ⟨tested, right⟩
          let nextPrefix : Brandt.CellProduct :=
            Brandt.CellProduct.snoc builtProduct nextFactor
          have expandedShape :
              expanded.toList =
                nextPrefix.word.toList ++ tail := by
            rw [step.expanded_toList]
            simp only [crossingCell, nextPrefix, nextFactor,
              Brandt.CellContains.cellLetters,
              Brandt.CellContains.expansionCopy,
              Brandt.CellProduct.word, Word.toList_append,
              Brandt.CellFactor.word_toList]
            rw [prefixShape]
            simp [List.append_assoc]
          have nextRemainderOmits :
              nextPrefix.RemainderOmitsBoundaries tail := by
            intro boundary boundaryMember
            simp [nextPrefix, nextFactor,
              Brandt.CellProduct.RemainderOmitsBoundaries,
              Brandt.CellProduct.boundaries] at boundaryMember
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
            induction tail.length smaller tail rfl
              expanded nextPrefix expandedShape
                nextRemainderOmits
                (step.noSingletonLetters noSingleton)
          exact
            ⟨product, step.derives.trans remainderDerivation⟩
  exact closeAtLength remainder.length remainder rfl
    current builtProduct shape remainderOmits noSingleton

private theorem headMemTailOfNoSingletonLetters
    (word : Word Nat)
    (noSingleton : Brandt.NoSingletonLetters word) :
    word.head ∈ word.tail := by
  apply Decidable.byContradiction
  intro absent
  have tailCount : word.tail.count word.head = 0 :=
    List.count_eq_zero.mpr absent
  have countOne : word.toList.count word.head = 1 := by
    simp [Word.toList, tailCount]
  exact noSingleton word.head (by simp [Word.toList]) countOne

/-- Every nonempty no-singleton word derives in H7 to a finite nonempty
product of Volkov cells. -/
theorem noSingletonLetters_derives_cellProduct
    {word : Word Nat}
    (noSingleton : Brandt.NoSingletonLetters word) :
    ∃ product : Brandt.CellProduct,
      Derives basis word product.word := by
  have repeatedHead :=
    headMemTailOfNoSingletonLetters word noSingleton
  obtain
      ⟨interior, remainder, tailShape, headNotRemainder⟩ :=
    existsRightmostSplit repeatedHead
  let firstFactor : Brandt.CellFactor :=
    ⟨word.head, interior⟩
  let firstProduct : Brandt.CellProduct :=
    Brandt.CellProduct.single firstFactor
  have initialShape :
      word.toList =
        firstProduct.word.toList ++ remainder := by
    simp [Word.toList, firstProduct, firstFactor,
      Brandt.CellProduct.word, Brandt.CellFactor.word,
      tailShape, List.append_assoc]
  have initialRemainderOmits :
      firstProduct.RemainderOmitsBoundaries remainder := by
    intro boundary boundaryMember
    have equal : boundary = word.head := by
      simpa [firstProduct, firstFactor,
        Brandt.CellProduct.boundaries] using boundaryMember
    subst boundary
    exact headNotRemainder
  exact existsDerivesCellProductOfPrefix
    word firstProduct remainder initialShape
      initialRemainderOmits noSingleton

/-- An H7 inverse witness descends to an inverse pair in the H7 term
semigroup. -/
theorem InverseWitness.termClass_isInverse
    {word : Word Nat} (witness : InverseWitness word) :
    (termSemigroup basis).IsInverse
      (termClass basis word)
      (termClass basis witness.inverse) := by
  constructor
  · simpa only [termSemigroup_mul_termClass] using
      (termClass_eq_iff_derives basis).2 witness.word_inverse_word
  · simpa only [termSemigroup_mul_termClass] using
      (termClass_eq_iff_derives basis).2 witness.inverse_word_inverse

theorem InverseWitness.termClass_isRegular
    {word : Word Nat} (witness : InverseWitness word) :
    (termSemigroup basis).IsRegular (termClass basis word) :=
  ⟨termClass basis witness.inverse, witness.termClass_isInverse⟩

/-- The exact constructive regularity boundary.  The combinatorial
cell-factorization already exists for `S5_415`; this proposition asks that
its expansion-only construction be replayed in the H7 presentation. -/
def RepeatedCellProductExposure : Prop :=
  ∀ word : Word Nat,
    Brandt.RepeatedWord word →
      ∃ product : Brandt.CellProduct,
        Derives basis word product.word

/-- The expansion-only recursion above discharges the constructive
cell-product boundary. -/
theorem repeatedCellProductExposure :
    RepeatedCellProductExposure := by
  intro word repeated
  obtain ⟨withoutSingletons, firstDerivation, _sameSupport,
      noSingletons⟩ :=
    repeatedWord_derives_noSingletonLetters repeated
  obtain ⟨product, secondDerivation⟩ :=
    noSingletonLetters_derives_cellProduct noSingletons
  exact ⟨product, firstDerivation.trans secondDerivation⟩

/-- Cell-product exposure supplies the regularity input required by
Kublanovskii separation. -/
theorem repeatedTermClass_isRegular_of_cellProductExposure
    (exposure : RepeatedCellProductExposure)
    {word : Word Nat} (repeated : Brandt.RepeatedWord word) :
    (termSemigroup basis).IsRegular (termClass basis word) := by
  rcases exposure word repeated with ⟨product, derivation⟩
  exact InverseWitness.termClass_isRegular <|
    (cellProductInverseWitness product).pullback derivation

/-! ## Guarded Kublanovskii separation -/

private theorem mul_reverse_mul_eq_self_of_isInverse
    {G : Semigroup S} {a aInv : S} (inverse : G.IsInverse a aInv) :
    G.mul a (G.mul aInv a) = a := by
  calc
    G.mul a (G.mul aInv a) = G.mul (G.mul a aInv) a :=
      (G.assoc a aInv a).symm
    _ = a := inverse.1

private theorem self_principalSandwichMem_of_isInverse
    {G : Semigroup S} {a aInv : S} (inverse : G.IsInverse a aInv) :
    G.PrincipalSandwichMem a a := by
  refine ⟨G.mul a aInv, G.mul aInv a, ?_⟩
  calc
    a = G.mul (G.mul a aInv) a := inverse.1.symm
    _ = G.mul a (G.mul aInv a) := G.assoc a aInv a
    _ = G.mul (G.mul (G.mul a aInv) a) (G.mul aInv a) := by
      rw [inverse.1]

private theorem reverse_mul_principalSandwichMem_of_isInverse
    {G : Semigroup S} {a aInv : S} (inverse : G.IsInverse a aInv) :
    G.PrincipalSandwichMem a (G.mul aInv a) := by
  refine ⟨aInv, G.mul aInv a, ?_⟩
  exact inverse.reverse_mul_idempotent.symm

private theorem principalSandwichMem_trans
    {G : Semigroup S} {x y z : S}
    (xy : G.PrincipalSandwichMem y x)
    (yz : G.PrincipalSandwichMem z y) :
    G.PrincipalSandwichMem z x := by
  rcases xy with ⟨p, q, xFactor⟩
  rcases yz with ⟨r, s, yFactor⟩
  refine ⟨G.mul p r, G.mul s q, ?_⟩
  calc
    x = G.mul (G.mul p y) q := xFactor
    _ = G.mul (G.mul p (G.mul (G.mul r z) s)) q := by
      rw [yFactor]
    _ = G.mul (G.mul (G.mul p r) z) (G.mul s q) := by
      simp only [G.assoc]

/-- Volkov's right-Schutzenberger separation argument needs only guarded
idempotent commutation.  In its unique commutation step the permanent guard
is the regular element `a` itself. -/
theorem distinct_regular_rightSchutzenberger_separation_of_leftGuarded
    {G : Semigroup S} {a b : S}
    (guarded : H7.LeftGuardedIdempotentsCommute G)
    (aRegular : G.IsRegular a) (bRegular : G.IsRegular b)
    (different : a ≠ b) :
    G.RightSchutzenbergerSeparates a a b ∨
      G.RightSchutzenbergerSeparates b a b := by
  classical
  rcases aRegular with ⟨aInv, aInverse⟩
  rcases bRegular with ⟨bInv, bInverse⟩
  have aReverse : G.mul a (G.mul aInv a) = a :=
    mul_reverse_mul_eq_self_of_isInverse aInverse
  have bReverse : G.mul b (G.mul bInv b) = b :=
    mul_reverse_mul_eq_self_of_isInverse bInverse
  have aInOwnSandwich : G.PrincipalSandwichMem a a :=
    self_principalSandwichMem_of_isInverse aInverse
  have bInOwnSandwich : G.PrincipalSandwichMem b b :=
    self_principalSandwichMem_of_isInverse bInverse
  have aIdempotentInA :
      G.PrincipalSandwichMem a (G.mul aInv a) :=
    reverse_mul_principalSandwichMem_of_isInverse aInverse
  have bIdempotentInB :
      G.PrincipalSandwichMem b (G.mul bInv b) :=
    reverse_mul_principalSandwichMem_of_isInverse bInverse
  have aIdempotent : G.IsIdempotent (G.mul aInv a) :=
    aInverse.reverse_mul_idempotent
  have bIdempotent : G.IsIdempotent (G.mul bInv b) :=
    bInverse.reverse_mul_idempotent

  by_cases aOutside : ¬ G.PrincipalSandwichMem b a
  · have bInIdealA : b ∈ Semigroup.I_z G a := by
      change ¬ G.PrincipalSandwichMem b a
      exact aOutside
    have aNotInIdealA : ¬ (a ∈ Semigroup.I_z G a) := by
      intro aInIdeal
      change ¬ G.PrincipalSandwichMem a a at aInIdeal
      exact aInIdeal aInOwnSandwich
    have bTimesAIdempotentInIdeal :
        G.mul b (G.mul aInv a) ∈ Semigroup.I_z G a :=
      (Semigroup.I_z G a).mul_mem_right bInIdealA (G.mul aInv a)
    have aTimesAIdempotentNotInIdeal :
        ¬ (G.mul a (G.mul aInv a) ∈ Semigroup.I_z G a) := by
      intro member
      rw [aReverse] at member
      exact aNotInIdealA member
    refine Or.inl ⟨G.mul aInv a, aIdempotentInA, ?_⟩
    intro rees
    rcases rees with equal | both
    · apply aTimesAIdempotentNotInIdeal
      rw [equal]
      exact bTimesAIdempotentInIdeal
    · exact aTimesAIdempotentNotInIdeal both.1
  · have aInside : G.PrincipalSandwichMem b a := by
      apply Classical.byContradiction
      intro contradiction
      exact aOutside contradiction
    by_cases bOutside : ¬ G.PrincipalSandwichMem a b
    · have aInIdealB : a ∈ Semigroup.I_z G b := by
        change ¬ G.PrincipalSandwichMem a b
        exact bOutside
      have bNotInIdealB : ¬ (b ∈ Semigroup.I_z G b) := by
        intro bInIdeal
        change ¬ G.PrincipalSandwichMem b b at bInIdeal
        exact bInIdeal bInOwnSandwich
      have aTimesBIdempotentInIdeal :
          G.mul a (G.mul bInv b) ∈ Semigroup.I_z G b :=
        (Semigroup.I_z G b).mul_mem_right aInIdealB (G.mul bInv b)
      have bTimesBIdempotentNotInIdeal :
          ¬ (G.mul b (G.mul bInv b) ∈ Semigroup.I_z G b) := by
        intro member
        rw [bReverse] at member
        exact bNotInIdealB member
      refine Or.inr ⟨G.mul bInv b, bIdempotentInB, ?_⟩
      intro rees
      rcases rees with equal | both
      · apply bTimesBIdempotentNotInIdeal
        rw [← equal]
        exact aTimesBIdempotentInIdeal
      · exact bTimesBIdempotentNotInIdeal both.2
    · have bInside : G.PrincipalSandwichMem a b := by
        apply Classical.byContradiction
        intro contradiction
        exact bOutside contradiction
      have sandwichEq (x : S) :
          G.PrincipalSandwichMem a x ↔
            G.PrincipalSandwichMem b x := by
        constructor
        · intro xInA
          exact principalSandwichMem_trans xInA aInside
        · intro xInB
          exact principalSandwichMem_trans xInB bInside
      have bIdempotentInA :
          G.PrincipalSandwichMem a (G.mul bInv b) :=
        (sandwichEq (G.mul bInv b)).2 bIdempotentInB
      have aNotInIdealA : ¬ (a ∈ Semigroup.I_z G a) := by
        intro aInIdeal
        change ¬ G.PrincipalSandwichMem a a at aInIdeal
        exact aInIdeal aInOwnSandwich
      have bNotInIdealA : ¬ (b ∈ Semigroup.I_z G a) := by
        intro bInIdeal
        change ¬ G.PrincipalSandwichMem b a at bInIdeal
        exact bInIdeal aInside
      have aTimesAIdempotentNotInIdeal :
          ¬ (G.mul a (G.mul aInv a) ∈ Semigroup.I_z G a) := by
        intro member
        rw [aReverse] at member
        exact aNotInIdealA member
      have bTimesBIdempotentNotInIdeal :
          ¬ (G.mul b (G.mul bInv b) ∈ Semigroup.I_z G a) := by
        intro member
        rw [bReverse] at member
        exact bNotInIdealA member

      by_cases reesAtA :
          (Semigroup.I_z G a).ReesRel
            (G.mul a (G.mul aInv a))
            (G.mul b (G.mul aInv a))
      · have aTimesAEq :
            G.mul a (G.mul aInv a) =
              G.mul b (G.mul aInv a) := by
          rcases reesAtA with equal | both
          · exact equal
          · exact (aTimesAIdempotentNotInIdeal both.1).elim
        by_cases reesAtB :
            (Semigroup.I_z G a).ReesRel
              (G.mul a (G.mul bInv b))
              (G.mul b (G.mul bInv b))
        · have aTimesBEq :
              G.mul a (G.mul bInv b) =
                G.mul b (G.mul bInv b) := by
            rcases reesAtB with equal | both
            · exact equal
            · exact (bTimesBIdempotentNotInIdeal both.2).elim
          have equal : a = b := by
            calc
              a = G.mul a (G.mul aInv a) := aReverse.symm
              _ = G.mul b (G.mul aInv a) := aTimesAEq
              _ =
                  G.mul (G.mul b (G.mul bInv b))
                    (G.mul aInv a) :=
                congrArg (fun x => G.mul x (G.mul aInv a))
                  bReverse.symm
              _ =
                  G.mul (G.mul a (G.mul bInv b))
                    (G.mul aInv a) :=
                congrArg (fun x => G.mul x (G.mul aInv a))
                  aTimesBEq.symm
              _ =
                  G.mul (G.mul a (G.mul aInv a))
                    (G.mul bInv b) :=
                guarded a bIdempotent aIdempotent
              _ = G.mul a (G.mul bInv b) :=
                congrArg (fun x => G.mul x (G.mul bInv b))
                  aReverse
              _ = G.mul b (G.mul bInv b) := aTimesBEq
              _ = b := bReverse
          exact False.elim (different equal)
        · exact Or.inl ⟨G.mul bInv b, bIdempotentInA, reesAtB⟩
      · exact Or.inl ⟨G.mul aInv a, aIdempotentInA, reesAtA⟩

/-- Projection form of guarded Kublanovskii separation. -/
theorem
    distinct_regular_rightSchutzenberger_projection_separation_of_leftGuarded
    {G : Semigroup S} {a b : S}
    (guarded : H7.LeftGuardedIdempotentsCommute G)
    (aRegular : G.IsRegular a) (bRegular : G.IsRegular b)
    (different : a ≠ b) :
    (Semigroup.rightSchutzenbergerCongruence G a).projection.toFun a ≠
        (Semigroup.rightSchutzenbergerCongruence G a).projection.toFun b ∨
      (Semigroup.rightSchutzenbergerCongruence G b).projection.toFun a ≠
        (Semigroup.rightSchutzenbergerCongruence G b).projection.toFun b := by
  rcases
      distinct_regular_rightSchutzenberger_separation_of_leftGuarded
        guarded aRegular bRegular different with
    separatedAtA | separatedAtB
  · exact Or.inl
      ((Semigroup.rightSchutzenberger_projection_ne_iff_exists_separator
        G a).2 separatedAtA)
  · exact Or.inr
      ((Semigroup.rightSchutzenberger_projection_ne_iff_exists_separator
        G b).2 separatedAtB)

/-! ## Exact original-orientation quotient boundary -/

/-- Repeated H7 term classes are regular.  This is kept separate from
quotient validity because it has a constructive cell-factorization proof. -/
def RepeatedTermClassRegularity : Prop :=
  ∀ word : Word Nat,
    Brandt.RepeatedWord word →
      (termSemigroup basis).IsRegular (termClass basis word)

theorem repeatedTermClassRegularity_of_cellProductExposure
    (exposure : RepeatedCellProductExposure) :
    RepeatedTermClassRegularity := by
  intro word repeated
  exact
    repeatedTermClass_isRegular_of_cellProductExposure exposure repeated

/-- Repeated H7 term classes are regular, unconditionally. -/
theorem repeatedTermClassRegularity :
    RepeatedTermClassRegularity :=
  repeatedTermClassRegularity_of_cellProductExposure
    repeatedCellProductExposure

/-- The exact pairwise projection residual.  It asks only for the two
projections used by guarded Kublanovskii separation, and only when both words
are repeated. -/
def RepeatedPairRightProjectionAgreement : Prop :=
  ∀ left right : Word Nat,
    H7.SameRootedBrandtSignature left right →
      Brandt.RepeatedWord left →
        Brandt.RepeatedWord right →
          ((Semigroup.rightSchutzenbergerCongruence
              (termSemigroup basis) (termClass basis left)).projection.toFun
                (termClass basis left) =
            (Semigroup.rightSchutzenbergerCongruence
              (termSemigroup basis) (termClass basis left)).projection.toFun
                (termClass basis right)) ∧
          ((Semigroup.rightSchutzenbergerCongruence
              (termSemigroup basis) (termClass basis right)).projection.toFun
                (termClass basis left) =
            (Semigroup.rightSchutzenbergerCongruence
              (termSemigroup basis) (termClass basis right)).projection.toFun
                (termClass basis right))

/-- A reusable all-regular-class equality for original-orientation right
Schutzenberger quotients.  Only canonical singleton-class valuations are
mentioned, and no assertion is made about arbitrary quotient identities. -/
def RootedRightProjectionAgreement : Prop :=
  ∀ z : TermSemigroup basis,
    (termSemigroup basis).IsRegular z →
      ∀ left right : Word Nat,
        H7.SameRootedBrandtSignature left right →
          (Semigroup.rightSchutzenbergerCongruence
              (termSemigroup basis) z).projection.toFun
                (termClass basis left) =
            (Semigroup.rightSchutzenbergerCongruence
              (termSemigroup basis) z).projection.toFun
                (termClass basis right)

/-- A more reusable, but stronger, formulation of the same orientation
obligation: every rooted Brandt identity is valid in every selected regular
right quotient of the original H7 term semigroup. -/
def RootedRightSchutzenbergerValidity : Prop :=
  ∀ z : TermSemigroup basis,
    (termSemigroup basis).IsRegular z →
      ∀ identity : Identity Nat,
        H7.SameRootedBrandtSignature identity.lhs identity.rhs →
          identity.SatisfiedBy
            (Semigroup.rightSchutzenbergerCongruence
              (termSemigroup basis) z).quotientSemigroup

/-- Full quotient validity implies the exact canonical projection agreement
used by repeated-word separation. -/
theorem rootedRightProjectionAgreement_of_validity
    (validity : RootedRightSchutzenbergerValidity) :
    RootedRightProjectionAgreement := by
  intro z zRegular left right same
  let projection :=
    (Semigroup.rightSchutzenbergerCongruence
      (termSemigroup basis) z).projection
  have evaluated :=
    validity z zRegular (⟨left, right⟩ : Identity Nat) same
      (fun letter =>
        projection.toFun
          (termClass basis (Word.singleton letter)))
  calc
    projection.toFun (termClass basis left) =
        projection.toFun
          ((termSemigroup basis).eval
            (fun letter =>
              termClass basis (Word.singleton letter))
            left) := by
      rw [termSemigroup_eval_singletonClass]
    _ =
        (Semigroup.rightSchutzenbergerCongruence
          (termSemigroup basis) z).quotientSemigroup.eval
            (fun letter =>
              projection.toFun
                (termClass basis (Word.singleton letter)))
            left :=
      projection.map_eval
        (fun letter => termClass basis (Word.singleton letter))
        left
    _ =
        (Semigroup.rightSchutzenbergerCongruence
          (termSemigroup basis) z).quotientSemigroup.eval
            (fun letter =>
              projection.toFun
                (termClass basis (Word.singleton letter)))
            right :=
      evaluated
    _ =
        projection.toFun
          ((termSemigroup basis).eval
            (fun letter =>
              termClass basis (Word.singleton letter))
            right) :=
      (projection.map_eval
        (fun letter => termClass basis (Word.singleton letter))
        right).symm
    _ = projection.toFun (termClass basis right) := by
      rw [termSemigroup_eval_singletonClass]

theorem repeatedPairRightProjectionAgreement_of_rootedAgreement
    (agreement : RootedRightProjectionAgreement) :
    RepeatedPairRightProjectionAgreement := by
  intro left right same leftRepeated rightRepeated
  have leftRegular :=
    repeatedTermClassRegularity left leftRepeated
  have rightRegular :=
    repeatedTermClassRegularity right rightRepeated
  exact
    ⟨agreement (termClass basis left) leftRegular left right same,
      agreement (termClass basis right) rightRegular left right same⟩

/-- Guarded separation reduces `RootedRepeatedCompleteness` to repeated
term-class regularity and equality in the two selected original-orientation
right projections. -/
theorem rootedRepeatedCompleteness_of_projectionAgreement
    (regularity : RepeatedTermClassRegularity)
    (agreement : RootedRightProjectionAgreement) :
    H7.RootedRepeatedCompleteness := by
  intro left right same leftRepeated rightRepeated
  refine (termClass_eq_iff_derives basis).mp ?_
  apply Classical.byContradiction
  intro classesDifferent
  have leftRegular := regularity left leftRepeated
  have rightRegular := regularity right rightRepeated
  rcases
      distinct_regular_rightSchutzenberger_projection_separation_of_leftGuarded
        H7.termSemigroup_leftGuardedIdempotentsCommute
        leftRegular rightRegular classesDifferent with
    separatedAtLeft | separatedAtRight
  · exact separatedAtLeft <|
      agreement (termClass basis left) leftRegular left right same
  · exact separatedAtRight <|
      agreement (termClass basis right) rightRegular left right same

/-- The exact pairwise projection condition closes the repeated branch. -/
theorem rootedRepeatedCompleteness_of_repeatedPairProjectionAgreement
    (agreement : RepeatedPairRightProjectionAgreement) :
    H7.RootedRepeatedCompleteness := by
  intro left right same leftRepeated rightRepeated
  refine (termClass_eq_iff_derives basis).mp ?_
  apply Classical.byContradiction
  intro classesDifferent
  have leftRegular :=
    repeatedTermClassRegularity left leftRepeated
  have rightRegular :=
    repeatedTermClassRegularity right rightRepeated
  have pairAgreement :=
    agreement left right same leftRepeated rightRepeated
  rcases
      distinct_regular_rightSchutzenberger_projection_separation_of_leftGuarded
        H7.termSemigroup_leftGuardedIdempotentsCommute
        leftRegular rightRegular classesDifferent with
    separatedAtLeft | separatedAtRight
  · exact separatedAtLeft pairAgreement.1
  · exact separatedAtRight pairAgreement.2

/-- Conversely, a repeated-word derivation makes both quotient projections
equal.  Thus the pairwise projection statement is an exact residual, not an
extra structural assumption. -/
theorem
    repeatedPairRightProjectionAgreement_of_rootedRepeatedCompleteness
    (complete : H7.RootedRepeatedCompleteness) :
    RepeatedPairRightProjectionAgreement := by
  intro left right same leftRepeated rightRepeated
  have classesEqual :
      termClass basis left = termClass basis right :=
    (termClass_eq_iff_derives basis).2
      (complete left right same leftRepeated rightRepeated)
  exact
    ⟨congrArg
        (Semigroup.rightSchutzenbergerCongruence
          (termSemigroup basis)
          (termClass basis left)).projection.toFun
        classesEqual,
      congrArg
        (Semigroup.rightSchutzenbergerCongruence
          (termSemigroup basis)
          (termClass basis right)).projection.toFun
        classesEqual⟩

theorem rootedRepeatedCompleteness_iff_repeatedPairProjectionAgreement :
    H7.RootedRepeatedCompleteness ↔
      RepeatedPairRightProjectionAgreement :=
  ⟨repeatedPairRightProjectionAgreement_of_rootedRepeatedCompleteness,
    rootedRepeatedCompleteness_of_repeatedPairProjectionAgreement⟩

/-- The reusable all-regular-class agreement is a sufficient structural
route to the exact pairwise residual. -/
theorem rootedRepeatedCompleteness_of_originalRightProjectionAgreement
    (agreement : RootedRightProjectionAgreement) :
    H7.RootedRepeatedCompleteness :=
  rootedRepeatedCompleteness_of_repeatedPairProjectionAgreement
    (repeatedPairRightProjectionAgreement_of_rootedAgreement agreement)

/-- The constructive and quotient obligations together close the exact H7
repeated-word residual. -/
theorem rootedRepeatedCompleteness_of_cellProductExposure_and_validity
    (exposure : RepeatedCellProductExposure)
    (validity : RootedRightSchutzenbergerValidity) :
    H7.RootedRepeatedCompleteness :=
  rootedRepeatedCompleteness_of_projectionAgreement
    (repeatedTermClassRegularity_of_cellProductExposure exposure)
    (rootedRightProjectionAgreement_of_validity validity)

/-- After the constructive regularity replay, the sole remaining premise is
original-orientation right-Schutzenberger quotient validity. -/
theorem rootedRepeatedCompleteness_of_validity
    (validity : RootedRightSchutzenbergerValidity) :
    H7.RootedRepeatedCompleteness :=
  rootedRepeatedCompleteness_of_projectionAgreement
    repeatedTermClassRegularity
    (rootedRightProjectionAgreement_of_validity validity)

end SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7Repeated

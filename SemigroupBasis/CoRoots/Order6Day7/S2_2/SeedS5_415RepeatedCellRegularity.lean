import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415IsolatedParitySplit
import SemigroupBasis.CoRoots.S5_415CellFactorization

/-!
# Rank040: parity-safe repeated-word regularity

The frozen doubled laws expand a cell y p y by TWO copies of p y.
Every occurrence parity is preserved. A finite pass removes singleton
letters, and a greedy derivation factors the result into actual cells.
The already-proved rank040 square/sandwich/product inverse witnesses give
an explicit inverse for EVERY repeated word modulo the frozen basis.

The old Brandt expansion is used only for its pure repeated-cell geometry:
two insertions preserve the existing cells. Its parity-changing derivation
is NEVER transported to rank040. Every new Derives edge below is built
from the genuine doubled rank040 cell law.

Combined with IsolatedParitySplit, the full join lift is now equivalent
to derivability for word pairs carrying explicit rank040 inverse witnesses.
That regular-pair comparison remains OPEN; regularity is not cancellation.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.RepeatedCellRegularity

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_415
open BrandtParityBridge

abbrev RankInverse := ExposureReplay.InverseWitness

theorem signature_of_derives {source target : Word Nat}
    (derived : Derives Rank040.basis source target) : SameFactorSignature source target :=
  sameFactorSignature_of_factorValid (Identity.mk source target)
    (derived.sound Rank040.leftModels) (derived.sound Rank040.rightModels)

def doubledExpansionWord {word : Word Nat} {tested : Nat}
    (cell : CellContains word tested) : Word Nat :=
  ChainReplay.Context.wrap cell.leadingContext
    (((Word.mk cell.y cell.p) ++ (Word.mk cell.y cell.p)) ++
      Word.mk cell.y (cell.p ++ [cell.y])) cell.suffix

theorem doubledExpansionWord_toList {word : Word Nat} {tested : Nat}
    (cell : CellContains word tested) :
    (doubledExpansionWord cell).toList =
      cell.leadingContext ++ cell.cellLetters ++ cell.expansionCopy ++ cell.expansionCopy ++ cell.suffix := by
  simp only [doubledExpansionWord, ChainReplay.Context.wrap_toList, Word.toList_append,
    CellContains.cellLetters, CellContains.expansionCopy]
  simp only [Word.toList, List.append_assoc, List.cons_append, List.nil_append]

structure DoubledCellExpansion {word : Word Nat} {tested : Nat}
    (cell : CellContains word tested) (expanded : Word Nat) : Prop where
  derives : Derives Rank040.basis word expanded
  expanded_toList : expanded.toList =
    cell.leadingContext ++ cell.cellLetters ++ cell.expansionCopy ++ cell.expansionCopy ++ cell.suffix

/-- Empty interiors use x²=x⁴; all other cells use the doubled sandwich.
The contextual expansion is an actual frozen-basis derivation. -/
theorem exists_doubledCellExpansion {word : Word Nat} {tested : Nat}
    (cell : CellContains word tested) : ∃ expanded, DoubledCellExpansion cell expanded := by
  refine ⟨doubledExpansionWord cell, ?_, doubledExpansionWord_toList cell⟩
  have original : ChainReplay.Context.wrap cell.leadingContext
      (Word.mk cell.y (cell.p ++ [cell.y])) cell.suffix = word := by
    apply Word.toList_injective
    rw [ChainReplay.Context.wrap_toList]
    simpa only [Word.toList, List.append_assoc, List.cons_append, List.nil_append] using
      cell.factorization.symm
  have expanded := ChainReplay.Context.derives_wrap
    (CutConnectivity.literalReturnAbsorbs cell.y cell.p) cell.leadingContext cell.suffix
  rw [original] at expanded
  exact expanded

theorem DoubledCellExpansion.count_eq
    {word expanded : Word Nat} {tested : Nat} {cell : CellContains word tested}
    (step : DoubledCellExpansion cell expanded) (letter : Nat) :
    expanded.toList.count letter = word.toList.count letter + 2 * cell.expansionCopy.count letter := by
  rw [step.expanded_toList, cell.toList_eq_context]
  simp only [List.count_append]
  omega

theorem DoubledCellExpansion.parity
    {word expanded : Word Nat} {tested : Nat} {cell : CellContains word tested}
    (step : DoubledCellExpansion cell expanded) : SameOccurrenceParity word expanded := by
  intro letter
  rw [step.count_eq letter]
  omega

theorem DoubledCellExpansion.sameFactorSignature
    {word expanded : Word Nat} {tested : Nat} {cell : CellContains word tested}
    (step : DoubledCellExpansion cell expanded) : SameFactorSignature word expanded :=
  signature_of_derives step.derives

def NoNewSingleton (source target : Word Nat) : Prop :=
  ∀ letter, target.toList.count letter = 1 → source.toList.count letter = 1

theorem NoNewSingleton.refl (word : Word Nat) : NoNewSingleton word word := fun _ count => count

theorem NoNewSingleton.trans {source middle target : Word Nat}
    (first : NoNewSingleton source middle) (second : NoNewSingleton middle target) :
    NoNewSingleton source target := fun letter count => first letter (second letter count)

theorem DoubledCellExpansion.noNewSingleton
    {word expanded : Word Nat} {tested : Nat} {cell : CellContains word tested}
    (step : DoubledCellExpansion cell expanded) : NoNewSingleton word expanded := by
  intro letter singleton
  have changeCount := step.count_eq letter
  omega

theorem DoubledCellExpansion.triplicatesCellLetter
    {word expanded : Word Nat} {tested letter : Nat} {cell : CellContains word tested}
    (step : DoubledCellExpansion cell expanded) (inside : letter ∈ cell.cellLetters) :
    3 ≤ expanded.toList.count letter := by
  have sourceMember : letter ∈ word.toList := by
    rw [cell.toList_eq_context]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr inside)))
  have sourcePositive := List.one_le_count_iff.mpr sourceMember
  have copyPositive := List.one_le_count_iff.mpr (cell.mem_expansionCopy_of_mem_cellLetters inside)
  have changeCount := step.count_eq letter
  omega

/-- Pure cell geometry is reused from TWO lower insertions. Their lower
Derives fields are deliberately not used as rank040 proof evidence. -/
theorem DoubledCellExpansion.repeatedWord
    {word expanded : Word Nat} {tested : Nat} {cell : CellContains word tested}
    (step : DoubledCellExpansion cell expanded) (repeated : RepeatedWord word) : RepeatedWord expanded := by
  obtain ⟨middle, firstStep⟩ := cell.exists_contextualCellExpansion
  let secondCell : CellContains middle tested :=
    { y := cell.y
      leadingContext := cell.leadingContext
      p := cell.p
      suffix := cell.expansionCopy ++ cell.suffix
      factorization := by
        rw [firstStep.expanded_toList]
        simp only [CellContains.cellLetters, List.append_assoc, List.cons_append, List.nil_append]
      tested_mem := cell.tested_mem }
  obtain ⟨last, secondStep⟩ := secondCell.exists_contextualCellExpansion
  have same : last = expanded := by
    apply Word.toList_injective
    rw [secondStep.expanded_toList, step.expanded_toList]
    simp only [secondCell, CellContains.cellLetters, CellContains.expansionCopy, List.append_assoc]
  rw [← same]
  exact secondStep.repeatedWord (firstStep.repeatedWord repeated)

theorem DoubledCellExpansion.noSingletonLetters
    {word expanded : Word Nat} {tested : Nat} {cell : CellContains word tested}
    (step : DoubledCellExpansion cell expanded) (none : NoSingletonLetters word) : NoSingletonLetters expanded := by
  intro letter _ singleton
  have previous := step.noNewSingleton letter singleton
  exact none letter (List.count_pos_iff.mp (by omega)) previous

/-- A structural pass over a finite list eliminates its singleton letters.
Previously eliminated letters stay eliminated, so there is no hidden fuel
or mathematical termination assumption. -/
theorem expandPastSingletons (letters : List Nat) (word : Word Nat) (repeated : RepeatedWord word) :
    ∃ target, Derives Rank040.basis word target ∧ RepeatedWord target ∧ NoNewSingleton word target ∧
      ∀ letter, letter ∈ letters → target.toList.count letter ≠ 1 := by
  classical
  induction letters generalizing word with
  | nil => exact ⟨word, Derives.refl _, repeated, NoNewSingleton.refl _,
      fun _ member => False.elim (List.not_mem_nil member)⟩
  | cons tested rest ih =>
      by_cases singleton : word.toList.count tested = 1
      · have member : tested ∈ word.toList := List.count_pos_iff.mp (by omega)
        let cell := repeated tested member
        obtain ⟨expanded, step⟩ := exists_doubledCellExpansion cell
        obtain ⟨target, derived, targetRepeated, noNew, avoids⟩ := ih expanded (step.repeatedWord repeated)
        refine ⟨target, step.derives.trans derived, targetRepeated, step.noNewSingleton.trans noNew, ?_⟩
        intro letter member count
        rcases List.mem_cons.mp member with same | later
        · subst letter
          have oldCount := noNew tested count
          have triplicated := step.triplicatesCellLetter cell.tested_mem
          omega
        · exact avoids letter later count
      · obtain ⟨target, derived, targetRepeated, noNew, avoids⟩ := ih word repeated
        refine ⟨target, derived, targetRepeated, noNew, ?_⟩
        intro letter member count
        rcases List.mem_cons.mp member with same | later
        · subst letter
          exact singleton (noNew tested count)
        · exact avoids letter later count

/-- Every repeated word reaches a no-singleton word while preserving BOTH
actual factor invariants. Odd singletons become at least three, not two. -/
theorem repeatedWord_derives_noSingleton
    (word : Word Nat) (repeated : RepeatedWord word) :
    ∃ target, Derives Rank040.basis word target ∧ SameFactorSignature word target ∧
      NoSingletonLetters target := by
  obtain ⟨target, derived, _, noNew, avoids⟩ := expandPastSingletons (singletonLetters word) word repeated
  refine ⟨target, derived, signature_of_derives derived, ?_⟩
  intro letter _ count
  exact avoids letter ((mem_singletonLetters_iff word letter).mpr (noNew letter count)) count

def cellFactorInverseWitness (factor : CellFactor) : RankInverse factor.word := by
  rcases factor with ⟨boundary, interior⟩
  cases interior with
  | nil => exact ExposureReplay.squareInverseWitness (Word.singleton boundary)
  | cons head tail =>
      exact ExposureReplay.sandwichInverseWitness (Word.singleton boundary) (Word.mk head tail)

def cellProductInverseWitness : (product : CellProduct) → RankInverse product.word
  | .single factor => cellFactorInverseWitness factor
  | .snoc previous factor => (cellProductInverseWitness previous).append (cellFactorInverseWitness factor)

def inverseWitnessPullback {source target : Word Nat} (witness : RankInverse target)
    (derived : Derives Rank040.basis source target) : RankInverse source where
  inverse := witness.inverse
  word_inverse_word :=
    (Derives.appendRight (Derives.appendRight derived witness.inverse) source).trans
      ((Derives.prepend (target ++ witness.inverse) derived).trans
        (witness.word_inverse_word.trans derived.symm))
  inverse_word_inverse :=
    (Derives.appendRight (Derives.prepend witness.inverse derived) witness.inverse).trans
      witness.inverse_word_inverse

private theorem cellProductFromPrefix
    (current : Word Nat) (built : CellProduct) (remainder : List Nat)
    (shape : current.toList = built.word.toList ++ remainder) (none : NoSingletonLetters current) :
    ∃ product : CellProduct, Derives Rank040.basis current product.word := by
  have close : ∀ bound, ∀ remainder : List Nat, remainder.length = bound →
      ∀ current : Word Nat, ∀ built : CellProduct,
        current.toList = built.word.toList ++ remainder → NoSingletonLetters current →
          ∃ product : CellProduct, Derives Rank040.basis current product.word := by
    intro bound
    refine Nat.strongRecOn bound ?_
    intro currentBound smaller remainder lengthEq current built shape none
    cases remainder with
    | nil =>
        have same : current = built.word := Word.toList_injective (by simpa only [List.append_nil] using shape)
        exact ⟨built, by rw [same]; exact Derives.refl _⟩
    | cons tested tail =>
        by_cases later : tested ∈ tail
        · obtain ⟨interior, next, tailShape⟩ := List.mem_iff_append.mp later
          let factor : CellFactor := ⟨tested, interior⟩
          let nextBuilt := CellProduct.snoc built factor
          have nextShape : current.toList = nextBuilt.word.toList ++ next := by
            rw [shape, tailShape]
            simp only [nextBuilt, factor, CellProduct.word, CellFactor.word_toList, Word.toList_append,
              List.append_assoc, List.cons_append, List.nil_append]
          have decrease : next.length < currentBound := by
            rw [← lengthEq, tailShape]
            simp only [List.length_cons, List.length_append]
            omega
          exact smaller next.length decrease next rfl current nextBuilt nextShape none
        · have currentMember : tested ∈ current.toList := by rw [shape]; simp
          have tailCount : tail.count tested = 0 := List.count_eq_zero.mpr later
          have sourceNotSingleton := none tested currentMember
          have prefixPositive : 0 < built.word.toList.count tested := by
            rw [shape, List.count_append] at sourceNotSingleton
            simp only [List.count_cons_self, tailCount] at sourceNotSingleton
            omega
          obtain ⟨left, right, prefixShape⟩ := List.mem_iff_append.mp (List.count_pos_iff.mp prefixPositive)
          let crossing : CellContains current tested :=
            { y := tested
              leadingContext := left
              p := right
              suffix := tail
              factorization := by
                rw [shape, prefixShape]
                simp only [List.append_assoc, List.cons_append]
              tested_mem := by simp }
          obtain ⟨expanded, step⟩ := exists_doubledCellExpansion crossing
          -- TWO inserted copies produce the cell t right t right t.
          let factor : CellFactor := ⟨tested, right ++ tested :: right⟩
          let nextBuilt := CellProduct.snoc built factor
          have nextShape : expanded.toList = nextBuilt.word.toList ++ tail := by
            rw [step.expanded_toList]
            simp only [crossing, nextBuilt, factor, CellContains.cellLetters, CellContains.expansionCopy,
              CellProduct.word, CellFactor.word_toList, Word.toList_append]
            rw [prefixShape]
            simp only [List.append_assoc, List.cons_append, List.nil_append]
          have decrease : tail.length < currentBound := by rw [← lengthEq]; simp
          obtain ⟨product, restDerived⟩ := smaller tail.length decrease tail rfl expanded nextBuilt
            nextShape (step.noSingletonLetters none)
          exact ⟨product, step.derives.trans restDerived⟩
  exact close remainder.length remainder rfl current built shape none

/-- The no-singleton case factors into genuine cells using only doubled
expansions. The unprocessed suffix length strictly decreases at each step. -/
theorem noSingleton_derives_cellProduct (word : Word Nat) (none : NoSingletonLetters word) :
    ∃ product : CellProduct, Derives Rank040.basis word product.word := by
  have headLater : word.head ∈ word.tail := by
    apply Classical.byContradiction
    intro absent
    have tailCount := List.count_eq_zero.mpr absent
    have singleton : word.toList.count word.head = 1 := by simp [Word.toList, tailCount]
    exact none word.head (by simp [Word.toList]) singleton
  obtain ⟨interior, remainder, tailShape⟩ := List.mem_iff_append.mp headLater
  let factor : CellFactor := ⟨word.head, interior⟩
  let built := CellProduct.single factor
  have shape : word.toList = built.word.toList ++ remainder := by
    simp only [built, CellProduct.word, CellFactor.word_toList]
    simp only [factor, Word.toList, tailShape, List.append_assoc, List.cons_append, List.nil_append]
  exact cellProductFromPrefix word built remainder shape none

noncomputable def noSingletonInverseWitness (word : Word Nat) (none : NoSingletonLetters word) :
    RankInverse word :=
  let existence := noSingleton_derives_cellProduct word none
  inverseWitnessPullback (cellProductInverseWitness (Classical.choose existence)) (Classical.choose_spec existence)

/-- EVERY repeated word has an explicit inverse modulo the FROZEN join
basis. This is the actual word-level regularity bridge, not factor inference. -/
noncomputable def repeatedWordInverseWitness (word : Word Nat) (repeated : RepeatedWord word) :
    RankInverse word :=
  let existence := repeatedWord_derives_noSingleton word repeated
  let target := Classical.choose existence
  let properties := Classical.choose_spec existence
  inverseWitnessPullback (noSingletonInverseWitness target properties.2.2) properties.1

theorem repeatedWord_termRegular (word : Word Nat) (repeated : RepeatedWord word) :
    (termSemigroup Rank040.basis).IsRegular (termClass Rank040.basis word) :=
  ⟨termClass Rank040.basis (repeatedWordInverseWitness word repeated).inverse,
    (repeatedWordInverseWitness word repeated).termInverse⟩

/-- OPEN regular-pair comparison. Each regularity premise contains actual
rank040 derivation witnesses, never a semantic regularity stamp. -/
def RegularPairParityLift : Prop :=
  ∀ left right : Word Nat, Nonempty (RankInverse left) → Nonempty (RankInverse right) →
    SameFactorSignature left right → Derives Rank040.basis left right

theorem brandtParityLift_of_regularPairParityLift (owner : RegularPairParityLift) : BrandtParityLift :=
  IsolatedParitySplit.brandtParityLift_of_repeatedPairParityLift
    (fun left right leftRepeated rightRepeated same => owner left right
      ⟨repeatedWordInverseWitness left leftRepeated⟩ ⟨repeatedWordInverseWitness right rightRepeated⟩ same)

theorem brandtParityLift_iff_regularPairParityLift : BrandtParityLift ↔ RegularPairParityLift :=
  ⟨fun owner left right _ _ same => owner (Identity.mk left right) same.brandt same.parity,
    brandtParityLift_of_regularPairParityLift⟩

theorem fixedHeadParityLift_iff_regularPairParityLift :
    RetargetCoverage.FixedHeadParityLift ↔ RegularPairParityLift :=
  RetargetCoverage.brandtParityLift_iff_fixedHeadParityLift.symm.trans
    brandtParityLift_iff_regularPairParityLift

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.RepeatedCellRegularity

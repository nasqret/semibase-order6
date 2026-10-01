import SemigroupBasis.CoRoots.Order6L1RRank1.Gca80a5da838636f5.ContextualFrozen
import SemigroupBasis.CoRoots.Order6L1RRank1.Gca80a5da838636f5.SelectedFactorTables
import SemigroupBasis.CoRoots.S5_1092Normalization
import SemigroupBasis.Generated.BandEmbeddingTransfers
import SemigroupBasis.Generated.S4_73
import SemigroupBasis.Subdirect

/-!
# Frozen-head stratified completeness for Gca

This off-tree module builds an explicit `ContextualFrozenRTC` from the 49
generated frozen paths.  It ports the public regular-band normalization scans
without importing the retired Gca `Primitives`, `Semantics`, `Normalization`,
or `Completeness` modules and without importing any canonical-search layer.

The selected `S4_73` hypothesis is rewritten once to the transparent Edmunds
four-element model.  All subsequent marker evaluations and multiplications
use `Fin 4` and `edmundsFourSeventyThreeMul` directly.

Source-static draft only: Helios elaboration is still required.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gca80a5da838636f5

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots
open SemigroupBasis.CoRoots.Order6L1RRank1

/-! ## Symmetry and one-step constructors -/

/-- Every frozen step may be traversed in the opposite direction. -/
theorem contextualFrozenStep_symm
    {left right : List Nat}
    (step : ContextualFrozenStep left right) :
    ContextualFrozenStep right left := by
  obtain ⟨witness, rfl, rfl⟩ := step
  cases witness with
  | mk rule direction leftContext rightContext =>
      cases direction with
      | forward =>
          exact
            ⟨⟨rule, .reverse, leftContext, rightContext⟩, rfl, rfl⟩
      | reverse =>
          exact
            ⟨⟨rule, .forward, leftContext, rightContext⟩, rfl, rfl⟩

/-- Reverse an exact contextual frozen-path chain. -/
theorem ContextualFrozenRTC.symm
    {left right : List Nat}
    (reachable : ContextualFrozenRTC left right) :
    ContextualFrozenRTC right left := by
  induction reachable with
  | refl letters => exact ContextualFrozenRTC.refl letters
  | cons step rest inductionHypothesis =>
      exact ContextualFrozenRTC.trans inductionHypothesis
        (ContextualFrozenRTC.cons
          (contextualFrozenStep_symm step)
          (ContextualFrozenRTC.refl _))

private def singletonWord (letter : Nat) : Word Nat :=
  Word.singleton letter

private theorem contextualFrozenRTC_of_witness
    (witness : ContextualFrozenWitness) :
    ContextualFrozenRTC witness.source witness.target :=
  ContextualFrozenRTC.cons
    ⟨witness, rfl, rfl⟩ (ContextualFrozenRTC.refl _)

/-! ## Exact three-guard deletion -/

/-- Delete the middle of three equal singleton guards.  The four branches are
exactly frozen paths 00000, 00002, 00004, and 00010. -/
private theorem contextualFrozenRTC_deleteBetweenGuards
    (letter : Nat) (left right : List Nat) :
    ContextualFrozenRTC
      ([letter] ++ left ++ [letter] ++ right ++ [letter])
      ([letter] ++ left ++ right ++ [letter]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          let endpoint := singletonWord letter
          let rule : FrozenPathInstantiation :=
            { index := .path00000
              V0 := endpoint
              V1 := endpoint
              V2 := endpoint
              V3 := endpoint }
          let witness : ContextualFrozenWitness :=
            ⟨rule, .forward, [], []⟩
          simpa [witness, rule, endpoint, singletonWord,
            ContextualFrozenWitness.source,
            ContextualFrozenWitness.target,
            ContextualFrozenWitness.coreSource,
            ContextualFrozenWitness.coreTarget,
            FrozenPathInstantiation.source,
            FrozenPathInstantiation.target,
            Word.singleton, Word.append, Word.toList,
            List.append_assoc] using
              contextualFrozenRTC_of_witness witness
      | cons rightHead rightTail =>
          let endpoint := singletonWord letter
          let rightWord : Word Nat := Word.mk rightHead rightTail
          let rule : FrozenPathInstantiation :=
            { index := .path00002
              V0 := endpoint
              V1 := rightWord
              V2 := endpoint
              V3 := endpoint }
          let witness : ContextualFrozenWitness :=
            ⟨rule, .forward, [], []⟩
          simpa [witness, rule, endpoint, rightWord, singletonWord,
            ContextualFrozenWitness.source,
            ContextualFrozenWitness.target,
            ContextualFrozenWitness.coreSource,
            ContextualFrozenWitness.coreTarget,
            FrozenPathInstantiation.source,
            FrozenPathInstantiation.target,
            Word.singleton, Word.append, Word.toList,
            List.append_assoc] using
              contextualFrozenRTC_of_witness witness
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          let endpoint := singletonWord letter
          let leftWord : Word Nat := Word.mk leftHead leftTail
          let rule : FrozenPathInstantiation :=
            { index := .path00004
              V0 := endpoint
              V1 := leftWord
              V2 := endpoint
              V3 := endpoint }
          let witness : ContextualFrozenWitness :=
            ⟨rule, .forward, [], []⟩
          simpa [witness, rule, endpoint, leftWord, singletonWord,
            ContextualFrozenWitness.source,
            ContextualFrozenWitness.target,
            ContextualFrozenWitness.coreSource,
            ContextualFrozenWitness.coreTarget,
            FrozenPathInstantiation.source,
            FrozenPathInstantiation.target,
            Word.singleton, Word.append, Word.toList,
            List.append_assoc] using
              contextualFrozenRTC_of_witness witness
      | cons rightHead rightTail =>
          let endpoint := singletonWord letter
          let leftWord : Word Nat := Word.mk leftHead leftTail
          let rightWord : Word Nat := Word.mk rightHead rightTail
          let rule : FrozenPathInstantiation :=
            { index := .path00010
              V0 := endpoint
              V1 := leftWord
              V2 := rightWord
              V3 := endpoint }
          let witness : ContextualFrozenWitness :=
            ⟨rule, .forward, [], []⟩
          simpa [witness, rule, endpoint, leftWord, rightWord,
            singletonWord,
            ContextualFrozenWitness.source,
            ContextualFrozenWitness.target,
            ContextualFrozenWitness.coreSource,
            ContextualFrozenWitness.coreTarget,
            FrozenPathInstantiation.source,
            FrozenPathInstantiation.target,
            Word.singleton, Word.append, Word.toList,
            List.append_assoc] using
              contextualFrozenRTC_of_witness witness

private theorem contextualFrozenRTC_deleteWithPrefixAndRightGuard
    (letter : Nat)
    (pref suffix guard : List Nat)
    (prefixHas : letter ∈ pref)
    (guardHas : letter ∈ guard) :
    ContextualFrozenRTC
      ((pref ++ letter :: suffix) ++ guard)
      ((pref ++ suffix) ++ guard) := by
  obtain ⟨prefixBefore, prefixAfter, prefixSplit⟩ :=
    List.mem_iff_append.mp prefixHas
  obtain ⟨guardBefore, guardAfter, guardSplit⟩ :=
    List.mem_iff_append.mp guardHas
  have core :=
    contextualFrozenRTC_deleteBetweenGuards
      letter prefixAfter (suffix ++ guardBefore)
  have contextual :=
    ContextualFrozenRTC.context core prefixBefore guardAfter
  simpa [prefixSplit, guardSplit, List.append_assoc] using contextual

private theorem contextualFrozenRTC_deleteWithLeftAndRightGuard
    (letter : Nat)
    (leftGuard pref suffix : List Nat)
    (leftHas : letter ∈ leftGuard)
    (rightHas : letter ∈ suffix) :
    ContextualFrozenRTC
      ((leftGuard ++ pref) ++ letter :: suffix)
      ((leftGuard ++ pref) ++ suffix) := by
  obtain ⟨leftBefore, leftAfter, leftSplit⟩ :=
    List.mem_iff_append.mp leftHas
  obtain ⟨rightBefore, rightAfter, rightSplit⟩ :=
    List.mem_iff_append.mp rightHas
  have core :=
    contextualFrozenRTC_deleteBetweenGuards
      letter (leftAfter ++ pref) rightBefore
  have contextual :=
    ContextualFrozenRTC.context core leftBefore rightAfter
  simpa [leftSplit, rightSplit, List.append_assoc] using contextual

private theorem contextualFrozenRTC_deleteAllWithGuards
    (letter : Nat)
    (guard : List Nat)
    (guardHas : letter ∈ guard) :
    ∀ (pref middle : List Nat),
      letter ∈ pref →
      ContextualFrozenRTC
        ((pref ++ middle) ++ guard)
        ((pref ++ middle.filter
          (fun selected => decide (selected ≠ letter))) ++ guard)
  | pref, [], _ => by
      simp only [List.filter_nil]
      exact ContextualFrozenRTC.refl _
  | pref, selected :: rest, prefixHas => by
      by_cases equal : selected = letter
      · subst selected
        have deleteCurrent :=
          contextualFrozenRTC_deleteWithPrefixAndRightGuard
            letter pref rest guard prefixHas guardHas
        have deleteRest :=
          contextualFrozenRTC_deleteAllWithGuards
            letter guard guardHas pref rest prefixHas
        simpa [List.append_assoc] using
          ContextualFrozenRTC.trans deleteCurrent deleteRest
      · have extendedHas : letter ∈ pref ++ [selected] :=
          List.mem_append.mpr (Or.inl prefixHas)
        have deleteRest :=
          contextualFrozenRTC_deleteAllWithGuards
            letter guard guardHas (pref ++ [selected]) rest extendedHas
        simpa [equal, List.append_assoc] using deleteRest

/-! ## Explicit first-copy and last-copy scans -/

private theorem contextualFrozenRTC_firstCopyNormalize :
    ∀ (letters guard : List Nat),
      (∀ letter, letter ∈ letters → letter ∈ guard) →
      ContextualFrozenRTC
        (letters ++ guard)
        (firstOccurrenceSequence letters ++ guard)
  | [], guard, _ => by
      simpa [firstOccurrenceSequence] using
        (ContextualFrozenRTC.refl guard)
  | letter :: rest, guard, support => by
      have normalizeRest :=
        contextualFrozenRTC_firstCopyNormalize rest guard
          (fun selected selectedMem =>
            support selected (List.mem_cons_of_mem letter selectedMem))
      have prefixed :=
        ContextualFrozenRTC.context normalizeRest [letter] []
      have prefixedAligned :
          ContextualFrozenRTC
            ([letter] ++ (rest ++ guard))
            ([letter] ++ firstOccurrenceSequence rest ++ guard) := by
        simpa only [List.append_nil, List.append_assoc] using prefixed
      have guardHas : letter ∈ guard := support letter (by simp)
      have deleteDuplicates :=
        contextualFrozenRTC_deleteAllWithGuards
          letter guard guardHas [letter]
            (firstOccurrenceSequence rest) (by simp)
      simpa [firstOccurrenceSequence, List.append_assoc] using
        ContextualFrozenRTC.trans prefixedAligned deleteDuplicates

private theorem contextualFrozenRTC_lastCopyNormalize :
    ∀ (pref letters : List Nat),
      (∀ letter, letter ∈ letters → letter ∈ pref) →
      ContextualFrozenRTC
        (pref ++ letters)
        (pref ++ S5_1092.lastOccurrenceSequence letters)
  | pref, [], _ => by
      simpa [S5_1092.lastOccurrenceSequence] using
        (ContextualFrozenRTC.refl pref)
  | pref, letter :: rest, support => by
      by_cases later : letter ∈ rest
      · have deleteCurrent :=
          contextualFrozenRTC_deleteWithLeftAndRightGuard
            letter pref [] rest (support letter (by simp)) later
        have normalizeRest :=
          contextualFrozenRTC_lastCopyNormalize pref rest
            (fun selected selectedMem =>
              support selected
                (List.mem_cons_of_mem letter selectedMem))
        have deleteCurrent' :
            ContextualFrozenRTC
              (pref ++ letter :: rest) (pref ++ rest) := by
          simpa using deleteCurrent
        simpa [S5_1092.lastOccurrenceSequence, later,
          List.append_assoc] using
            ContextualFrozenRTC.trans deleteCurrent' normalizeRest
      · have extendedSupport :
          ∀ selected, selected ∈ rest →
            selected ∈ pref ++ [letter] :=
          fun selected selectedMem =>
            List.mem_append.mpr
              (Or.inl (support selected
                (List.mem_cons_of_mem letter selectedMem)))
        have normalizeRest :=
          contextualFrozenRTC_lastCopyNormalize
            (pref ++ [letter]) rest extendedSupport
        simpa [S5_1092.lastOccurrenceSequence, later,
          List.append_assoc] using normalizeRest

/-- Path 00001 in reverse duplicates a nonempty block behind a nonempty
protected guard. -/
private theorem contextualFrozenRTC_duplicateProtected
    (guard block : Word Nat) :
    ContextualFrozenRTC
      (guard.toList ++ block.toList)
      (guard.toList ++ block.toList ++ block.toList) := by
  let rule : FrozenPathInstantiation :=
    { index := .path00001
      V0 := guard
      V1 := block
      V2 := guard
      V3 := guard }
  let witness : ContextualFrozenWitness :=
    ⟨rule, .reverse, [], []⟩
  simpa [witness, rule,
    ContextualFrozenWitness.source,
    ContextualFrozenWitness.target,
    ContextualFrozenWitness.coreSource,
    ContextualFrozenWitness.coreTarget,
    FrozenPathInstantiation.source,
    FrozenPathInstantiation.target,
    Word.toList_append, List.append_assoc] using
      contextualFrozenRTC_of_witness witness

/-- Normalize a nonempty block by the regular-band first/last scans beneath a
fixed nonempty guard, using only frozen paths. -/
private theorem contextualFrozenRTC_regularBandNormalAfterGuard
    (guard block : Word Nat) :
    ContextualFrozenRTC
      (guard.toList ++ block.toList)
      (guard.toList ++
        S5_1092.regularBandNormalList block.toList) := by
  have duplicate := contextualFrozenRTC_duplicateProtected guard block
  have normalizeFirst :=
    contextualFrozenRTC_firstCopyNormalize
      block.toList block.toList (fun _ member => member)
  have normalizeLast :=
    contextualFrozenRTC_lastCopyNormalize
      (firstOccurrenceSequence block.toList) block.toList
      (fun selected selectedMem =>
        (mem_firstOccurrenceSequence_iff
          selected block.toList).mpr selectedMem)
  have normalized :=
    ContextualFrozenRTC.trans normalizeFirst normalizeLast
  have protectedRoute :=
    ContextualFrozenRTC.context normalized guard.toList []
  have protectedRouteAligned :
      ContextualFrozenRTC
        (guard.toList ++ block.toList ++ block.toList)
        (guard.toList ++
          (firstOccurrenceSequence block.toList ++
            S5_1092.lastOccurrenceSequence block.toList)) := by
    simpa only [List.append_nil, List.append_assoc] using protectedRoute
  simpa [S5_1092.regularBandNormalList,
    List.append_assoc] using
      ContextualFrozenRTC.trans duplicate protectedRouteAligned

/-! ## Head-stratified endpoint -/

/-- The nonempty endpoint selected by the repeated/simple initial stratum. -/
def frozenHeadEndpoint (word : Word Nat) : Word Nat :=
  if word.head ∈ word.tail then
    Word.mk word.head
      (S5_1092.regularBandNormalList word.toList)
  else
    Word.mk word.head
      (S5_1092.regularBandNormalList word.tail)

/-- Every word reaches its frozen-head endpoint through an explicit chain of
the 49 generated frozen paths. -/
theorem contextualFrozenRTC_frozenHeadEndpoint (word : Word Nat) :
    ContextualFrozenRTC word.toList
      (frozenHeadEndpoint word).toList := by
  cases word with
  | mk head tail =>
      by_cases repeated : head ∈ tail
      · obtain ⟨before, after, tailShape⟩ :=
          List.mem_iff_append.mp repeated
        have insertCore :=
          (contextualFrozenRTC_deleteBetweenGuards
            head [] before).symm
        have insertContext :=
          ContextualFrozenRTC.context insertCore [] after
        have insertGuard :
            ContextualFrozenRTC
              (head :: tail) ([head] ++ (head :: tail)) := by
          simpa [tailShape, List.append_assoc] using insertContext
        have normalizeWhole :=
          contextualFrozenRTC_regularBandNormalAfterGuard
            (Word.singleton head) (Word.mk head tail)
        have combined :=
          ContextualFrozenRTC.trans insertGuard normalizeWhole
        simpa [frozenHeadEndpoint, repeated, Word.toList,
          Word.toList_singleton] using combined
      · cases tail with
        | nil =>
            simpa [frozenHeadEndpoint, repeated,
              S5_1092.regularBandNormalList,
              firstOccurrenceSequence,
              S5_1092.lastOccurrenceSequence,
              Word.toList] using
                (ContextualFrozenRTC.refl [head])
        | cons tailHead tailRest =>
            let tailWord : Word Nat := Word.mk tailHead tailRest
            have normalizeTail :=
              contextualFrozenRTC_regularBandNormalAfterGuard
                (Word.singleton head) tailWord
            simpa [frozenHeadEndpoint, repeated, tailWord,
              Word.toList, Word.toList_singleton] using normalizeTail

/-! ## Transparent selected-factor semantics -/

/-- The embedded `[0,3,2]` copy of the three-element left regular band in the
transparent Edmunds `S4_73` model. -/
private def transparentS4_73FirstOccurrenceEmbedding :
    Embedding leftRegularBandThree.semigroup
      edmundsFourSeventyThree.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨3, by decide⟩ else
        ⟨2, by decide⟩
  injective := by
    intro left right
    revert left right
    decide
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide

private theorem transparentS4_73Valid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy edmundsFourSeventyThree.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList := by
  have lrbValid :
      identity.SatisfiedBy leftRegularBandThree.semigroup :=
    transparentS4_73FirstOccurrenceEmbedding.pullback_identity
      identity valid
  exact firstOccurrenceSequence_eq_of_valid identity lrbValid

private theorem head_eq_of_firstOccurrenceSequence_eq
    {left right : Word Nat}
    (same :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    left.head = right.head := by
  have heads := congrArg List.head? same
  simpa [Word.toList, firstOccurrenceSequence] using heads

/-- Marker into the literal carrier `Fin 4`; no generated-table carrier
occurs below this definition. -/
private def frozenHeadInitialRepeatMarker
    (initial : Nat) : Nat → Fin 4 :=
  fun letter => if letter = initial then ⟨1, by decide⟩ else
    ⟨3, by decide⟩

private theorem frozenHeadMarkerFold_zero (initial : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun value letter =>
            edmundsFourSeventyThreeMul value
              (frozenHeadInitialRepeatMarker initial letter))
          (0 : Fin 4) = 0
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      have step :
          edmundsFourSeventyThreeMul (0 : Fin 4)
              (frozenHeadInitialRepeatMarker initial letter) = 0 := by
        apply Fin.ext
        simp [edmundsFourSeventyThreeMul]
      rw [step]
      exact frozenHeadMarkerFold_zero initial rest

private theorem frozenHeadMarkerFold_one (initial : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun value letter =>
            edmundsFourSeventyThreeMul value
              (frozenHeadInitialRepeatMarker initial letter))
          (1 : Fin 4) =
        if initial ∈ letters then 0 else 1
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      by_cases equal : letter = initial
      · subst letter
        have step :
            edmundsFourSeventyThreeMul (1 : Fin 4)
                (frozenHeadInitialRepeatMarker initial initial) = 0 := by
          apply Fin.ext
          simp [edmundsFourSeventyThreeMul,
            frozenHeadInitialRepeatMarker]
        rw [step, frozenHeadMarkerFold_zero]
        simp
      · have step :
            edmundsFourSeventyThreeMul (1 : Fin 4)
                (frozenHeadInitialRepeatMarker initial letter) = 1 := by
          apply Fin.ext
          simp [edmundsFourSeventyThreeMul,
            frozenHeadInitialRepeatMarker, equal]
        have reversedInequality : initial ≠ letter := by
          intro reversed
          exact equal reversed.symm
        rw [step, frozenHeadMarkerFold_one]
        simp [reversedInequality]

private theorem transparentS4_73_eval_initialRepeatMarker
    (word : Word Nat) :
    edmundsFourSeventyThree.semigroup.eval
        (frozenHeadInitialRepeatMarker word.head) word =
      if word.head ∈ word.tail then (0 : Fin 4) else (1 : Fin 4) := by
  cases word with
  | mk head tail =>
      unfold Semigroup.eval
      change
        tail.foldl
            (fun value letter =>
              edmundsFourSeventyThreeMul value
                (frozenHeadInitialRepeatMarker head letter))
            (frozenHeadInitialRepeatMarker head head) =
          if head ∈ tail then 0 else 1
      have initialValue :
          frozenHeadInitialRepeatMarker head head = (1 : Fin 4) := by
        simp [frozenHeadInitialRepeatMarker]
      rw [initialValue, frozenHeadMarkerFold_one]

private theorem transparentS4_73Valid_initialRepeated_iff
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy edmundsFourSeventyThree.semigroup)
    (heads : identity.lhs.head = identity.rhs.head) :
    (identity.lhs.head ∈ identity.lhs.tail) ↔
      (identity.rhs.head ∈ identity.rhs.tail) := by
  have evaluated :=
    valid (frozenHeadInitialRepeatMarker identity.lhs.head)
  have leftEvaluation :=
    transparentS4_73_eval_initialRepeatMarker identity.lhs
  have rightEvaluation :
      edmundsFourSeventyThree.semigroup.eval
          (frozenHeadInitialRepeatMarker identity.lhs.head)
          identity.rhs =
        if identity.rhs.head ∈ identity.rhs.tail
          then (0 : Fin 4) else (1 : Fin 4) := by
    simpa [heads] using
      transparentS4_73_eval_initialRepeatMarker identity.rhs
  rw [leftEvaluation, rightEvaluation] at evaluated
  by_cases leftRepeated : identity.lhs.head ∈ identity.lhs.tail <;>
    by_cases rightRepeated : identity.rhs.head ∈ identity.rhs.tail <;>
      simp [leftRepeated, rightRepeated] at evaluated ⊢

private theorem s4_116opValid_lastOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy FactorTables.s4_116op.semigroup) :
    S5_1092.lastOccurrenceSequence identity.lhs.toList =
      S5_1092.lastOccurrenceSequence identity.rhs.toList := by
  have oppositeValid :
      identity.SatisfiedBy
        Generated.Catalogue.S4_116.table.semigroup.opposite := by
    simpa only [FactorTables.s4_116op_semigroup] using valid
  have reversedValid :
      identity.reversed.SatisfiedBy
        Generated.Catalogue.S4_116.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed identity
      Generated.Catalogue.S4_116.table.semigroup).mp oppositeValid
  have lrbValid :
      identity.reversed.SatisfiedBy leftRegularBandThree.semigroup :=
    Generated.BandEmbeddingTransfers.S4_116.embedding.pullback_identity
      identity.reversed reversedValid
  have firstReversed :=
    firstOccurrenceSequence_eq_of_valid identity.reversed lrbValid
  have reversedEquality := congrArg List.reverse firstReversed
  simpa [Identity.reversed,
    S5_1092.lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence] using
      reversedEquality

/-! ## Endpoint extensionality from the three factor coordinates -/

private theorem firstOccurrenceSequence_cons_of_not_mem
    (head : Nat) (tail : List Nat) (absent : head ∉ tail) :
    firstOccurrenceSequence (head :: tail) =
      head :: firstOccurrenceSequence tail := by
  rw [firstOccurrenceSequence]
  congr 1
  apply List.filter_eq_self.mpr
  intro selected member
  have selectedInTail : selected ∈ tail :=
    (mem_firstOccurrenceSequence_iff selected tail).mp member
  have different : selected ≠ head := by
    intro equal
    subst selected
    exact absent selectedInTail
  simp [different]

private theorem lastOccurrenceSequence_cons_of_not_mem
    (head : Nat) (tail : List Nat) (absent : head ∉ tail) :
    S5_1092.lastOccurrenceSequence (head :: tail) =
      head :: S5_1092.lastOccurrenceSequence tail := by
  simp [S5_1092.lastOccurrenceSequence, absent]

private theorem frozenHeadEndpoint_eq_of_coordinates
    {left right : Word Nat}
    (firstOccurrences :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (lastOccurrences :
      S5_1092.lastOccurrenceSequence left.toList =
        S5_1092.lastOccurrenceSequence right.toList)
    (initialRepeated :
      (left.head ∈ left.tail) ↔ (right.head ∈ right.tail)) :
    frozenHeadEndpoint left = frozenHeadEndpoint right := by
  have heads : left.head = right.head :=
    head_eq_of_firstOccurrenceSequence_eq firstOccurrences
  by_cases leftRepeated : left.head ∈ left.tail
  · have rightRepeated : right.head ∈ right.tail :=
      initialRepeated.mp leftRepeated
    have normalizedTail :
        S5_1092.regularBandNormalList left.toList =
          S5_1092.regularBandNormalList right.toList := by
      unfold S5_1092.regularBandNormalList
      exact
        (congrArg
          (fun initial : List Nat =>
            initial ++ S5_1092.lastOccurrenceSequence left.toList)
          firstOccurrences).trans
          (congrArg
            (fun final : List Nat =>
              firstOccurrenceSequence right.toList ++ final)
            lastOccurrences)
    have endpointHeads :
        Word.mk left.head
            (S5_1092.regularBandNormalList left.toList) =
          Word.mk right.head
            (S5_1092.regularBandNormalList left.toList) :=
      congrArg
        (fun initial : Nat =>
          Word.mk initial (S5_1092.regularBandNormalList left.toList))
        heads
    have endpointTails :
        Word.mk right.head
            (S5_1092.regularBandNormalList left.toList) =
          Word.mk right.head
            (S5_1092.regularBandNormalList right.toList) :=
      congrArg (Word.mk right.head) normalizedTail
    simpa only [frozenHeadEndpoint, leftRepeated, rightRepeated,
      ite_true, ite_false] using endpointHeads.trans endpointTails
  · have rightSimple : right.head ∉ right.tail := by
      intro repeated
      exact leftRepeated (initialRepeated.mpr repeated)
    have leftFirst :=
      firstOccurrenceSequence_cons_of_not_mem
        left.head left.tail leftRepeated
    have rightFirst :=
      firstOccurrenceSequence_cons_of_not_mem
        right.head right.tail rightSimple
    have firstCons :
        left.head :: firstOccurrenceSequence left.tail =
          right.head :: firstOccurrenceSequence right.tail :=
      leftFirst.symm.trans <| firstOccurrences.trans rightFirst
    have tailFirst :
        firstOccurrenceSequence left.tail =
          firstOccurrenceSequence right.tail := by
      simpa using congrArg List.tail firstCons
    have leftLast :=
      lastOccurrenceSequence_cons_of_not_mem
        left.head left.tail leftRepeated
    have rightLast :=
      lastOccurrenceSequence_cons_of_not_mem
        right.head right.tail rightSimple
    have lastCons :
        left.head :: S5_1092.lastOccurrenceSequence left.tail =
          right.head :: S5_1092.lastOccurrenceSequence right.tail :=
      leftLast.symm.trans <| lastOccurrences.trans rightLast
    have tailLast :
        S5_1092.lastOccurrenceSequence left.tail =
          S5_1092.lastOccurrenceSequence right.tail := by
      simpa using congrArg List.tail lastCons
    have normalizedTail :
        S5_1092.regularBandNormalList left.tail =
          S5_1092.regularBandNormalList right.tail := by
      unfold S5_1092.regularBandNormalList
      exact
        (congrArg
          (fun initial : List Nat =>
            initial ++ S5_1092.lastOccurrenceSequence left.tail)
          tailFirst).trans
          (congrArg
            (fun final : List Nat =>
              firstOccurrenceSequence right.tail ++ final)
            tailLast)
    have endpointHeads :
        Word.mk left.head (S5_1092.regularBandNormalList left.tail) =
          Word.mk right.head (S5_1092.regularBandNormalList left.tail) :=
      congrArg
        (fun initial : Nat =>
          Word.mk initial (S5_1092.regularBandNormalList left.tail))
        heads
    have endpointTails :
        Word.mk right.head (S5_1092.regularBandNormalList left.tail) =
          Word.mk right.head (S5_1092.regularBandNormalList right.tail) :=
      congrArg (Word.mk right.head) normalizedTail
    simpa only [frozenHeadEndpoint, leftRepeated, rightSimple,
      ite_true, ite_false] using endpointHeads.trans endpointTails

/-- The selected factors determine the frozen-head endpoint.  The generated
`S4_73` hypothesis is rewritten to the transparent Edmunds model exactly once
at the entrance to this proof. -/
theorem frozenHeadEndpoint_eq_of_factor_valid
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy FactorTables.s4_116op.semigroup)
    (rightValid :
      identity.SatisfiedBy FactorTables.s4_73.semigroup) :
    frozenHeadEndpoint identity.lhs =
      frozenHeadEndpoint identity.rhs := by
  have rightValidGenerated :
      identity.SatisfiedBy Generated.S4_73.table.semigroup :=
    rightValid
  have rightValidTransparent :
      identity.SatisfiedBy edmundsFourSeventyThree.semigroup := by
    rw [Generated.S4_73.table_eq_catalogue_model]
      at rightValidGenerated
    exact rightValidGenerated
  have firstOccurrences :=
    transparentS4_73Valid_firstOccurrenceSequence_eq
      identity rightValidTransparent
  have heads :=
    head_eq_of_firstOccurrenceSequence_eq firstOccurrences
  have lastOccurrences :=
    s4_116opValid_lastOccurrenceSequence_eq identity leftValid
  have initialRepeated :=
    transparentS4_73Valid_initialRepeated_iff
      identity rightValidTransparent heads
  exact frozenHeadEndpoint_eq_of_coordinates
    firstOccurrences lastOccurrences initialRepeated

/-! ## Unrestricted completeness package -/

theorem derivesOfFactorValidFrozenHead
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy FactorTables.s4_116op.semigroup)
    (rightValid :
      identity.SatisfiedBy FactorTables.s4_73.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have lhsRoute := contextualFrozenRTC_derives
    (contextualFrozenRTC_frozenHeadEndpoint identity.lhs)
  have rhsRoute := contextualFrozenRTC_derives
    (contextualFrozenRTC_frozenHeadEndpoint identity.rhs)
  rw [frozenHeadEndpoint_eq_of_factor_valid
    identity leftValid rightValid] at lhsRoute
  exact lhsRoute.trans rhsRoute.symm

def intersectionBasisFrozenHead :
    IntersectionBasis
      FactorTables.s4_116op.semigroup
      FactorTables.s4_73.semigroup
      basis where
  leftModels := left_models
  rightModels := right_models
  complete := derivesOfFactorValidFrozenHead

end SemigroupBasis.CoRoots.Order6L1RRank1.Gca80a5da838636f5

import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087
import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_353Opposite
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_240Completeness

/-!
# An unrestricted first-order / endpoint-suffix seed for rank 087

The independently complete `S3_16` factor fixes the FULL first-occurrence
sequence.  Independently complete `S5_240` fixes singleton words, globally
unique final variables, and globally simple ordered penultimate pairs.

The exact frozen nine-law presentation replays the complete left-regular-band
calculus behind two final guards.  A relative marker-change lemma preserves
first-occurrence order while changing an already-seen penultimate block.
Together with an explicit terminal-square collapse, this gives canonical
representatives for all four endpoint strata, including simple penultimate
pairs whose final variable has already occurred.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 7000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

universe u v

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- The exact frozen square expansion `xx = xxx`. -/
theorem derivesPowerExpansion (first : Word Nat) :
    Derives basis
      (first ++ first)
      ((first ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first first first)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 03 deletes an initial duplicate before TWO final guards. -/
theorem derivesProtectedHeadContraction
    (first guard₁ guard₂ : Word Nat) :
    Derives basis
      (((first ++ first) ++ guard₁) ++ guard₂)
      ((first ++ guard₁) ++ guard₂) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 2]) (Word.mk 0 [1, 2]) :=
    Derives.fromBasis (e := law03) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first guard₁ guard₂)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 04 converts two returned initial blocks into two second blocks. -/
theorem derivesReturnedSquareTransfer
    (first second : Word Nat) :
    Derives basis
      (((first ++ second) ++ first) ++ first)
      ((first ++ second) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0, 0]) (Word.mk 0 [1, 1]) :=
    Derives.fromBasis (e := law04) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 05 changes a returned initial block into the already-seen
second block while a genuine nonempty final guard remains. -/
theorem derivesGuardedReturnTransfer
    (first second guard : Word Nat) :
    Derives basis
      (((first ++ second) ++ first) ++ guard)
      (((first ++ second) ++ second) ++ guard) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0, 2]) (Word.mk 0 [1, 1, 2]) :=
    Derives.fromBasis (e := law05) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second guard)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The unrestricted terminal square collapse follows from law 05 and the
literal square expansion: `uvuv → uvvv → uvv`. -/
theorem derivesTerminalSquareCollapse
    (first second : Word Nat) :
    Derives basis
      ((first ++ second) ++ (first ++ second))
      ((first ++ second) ++ second) := by
  have transfer :
      Derives basis
        ((first ++ second) ++ (first ++ second))
        (((first ++ second) ++ second) ++ second) := by
    simpa [Word.append_assoc] using
      derivesGuardedReturnTransfer first second second
  have contraction :
      Derives basis
        (((first ++ second) ++ second) ++ second)
        ((first ++ second) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend first (derivesPowerExpansion second).symm
  exact transfer.trans contraction

/-- Complete LRB regularity has the exact two-step protected replay
`xyzw → xyyzw → xyxzw`; ONE final guard would be false. -/
theorem derivesLrbRegularUnderFinalPair
    (first second guard₁ guard₂ : Word Nat) :
    Derives basis
      (((first ++ second) ++ guard₁) ++ guard₂)
      ((((first ++ second) ++ first) ++ guard₁) ++ guard₂) := by
  have firstStep :
      Derives basis
        (((first ++ second) ++ guard₁) ++ guard₂)
        ((((first ++ second) ++ second) ++ guard₁) ++ guard₂) := by
    simpa [Word.append_assoc] using
      Derives.prepend first
        (derivesProtectedHeadContraction second guard₁ guard₂).symm
  have secondStep :
      Derives basis
        ((((first ++ second) ++ second) ++ guard₁) ++ guard₂)
        ((((first ++ second) ++ first) ++ guard₁) ++ guard₂) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesGuardedReturnTransfer first second guard₁).symm guard₂
  exact firstStep.trans secondStep

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp

/-- The complete TWO-law LRB calculus lifts behind any two nonempty final
guards, through every simultaneous substitution and both contexts. -/
theorem liftLeftRegularBandUnderFinalPair
    {left right : Word Nat}
    (derivation : Derives leftRegularBandThreeBasis left right)
    (guard₁ guard₂ : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      ((left.bind substitution ++ guard₁) ++ guard₂)
      ((right.bind substitution ++ guard₁) ++ guard₂) := by
  induction derivation generalizing guard₁ guard₂ substitution with
  | fromBasis member =>
      simp only [leftRegularBandThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change Derives basis
          (((Word.singleton 0).bind substitution ++ guard₁) ++ guard₂)
          (((Word.mk 0 [0]).bind substitution ++ guard₁) ++ guard₂)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          (derivesProtectedHeadContraction
            (substitution 0) guard₁ guard₂).symm
      · change Derives basis
          (((Word.mk 0 [1]).bind substitution ++ guard₁) ++ guard₂)
          (((Word.mk 0 [1, 0]).bind substitution ++ guard₁) ++ guard₂)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesLrbRegularUnderFinalPair
            (substitution 0) (substitution 1) guard₁ guard₂
  | refl => exact Derives.refl _
  | symm _ hypothesis =>
      exact (hypothesis guard₁ guard₂ substitution).symm
  | trans _ _ first second =>
      exact (first guard₁ guard₂ substitution).trans
        (second guard₁ guard₂ substitution)
  | prepend front _ hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (front.bind substitution)
          (hypothesis guard₁ guard₂ substitution)
  | appendRight _ suffix hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        hypothesis (suffix.bind substitution) (guard₁ ++ guard₂)
          substitution
  | subst _ first hypothesis =>
      simpa [bind_bind] using
        hypothesis guard₁ guard₂
          (fun letter => (first letter).bind substitution)

/-- Equal COMPLETE first-occurrence sequences give an unrestricted LRB proof. -/
theorem lrbDerives_of_sameFirstOccurrences
    (left right : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    Derives leftRegularBandThreeBasis left right := by
  have leftNormal := lrbDerivesNormal left
  have rightNormal := lrbDerivesNormal right
  cases normal : firstOccurrenceSequence left.toList with
  | nil =>
      rw [normal] at leftNormal
      exact False.elim leftNormal
  | cons head tail =>
      have rightSequence :
          firstOccurrenceSequence right.toList = head :: tail := by
        simpa [normal] using order.symm
      rw [normal] at leftNormal
      rw [rightSequence] at rightNormal
      exact leftNormal.trans rightNormal.symm

/-- Every equal-first-order pair derives behind two literal final guards. -/
theorem derivesSameFirstOrderUnderFinalPair
    (left right guard₁ guard₂ : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    Derives basis
      ((left ++ guard₁) ++ guard₂)
      ((right ++ guard₁) ++ guard₂) := by
  simpa only [bind_singleton] using
    liftLeftRegularBandUnderFinalPair
      (lrbDerives_of_sameFirstOccurrences left right order)
      guard₁ guard₂ Word.singleton

/-- Appending one already-seen letter preserves the complete first order. -/
theorem firstOccurrenceSequence_append_final
    (final : Nat) :
    ∀ before : List Nat,
      firstOccurrenceSequence (before ++ [final]) =
        if final ∈ before then
          firstOccurrenceSequence before
        else
          firstOccurrenceSequence before ++ [final]
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      have induction := firstOccurrenceSequence_append_final final rest
      by_cases equal : letter = final
      · subst letter
        by_cases present : final ∈ rest <;>
          simp [firstOccurrenceSequence, induction, present,
            List.filter_append]
      · have reverseEqual : final ≠ letter := Ne.symm equal
        by_cases present : final ∈ rest <;>
          simp [firstOccurrenceSequence, induction, reverseEqual,
            present, List.filter_append]

/-- The first-occurrence renderer preserves support exactly. -/
theorem mem_firstOccurrenceSequence_iff
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔ selected ∈ letters
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      by_cases equal : selected = letter
      · subst selected
        simp [firstOccurrenceSequence]
      · have induction := mem_firstOccurrenceSequence_iff selected rest
        simp [firstOccurrenceSequence, induction, equal]

/-- A supported final singleton can be appended in complete LRB theory. -/
theorem lrbAppendSeen
    (stemWord : Word Nat) (selected : Nat)
    (present : selected ∈ stemWord.toList) :
    Derives leftRegularBandThreeBasis
      stemWord (stemWord ++ Word.singleton selected) := by
  apply lrbDerives_of_sameFirstOccurrences
  rw [Word.toList_append, Word.toList_singleton,
    firstOccurrenceSequence_append_final, if_pos present]

/-- Change a seen penultimate BLOCK to another seen block while preserving
the full first-occurrence order and an actual nonempty final guard. -/
theorem derivesChangeSeenPenultimate
    (stemWord old replacement final : Word Nat)
    (oldSeen :
      Derives leftRegularBandThreeBasis stemWord (stemWord ++ old))
    (replacementSeen :
      Derives leftRegularBandThreeBasis stemWord (stemWord ++ replacement)) :
    Derives basis
      ((stemWord ++ old) ++ final)
      ((stemWord ++ replacement) ++ final) := by
  have oldAfterReplacement :
      Derives leftRegularBandThreeBasis
        (stemWord ++ replacement)
        ((stemWord ++ replacement) ++ old) :=
    replacementSeen.symm.trans <|
      oldSeen.trans (Derives.appendRight replacementSeen old)
  have firstStep :
      Derives basis
        ((stemWord ++ old) ++ final)
        (((stemWord ++ replacement) ++ old) ++ final) := by
    simpa only [bind_singleton] using
      liftLeftRegularBandUnderFinalPair
        replacementSeen old final Word.singleton
  have secondStep :
      Derives basis
        (((stemWord ++ replacement) ++ old) ++ final)
        ((((stemWord ++ replacement) ++ old) ++ old) ++ final) := by
    simpa only [bind_singleton] using
      liftLeftRegularBandUnderFinalPair
        oldAfterReplacement old final Word.singleton
  have thirdStep :
      Derives basis
        ((((stemWord ++ replacement) ++ old) ++ old) ++ final)
        ((((stemWord ++ replacement) ++ old) ++ replacement) ++ final) := by
    simpa [Word.append_assoc] using
      Derives.prepend stemWord
        (derivesGuardedReturnTransfer replacement old final).symm
  have fourthStep :
      Derives basis
        ((((stemWord ++ replacement) ++ old) ++ replacement) ++ final)
        ((stemWord ++ replacement) ++ final) := by
    have remove :
        Derives leftRegularBandThreeBasis
          ((stemWord ++ replacement) ++ old) stemWord :=
      (replacementSeen.trans oldAfterReplacement).symm
    simpa only [bind_singleton] using
      liftLeftRegularBandUnderFinalPair
        remove replacement final Word.singleton
  exact firstStep.trans <|
    secondStep.trans <| thirdStep.trans fourthStep

/-- A seen penultimate block before a globally unique final can be replaced
by the entire supported prefix. -/
theorem derivesSeenPenultimateToDoubledPrefix
    (stemWord old final : Word Nat)
    (oldSeen :
      Derives leftRegularBandThreeBasis stemWord (stemWord ++ old)) :
    Derives basis
      ((stemWord ++ old) ++ final)
      ((stemWord ++ stemWord) ++ final) := by
  exact derivesChangeSeenPenultimate stemWord old stemWord final
    oldSeen (lrbDerivesIdempotenceContraction stemWord).symm

/-- When BOTH terminal variables have already occurred, normalize to the
square of the entire first-occurrence prefix without cancelling a guard. -/
theorem derivesSeenTerminalPairToPrefixSquare
    (stemWord old final : Word Nat)
    (oldSeen :
      Derives leftRegularBandThreeBasis stemWord (stemWord ++ old))
    (finalSeen :
      Derives leftRegularBandThreeBasis stemWord (stemWord ++ final)) :
    Derives basis
      ((stemWord ++ old) ++ final)
      (stemWord ++ stemWord) := by
  have switch :=
    derivesChangeSeenPenultimate stemWord old final final oldSeen finalSeen
  have expand :
      Derives basis
        ((stemWord ++ final) ++ final)
        (((stemWord ++ final) ++ stemWord) ++ stemWord) :=
    (derivesReturnedSquareTransfer stemWord final).symm
  have remove :
      Derives basis
        (((stemWord ++ final) ++ stemWord) ++ stemWord)
        ((stemWord ++ stemWord) ++ stemWord) := by
    simpa only [bind_singleton] using
      liftLeftRegularBandUnderFinalPair
        finalSeen.symm stemWord stemWord Word.singleton
  exact switch.trans <|
    expand.trans <|
      remove.trans (derivesPowerExpansion stemWord).symm

/-- Explicit terminal-pair rendering is split back into the identical stem
and ordered endpoint variables. -/
theorem terminalSplit_wordOfTerminalPair
    (stem : List Nat) (penultimate final : Nat) :
    terminalSplit
        (SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
          stem penultimate final) =
      .pair stem penultimate final := by
  simpa [SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair,
    TerminalSplit.renderWord] using
    terminalSplit_renderWord_inverse
      (.pair stem penultimate final)

/-- Retain the first occurrence of every stem variable while keeping BOTH
actual final variables untouched.  Empty stems remain literal. -/
theorem derivesStemFirstOccurrenceNormal
    (stem : List Nat) (penultimate final : Nat) :
    Derives basis
      (SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
        stem penultimate final)
      (SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
        (firstOccurrenceSequence stem) penultimate final) := by
  cases stem with
  | nil =>
      exact Derives.refl _
  | cons first rest =>
      let initialWord : Word Nat := ⟨first, rest⟩
      let normalWord : Word Nat :=
        ⟨first,
          (firstOccurrenceSequence rest).filter
            (fun letter => decide (letter ≠ first))⟩
      have lower :
          Derives leftRegularBandThreeBasis
            initialWord normalWord := by
        simpa [initialWord, normalWord, Word.toList,
          firstOccurrenceSequence] using
          lrbDerivesNormal initialWord
      have sourceShape :
          SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
            (first :: rest) penultimate final =
            ((initialWord ++ Word.singleton penultimate) ++
              Word.singleton final) := by
        apply Word.toList_injective
        rw [SemigroupBasis.CoRoots.S5_240.toList_wordOfTerminalPair,
          Word.toList_append, Word.toList_append]
        simp [initialWord, Word.toList, List.append_assoc]
      have targetShape :
          SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
            (firstOccurrenceSequence (first :: rest))
            penultimate final =
            ((normalWord ++ Word.singleton penultimate) ++
              Word.singleton final) := by
        apply Word.toList_injective
        rw [SemigroupBasis.CoRoots.S5_240.toList_wordOfTerminalPair,
          Word.toList_append, Word.toList_append]
        simp [normalWord, firstOccurrenceSequence,
          Word.toList, List.append_assoc]
      rw [sourceShape, targetShape]
      simpa only [bind_singleton] using
        liftLeftRegularBandUnderFinalPair lower
          (Word.singleton penultimate)
          (Word.singleton final) Word.singleton

/-- Four genuine endpoint strata, determined solely by full first order and
the independent complete `S5_240` endpoint-suffix signature. -/
noncomputable def canonicalList (word : Word Nat) : List Nat := by
  classical
  let order := firstOccurrenceSequence word.toList
  exact
    match terminalSplit word with
    | .singleton _ => order
    | .pair _ penultimate final =>
        if SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair
            word penultimate final then
          if UniqueFinal word final then
            order
          else
            order ++ [final]
        else if UniqueFinal word final then
          order.dropLast ++ order.dropLast ++ [final]
        else
          order ++ order

/-- The canonical renderer is independent of the chosen endpoint
decomposition whenever BOTH genuine factor signatures agree. -/
theorem canonicalList_eq_of_invariants
    (left right : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (signature :
      SemigroupBasis.CoRoots.S5_240.SameEndpointSuffixSignature
        left right) :
    canonicalList left = canonicalList right := by
  classical
  cases leftSplit : terminalSplit left with
  | singleton leftFinal =>
      cases rightSplit : terminalSplit right with
      | singleton rightFinal =>
          simpa [canonicalList, leftSplit, rightSplit] using order
      | pair rightStem rightPenultimate rightFinal =>
          have singleton : IsSingletonWord left := by
            simp [IsSingletonWord, leftSplit]
          have impossible := signature.singleton.mp singleton
          simp [IsSingletonWord, rightSplit] at impossible
  | pair leftStem leftPenultimate leftFinal =>
      cases rightSplit : terminalSplit right with
      | singleton rightFinal =>
          have singleton : IsSingletonWord right := by
            simp [IsSingletonWord, rightSplit]
          have impossible := signature.singleton.mpr singleton
          simp [IsSingletonWord, leftSplit] at impossible
      | pair rightStem rightPenultimate rightFinal =>
          by_cases leftSimple :
              SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair
                left leftPenultimate leftFinal
          · have rightSimple :=
              (signature.simplePenultimatePair
                leftPenultimate leftFinal).mp leftSimple
            have rightParts :
                rightPenultimate = leftPenultimate ∧
                  rightFinal = leftFinal ∧
                    leftPenultimate ∉ rightStem ∧
                    leftFinal ≠ leftPenultimate := by
              simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
                rightSplit] using rightSimple
            have penultimateEq := rightParts.1
            have finalEq := rightParts.2.1
            subst rightPenultimate
            subst rightFinal
            by_cases unique : UniqueFinal left leftFinal
            · have uniqueRight :=
                (signature.uniqueFinal leftFinal).mp unique
              simp [canonicalList, leftSplit, rightSplit,
                leftSimple, rightSimple, unique, uniqueRight, order]
            · have uniqueRight : ¬ UniqueFinal right leftFinal := by
                intro present
                exact unique
                  ((signature.uniqueFinal leftFinal).mpr present)
              simp [canonicalList, leftSplit, rightSplit,
                leftSimple, rightSimple, unique, uniqueRight, order]
          · have rightNotSimple :
                ¬ SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair
                  right rightPenultimate rightFinal := by
              intro rightSimple
              have leftSpecific :=
                (signature.simplePenultimatePair
                  rightPenultimate rightFinal).mpr rightSimple
              have leftParts :
                  leftPenultimate = rightPenultimate ∧
                    leftFinal = rightFinal ∧
                      rightPenultimate ∉ leftStem ∧
                      rightFinal ≠ rightPenultimate := by
                simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
                  leftSplit] using leftSpecific
              have actual :
                  SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair
                    left leftPenultimate leftFinal := by
                simpa [leftParts.1, leftParts.2.1] using leftSpecific
              exact leftSimple actual
            by_cases uniqueLeft : UniqueFinal left leftFinal
            · have rightUnique :=
                (signature.uniqueFinal leftFinal).mp uniqueLeft
              have rightFinalEq : rightFinal = leftFinal := by
                have data :
                    rightFinal = leftFinal ∧
                      rightFinal ≠ rightPenultimate ∧
                      rightFinal ∉ rightStem := by
                  simpa [UniqueFinal, rightSplit] using rightUnique
                exact data.1
              subst rightFinal
              simp [canonicalList, leftSplit, rightSplit,
                leftSimple, rightNotSimple, uniqueLeft, rightUnique,
                order]
            · have uniqueRight : ¬ UniqueFinal right rightFinal := by
                intro present
                have leftSpecific :=
                  (signature.uniqueFinal rightFinal).mpr present
                have leftFinalEq : leftFinal = rightFinal := by
                  have data :
                      leftFinal = rightFinal ∧
                        leftFinal ≠ leftPenultimate ∧
                        leftFinal ∉ leftStem := by
                    simpa [UniqueFinal, leftSplit] using leftSpecific
                  exact data.1
                subst rightFinal
                exact uniqueLeft leftSpecific
              simp [canonicalList, leftSplit, rightSplit,
                leftSimple, rightNotSimple, uniqueLeft, uniqueRight,
                order]

/-- Concrete decidable form of the four-stratum canonical renderer. -/
theorem canonicalList_terminalPair
    (stem : List Nat) (penultimate final : Nat) :
    canonicalList
        (SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
          stem penultimate final) =
      let order := firstOccurrenceSequence (stem ++ [penultimate, final])
      if penultimate ∉ stem ∧ final ≠ penultimate then
        if final ≠ penultimate ∧ final ∉ stem then
          order
        else
          order ++ [final]
      else if final ≠ penultimate ∧ final ∉ stem then
        order.dropLast ++ order.dropLast ++ [final]
      else
        order ++ order := by
  classical
  simp [canonicalList, terminalSplit_wordOfTerminalPair,
    SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
    UniqueFinal,
    SemigroupBasis.CoRoots.S5_240.toList_wordOfTerminalPair]

/-- Appending a genuine last letter and dropping it recovers the whole stem. -/
theorem dropLast_append_singleton
    (letters : List Nat) (final : Nat) :
    (letters ++ [final]).dropLast = letters := by
  simp

/-- Every nonempty word reaches the canonical renderer.  The proof treats
singleton, globally simple terminal pair, unique-final repeated marker,
repeated seen final, and genuinely new terminal doubletons separately. -/
theorem derivesToCanonical
    (word : Word Nat) :
    ∃ normal : Word Nat,
      normal.toList = canonicalList word ∧
        Derives basis word normal := by
  classical
  cases split : terminalSplit word with
  | singleton final =>
      have rendered := terminalSplit_renderWord word
      rw [split] at rendered
      have shape : word = Word.singleton final := by
        simpa [TerminalSplit.renderWord] using rendered.symm
      rw [shape]
      refine ⟨Word.singleton final, ?_, Derives.refl _⟩
      have singletonSplit :
          terminalSplit (Word.singleton final) = .singleton final := by
        rfl
      simp [canonicalList, singletonSplit,
        Word.toList, firstOccurrenceSequence]
  | pair stem penultimate final =>
      have rendered := terminalSplit_renderWord word
      rw [split] at rendered
      have shape :
          word = SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
            stem penultimate final := by
        simpa [TerminalSplit.renderWord,
          SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair] using
          rendered.symm
      rw [shape]
      cases stem with
      | nil =>
          by_cases equal : final = penultimate
          · subst final
            refine ⟨SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
              [] penultimate penultimate, ?_, Derives.refl _⟩
            rw [canonicalList_terminalPair]
            simp [SemigroupBasis.CoRoots.S5_240.toList_wordOfTerminalPair,
              firstOccurrenceSequence]
          · refine ⟨SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
              [] penultimate final, ?_, Derives.refl _⟩
            rw [canonicalList_terminalPair]
            simp [SemigroupBasis.CoRoots.S5_240.toList_wordOfTerminalPair,
              firstOccurrenceSequence, equal]
      | cons head rest =>
          let originalStem : List Nat := head :: rest
          let normalStem : List Nat :=
            firstOccurrenceSequence originalStem
          let stemWord : Word Nat :=
            ⟨head,
              (firstOccurrenceSequence rest).filter
                (fun letter => decide (letter ≠ head))⟩
          have stemWordList : stemWord.toList = normalStem := by
            simp [stemWord, normalStem, originalStem,
              Word.toList, firstOccurrenceSequence]
          have normalized :=
            derivesStemFirstOccurrenceNormal
              originalStem penultimate final
          have normalizedShape :
              SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
                  normalStem penultimate final =
                ((stemWord ++ Word.singleton penultimate) ++
                  Word.singleton final) := by
            apply Word.toList_injective
            rw [SemigroupBasis.CoRoots.S5_240.toList_wordOfTerminalPair,
              Word.toList_append, Word.toList_append, stemWordList]
            simp [List.append_assoc]
          have penultimateMembership :
              penultimate ∈ normalStem ↔
                penultimate ∈ originalStem := by
            exact mem_firstOccurrenceSequence_iff
              penultimate originalStem
          have finalMembership :
              final ∈ normalStem ↔ final ∈ originalStem := by
            exact mem_firstOccurrenceSequence_iff
              final originalStem
          by_cases oldSeenOriginal : penultimate ∈ originalStem
          · have oldSeenNormal : penultimate ∈ normalStem :=
              penultimateMembership.mpr oldSeenOriginal
            have oldSeen :
                Derives leftRegularBandThreeBasis
                  stemWord
                  (stemWord ++ Word.singleton penultimate) :=
              lrbAppendSeen stemWord penultimate
                (by simpa [stemWordList] using oldSeenNormal)
            by_cases finalSeenOriginal : final ∈ originalStem
            · have finalSeenNormal : final ∈ normalStem :=
                finalMembership.mpr finalSeenOriginal
              have finalSeen :
                  Derives leftRegularBandThreeBasis
                    stemWord (stemWord ++ Word.singleton final) :=
                lrbAppendSeen stemWord final
                  (by simpa [stemWordList] using finalSeenNormal)
              have fullOrder :
                  firstOccurrenceSequence
                    (originalStem ++ [penultimate, final]) =
                    normalStem := by
                rw [show
                  originalStem ++ [penultimate, final] =
                    (originalStem ++ [penultimate]) ++ [final] by
                      simp [List.append_assoc]]
                rw [firstOccurrenceSequence_append_final,
                  if_pos (by simp [finalSeenOriginal]),
                  firstOccurrenceSequence_append_final,
                  if_pos oldSeenOriginal]
              have canonical :
                  canonicalList
                      (SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
                        originalStem penultimate final) =
                    normalStem ++ normalStem := by
                rw [canonicalList_terminalPair, fullOrder]
                simp [oldSeenOriginal, finalSeenOriginal]
              refine ⟨stemWord ++ stemWord, ?_, ?_⟩
              · rw [canonical, Word.toList_append, stemWordList]
              · have finalStep :=
                  derivesSeenTerminalPairToPrefixSquare
                    stemWord (Word.singleton penultimate)
                    (Word.singleton final) oldSeen finalSeen
                exact normalized.trans <| by
                  rw [normalizedShape]
                  exact finalStep
            · have different : final ≠ penultimate := by
                intro equal
                subst final
                exact finalSeenOriginal oldSeenOriginal
              have fullOrder :
                  firstOccurrenceSequence
                    (originalStem ++ [penultimate, final]) =
                    normalStem ++ [final] := by
                rw [show
                  originalStem ++ [penultimate, final] =
                    (originalStem ++ [penultimate]) ++ [final] by
                      simp [List.append_assoc]]
                rw [firstOccurrenceSequence_append_final,
                  if_neg (by simp [finalSeenOriginal, different]),
                  firstOccurrenceSequence_append_final,
                  if_pos oldSeenOriginal]
              have canonical :
                  canonicalList
                      (SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
                        originalStem penultimate final) =
                    (normalStem ++ normalStem) ++ [final] := by
                rw [canonicalList_terminalPair, fullOrder]
                simp [oldSeenOriginal, finalSeenOriginal, different,
                  List.append_assoc]
              refine ⟨(stemWord ++ stemWord) ++ Word.singleton final,
                ?_, ?_⟩
              · rw [canonical, Word.toList_append,
                    Word.toList_append, stemWordList]
                simp [List.append_assoc]
              · have finalStep :=
                  derivesSeenPenultimateToDoubledPrefix
                    stemWord (Word.singleton penultimate)
                    (Word.singleton final) oldSeen
                exact normalized.trans <| by
                  rw [normalizedShape]
                  exact finalStep
          · by_cases equal : final = penultimate
            · subst final
              have fullOrder :
                  firstOccurrenceSequence
                    (originalStem ++ [penultimate, penultimate]) =
                    normalStem ++ [penultimate] := by
                rw [show
                  originalStem ++ [penultimate, penultimate] =
                    (originalStem ++ [penultimate]) ++ [penultimate] by
                      simp [List.append_assoc]]
                rw [firstOccurrenceSequence_append_final,
                  if_pos (by simp),
                  firstOccurrenceSequence_append_final,
                  if_neg oldSeenOriginal]
              have canonical :
                  canonicalList
                      (SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
                        originalStem penultimate penultimate) =
                    (normalStem ++ [penultimate]) ++
                      (normalStem ++ [penultimate]) := by
                rw [canonicalList_terminalPair, fullOrder]
                simp [oldSeenOriginal]
              let extended := stemWord ++ Word.singleton penultimate
              refine ⟨extended ++ extended, ?_, ?_⟩
              · rw [canonical, Word.toList_append]
                simp [extended, Word.toList_append, stemWordList]
              · have finalStep :=
                  (derivesTerminalSquareCollapse
                    stemWord (Word.singleton penultimate)).symm
                exact normalized.trans <| by
                  rw [normalizedShape]
                  simpa [extended, Word.append_assoc] using finalStep
            · by_cases finalSeenOriginal : final ∈ originalStem
              · have fullOrder :
                    firstOccurrenceSequence
                      (originalStem ++ [penultimate, final]) =
                      normalStem ++ [penultimate] := by
                  rw [show
                    originalStem ++ [penultimate, final] =
                      (originalStem ++ [penultimate]) ++ [final] by
                        simp [List.append_assoc]]
                  rw [firstOccurrenceSequence_append_final,
                    if_pos (by simp [finalSeenOriginal]),
                    firstOccurrenceSequence_append_final,
                    if_neg oldSeenOriginal]
                have canonical :
                    canonicalList
                        (SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
                          originalStem penultimate final) =
                      (normalStem ++ [penultimate]) ++ [final] := by
                  rw [canonicalList_terminalPair, fullOrder]
                  simp [oldSeenOriginal, finalSeenOriginal, equal]
                refine ⟨SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
                  normalStem penultimate final, ?_, normalized⟩
                rw [canonical,
                  SemigroupBasis.CoRoots.S5_240.toList_wordOfTerminalPair]
                simp [List.append_assoc]
              · have fullOrder :
                    firstOccurrenceSequence
                      (originalStem ++ [penultimate, final]) =
                      (normalStem ++ [penultimate]) ++ [final] := by
                  rw [show
                    originalStem ++ [penultimate, final] =
                      (originalStem ++ [penultimate]) ++ [final] by
                        simp [List.append_assoc]]
                  rw [firstOccurrenceSequence_append_final,
                    if_neg (by simp [finalSeenOriginal, equal]),
                    firstOccurrenceSequence_append_final,
                    if_neg oldSeenOriginal]
                have canonical :
                    canonicalList
                        (SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
                          originalStem penultimate final) =
                      (normalStem ++ [penultimate]) ++ [final] := by
                  rw [canonicalList_terminalPair, fullOrder]
                  simp [oldSeenOriginal, finalSeenOriginal, equal]
                refine ⟨SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
                  normalStem penultimate final, ?_, normalized⟩
                rw [canonical,
                  SemigroupBasis.CoRoots.S5_240.toList_wordOfTerminalPair]
                simp [List.append_assoc]

/-- Exact unrestricted derivational completeness from the INDEPENDENT full
first-occurrence and endpoint-suffix signatures. -/
theorem derives_of_signatures
    (left right : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (signature :
      SemigroupBasis.CoRoots.S5_240.SameEndpointSuffixSignature
        left right) :
    Derives basis left right := by
  obtain ⟨leftNormal, leftList, leftDerivation⟩ :=
    derivesToCanonical left
  obtain ⟨rightNormal, rightList, rightDerivation⟩ :=
    derivesToCanonical right
  have sameCanonical :=
    canonicalList_eq_of_invariants left right order signature
  have normalEqual : leftNormal = rightNormal := by
    apply Word.toList_injective
    exact leftList.trans (sameCanonical.trans rightList.symm)
  exact leftDerivation.trans <| by
    rw [normalEqual]
    exact rightDerivation.symm

/-- The independently certified left and right ACTUAL factors supply every
premise of the unrestricted canonical proof. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have order :=
    SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank018.Seed.firstOccurrences_of_leftValid
      identity leftValid
  have actualRight :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup := by
    simpa [rightTable] using rightValid
  have signature :=
    SemigroupBasis.CoRoots.S5_240.valid_signature
      identity actualRight
  exact derives_of_signatures identity.lhs identity.rhs order signature

/-- Exact frozen nine-law intersection assembled AFTER unrestricted proof. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Certified reusable rank-087 family seed; no premise is left conditional. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- The staged rank-087 representative class is proved unconditionally. -/
theorem s6_6171_representative_basis :
    BasisFor S6_6171.table.semigroup basis :=
  S6_6171.representative_basis_of_normalizer normalizer

/-- Its opposite orientation uses the exact reversed frozen presentation. -/
theorem s6_6171_opposite_basis :
    BasisFor S6_6171.table.semigroup.opposite (reversedBasis basis) :=
  S6_6171.opposite_basis_of_normalizer normalizer

/-- Reviewed shared transport retains explicit displayed-law derivations and
independent unrestricted validity implications for BOTH target factors. -/
noncomputable def transportedNormalizer
    {A : Type u} {B : Type v}
    {targetLeft : Semigroup A} {targetRight : Semigroup B}
    {targetBasis : List (Identity Nat)}
    (lawDerivations :
      ∀ law : Identity Nat,
        law ∈ basis → Derives targetBasis law.lhs law.rhs)
    (leftTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetLeft →
          identity.SatisfiedBy leftTable.semigroup)
    (rightTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetRight →
          identity.SatisfiedBy rightTable.semigroup) :
    IntersectionNormalizer targetLeft targetRight targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer lawDerivations leftTheory rightTheory

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed

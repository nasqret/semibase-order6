import SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469.Basis
import SemigroupBasis.CoRoots.S5_1092Normalization
import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.Generated.BandEmbeddingTransfers
import SemigroupBasis.Generated.S4_64

/-!
# Joint semantics for L1R group `43fb00e0b3bdd469`

The selected `S4_64` factor fixes its duplicate-free open-or-closed key.
Removing the final marker from that key leaves the first-occurrence sequence
of the prefix before the original final letter.  The selected opposite
`S4_116` factor fixes the whole-word last-occurrence sequence.  Those two
lists are exactly the data consumed by the unrestricted normalizer.
-/

namespace SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots
open SemigroupBasis.CoRoots.Order6L1RRank1

/-! ## A proof-oriented `S4_64` normal form -/

/-- The first-occurrence key before the final letter.  The singleton
convention has an empty prefix. -/
def prefixFirstOccurrences (word : Word Nat) : List Nat :=
  firstOccurrenceSequence (splitPrefixFinal word).1

/-- The public Edmunds normal form, expressed using the repository's
prefix/final split.  This definition is proof-oriented; the Layer-A
shortlex canonicalizer remains independent. -/
def s4_64ProofNormal (word : Word Nat) : Word Nat :=
  match (splitPrefixFinal word).1 with
  | [] => word
  | first :: rest =>
      match firstOccurrenceSequence (first :: rest) with
      | [] => word
      | initial :: remaining =>
          edmundsFourSixtyFourLongNormal
            initial remaining (splitPrefixFinal word).2

private theorem edmundsFourSixtyFourOpenSingleton_eq (letter : Nat) :
    Word.singleton letter =
      edmundsFourSixtyFourNormalWord letter [] false := by
  have singletonList :
      (Word.singleton letter).toList = [letter] := by
    rfl
  have normalList :
      (edmundsFourSixtyFourNormalWord letter [] false).toList =
        [letter] := by
    rfl
  have representedEquality :
      (Word.singleton letter).toList =
        (edmundsFourSixtyFourNormalWord letter [] false).toList :=
    singletonList.trans normalList.symm
  exact Word.toList_injective representedEquality

private theorem edmundsFourSixtyFourLongNormal_toList
    (initial : Nat) (remaining : List Nat) (final : Nat) :
    (edmundsFourSixtyFourLongNormal initial remaining final).toList =
      if final ∈ initial :: remaining then
        initial :: (remaining ++ [initial])
      else
        initial :: (remaining ++ [final]) := by
  by_cases finalMem : final ∈ initial :: remaining
  · have selectedWord :
        edmundsFourSixtyFourLongNormal initial remaining final =
          Word.mk initial (remaining ++ [initial]) := by
      exact if_pos finalMem
    have representedWord :
        (edmundsFourSixtyFourLongNormal initial remaining final).toList =
          (Word.mk initial (remaining ++ [initial])).toList :=
      congrArg Word.toList selectedWord
    have representedList :
        (Word.mk initial (remaining ++ [initial])).toList =
          initial :: (remaining ++ [initial]) := by
      rfl
    have leftBranch :
        (edmundsFourSixtyFourLongNormal initial remaining final).toList =
          initial :: (remaining ++ [initial]) :=
      representedWord.trans representedList
    have rightBranch :
        (if final ∈ initial :: remaining then
            initial :: (remaining ++ [initial])
          else
            initial :: (remaining ++ [final])) =
          initial :: (remaining ++ [initial]) :=
      if_pos finalMem
    exact leftBranch.trans rightBranch.symm
  · have selectedWord :
        edmundsFourSixtyFourLongNormal initial remaining final =
          Word.mk initial (remaining ++ [final]) := by
      exact if_neg finalMem
    have representedWord :
        (edmundsFourSixtyFourLongNormal initial remaining final).toList =
          (Word.mk initial (remaining ++ [final])).toList :=
      congrArg Word.toList selectedWord
    have representedList :
        (Word.mk initial (remaining ++ [final])).toList =
          initial :: (remaining ++ [final]) := by
      rfl
    have leftBranch :
        (edmundsFourSixtyFourLongNormal initial remaining final).toList =
          initial :: (remaining ++ [final]) :=
      representedWord.trans representedList
    have rightBranch :
        (if final ∈ initial :: remaining then
            initial :: (remaining ++ [initial])
          else
            initial :: (remaining ++ [final])) =
          initial :: (remaining ++ [final]) :=
      if_neg finalMem
    exact leftBranch.trans rightBranch.symm

private theorem dropLast_cons_append_singleton
    (head : Nat) (tail : List Nat) (final : Nat) :
    (head :: (tail ++ [final])).dropLast = head :: tail := by
  induction tail generalizing head with
  | nil => rfl
  | cons next rest induction =>
      have representedSource :
          (head :: ((next :: rest) ++ [final])).dropLast =
            head :: (next :: (rest ++ [final])).dropLast := by
        rfl
      have representedTarget :
          head :: (next :: (rest ++ [final])).dropLast =
            head :: next :: rest :=
        congrArg (List.cons head) (induction (head := next))
      exact representedSource.trans representedTarget

private theorem edmundsFourSixtyFourLongNormal_dropLast
    (initial : Nat) (remaining : List Nat) (final : Nat) :
    (edmundsFourSixtyFourLongNormal initial remaining final).toList.dropLast =
      initial :: remaining := by
  have representedNormal :
      (edmundsFourSixtyFourLongNormal initial remaining final).toList =
        if final ∈ initial :: remaining then
          initial :: (remaining ++ [initial])
        else
          initial :: (remaining ++ [final]) :=
    edmundsFourSixtyFourLongNormal_toList initial remaining final
  have representedDropLast :
      (edmundsFourSixtyFourLongNormal initial remaining final).toList.dropLast =
        (if final ∈ initial :: remaining then
            initial :: (remaining ++ [initial])
          else
            initial :: (remaining ++ [final])).dropLast :=
    congrArg List.dropLast representedNormal
  by_cases finalMem : final ∈ initial :: remaining
  · have selectedBranch :
        (if final ∈ initial :: remaining then
            initial :: (remaining ++ [initial])
          else
            initial :: (remaining ++ [final])).dropLast =
          (initial :: (remaining ++ [initial])).dropLast :=
      congrArg List.dropLast (if_pos finalMem)
    have branchStep :
        (edmundsFourSixtyFourLongNormal initial remaining final).toList.dropLast =
          (initial :: (remaining ++ [initial])).dropLast :=
      representedDropLast.trans selectedBranch
    exact branchStep.trans
      (dropLast_cons_append_singleton initial remaining initial)
  · have selectedBranch :
        (if final ∈ initial :: remaining then
            initial :: (remaining ++ [initial])
          else
            initial :: (remaining ++ [final])).dropLast =
          (initial :: (remaining ++ [final])).dropLast :=
      congrArg List.dropLast (if_neg finalMem)
    have branchStep :
        (edmundsFourSixtyFourLongNormal initial remaining final).toList.dropLast =
          (initial :: (remaining ++ [final])).dropLast :=
      representedDropLast.trans selectedBranch
    exact branchStep.trans
      (dropLast_cons_append_singleton initial remaining final)

/-- Every word derives to the proof-oriented `S4_64` normal form. -/
theorem derivesS4_64ProofNormal (word : Word Nat) :
    Derives edmundsFourSixtyFourBasis word (s4_64ProofNormal word) := by
  let split := splitPrefixFinal word
  have splitRepresentation : split = splitPrefixFinal word := by
    rfl
  have splitPrefixBridge : split.1 = (splitPrefixFinal word).1 :=
    congrArg Prod.fst splitRepresentation
  have splitFinalBridge : split.2 = (splitPrefixFinal word).2 :=
    congrArg Prod.snd splitRepresentation
  have baseReconstruct :
      wordOfPrefixFinal (splitPrefixFinal word).1
          (splitPrefixFinal word).2 = word :=
    wordOfPrefixFinal_split word
  have reconstructAtSplit :
      wordOfPrefixFinal split.1 split.2 =
        wordOfPrefixFinal (splitPrefixFinal word).1
          (splitPrefixFinal word).2 :=
    congrArg
      (fun current : List Nat × Nat =>
        wordOfPrefixFinal current.1 current.2)
      splitRepresentation
  have reconstruct :
      wordOfPrefixFinal split.1 split.2 = word :=
    reconstructAtSplit.trans baseReconstruct
  let proofNormalAtPrefix : List Nat → Word Nat := fun prefixWord =>
    match prefixWord with
    | [] => word
    | first :: rest =>
        match firstOccurrenceSequence (first :: rest) with
        | [] => word
        | initial :: remaining =>
            edmundsFourSixtyFourLongNormal initial remaining
              (splitPrefixFinal word).2
  have foldedNormal :
      s4_64ProofNormal word =
        proofNormalAtPrefix (splitPrefixFinal word).1 := by
    rfl
  cases prefixEq : split.1 with
  | nil =>
      have actualPrefix : (splitPrefixFinal word).1 = [] :=
        splitPrefixBridge.symm.trans prefixEq
      have prefixTransport :
          proofNormalAtPrefix (splitPrefixFinal word).1 =
            proofNormalAtPrefix [] :=
        congrArg proofNormalAtPrefix actualPrefix
      have nilValue : proofNormalAtPrefix [] = word := by
        rfl
      have normalStep :
          s4_64ProofNormal word = proofNormalAtPrefix [] :=
        foldedNormal.trans prefixTransport
      have normalEq : s4_64ProofNormal word = word :=
        normalStep.trans nilValue
      have reflected :
          Derives edmundsFourSixtyFourBasis word word :=
        Derives.refl word
      have targetType :
          Derives edmundsFourSixtyFourBasis word (s4_64ProofNormal word) =
            Derives edmundsFourSixtyFourBasis word word :=
        congrArg
          (fun target : Word Nat =>
            Derives edmundsFourSixtyFourBasis word target)
          normalEq
      exact Eq.mpr targetType reflected
  | cons first rest =>
      have sourceListLeft :
          (wordOfPrefixFinal (first :: rest) split.2).toList =
            (first :: rest) ++ [split.2] :=
        toList_wordOfPrefixFinal (first :: rest) split.2
      have sourceListAssociation :
          (first :: rest) ++ [split.2] =
            first :: (rest ++ [split.2]) := by
        rfl
      have sourceListRight :
          (Word.mk first (rest ++ [split.2])).toList =
            first :: (rest ++ [split.2]) := by
        rfl
      have sourceListStep :
          (wordOfPrefixFinal (first :: rest) split.2).toList =
            first :: (rest ++ [split.2]) :=
        sourceListLeft.trans sourceListAssociation
      have sourceListEquality :
          (wordOfPrefixFinal (first :: rest) split.2).toList =
            (Word.mk first (rest ++ [split.2])).toList :=
        sourceListStep.trans sourceListRight.symm
      have sourceForm :
          wordOfPrefixFinal (first :: rest) split.2 =
            Word.mk first (rest ++ [split.2]) :=
        Word.toList_injective sourceListEquality
      have prefixWordBridge :
          wordOfPrefixFinal (first :: rest) split.2 =
            wordOfPrefixFinal split.1 split.2 :=
        congrArg (fun prefixWord => wordOfPrefixFinal prefixWord split.2)
          prefixEq.symm
      have sourceRebuildStep :
          Word.mk first (rest ++ [split.2]) =
            wordOfPrefixFinal split.1 split.2 :=
        sourceForm.symm.trans prefixWordBridge
      have sourceEq :
          Word.mk first (rest ++ [split.2]) = word :=
        sourceRebuildStep.trans reconstruct
      let continuation : List Nat → Prop := fun occurrence =>
        match occurrence with
        | [] => False
        | initial :: remaining =>
            Derives edmundsFourSixtyFourBasis
              (Word.mk first (rest ++ [split.2]))
              (edmundsFourSixtyFourLongNormal
                initial remaining split.2)
      have normalizes :
          continuation (firstOccurrenceSequence (first :: rest)) := by
        exact edmundsFourSixtyFourDerivesLongNormal first rest split.2
      cases firstEq : firstOccurrenceSequence (first :: rest) with
      | nil =>
          have foldedSequence :
              firstOccurrenceSequence (first :: rest) =
                first ::
                  (firstOccurrenceSequence rest).filter
                    (fun current => decide (current ≠ first)) := by
            rfl
          have impossible :
              first ::
                  (firstOccurrenceSequence rest).filter
                    (fun current => decide (current ≠ first)) = [] :=
            foldedSequence.symm.trans firstEq
          exact False.elim (List.cons_ne_nil first _ impossible)
      | cons initial remaining =>
          have normalizesSelected :
              continuation (initial :: remaining) :=
            Eq.mp (congrArg continuation firstEq) normalizes
          have normalizesTyped :
              Derives edmundsFourSixtyFourBasis
                (Word.mk first (rest ++ [split.2]))
                (edmundsFourSixtyFourLongNormal
                  initial remaining split.2) := by
            exact normalizesSelected
          have sourceType :
              Derives edmundsFourSixtyFourBasis
                  (Word.mk first (rest ++ [split.2]))
                  (edmundsFourSixtyFourLongNormal
                    initial remaining split.2) =
                Derives edmundsFourSixtyFourBasis word
                  (edmundsFourSixtyFourLongNormal
                    initial remaining split.2) :=
            congrArg
              (fun source : Word Nat =>
                Derives edmundsFourSixtyFourBasis source
                  (edmundsFourSixtyFourLongNormal
                    initial remaining split.2))
              sourceEq
          have normalizesAtSource :
              Derives edmundsFourSixtyFourBasis word
                (edmundsFourSixtyFourLongNormal
                  initial remaining split.2) :=
            Eq.mp sourceType normalizesTyped
          have actualPrefix :
              (splitPrefixFinal word).1 = first :: rest :=
            splitPrefixBridge.symm.trans prefixEq
          have prefixTransport :
              proofNormalAtPrefix (splitPrefixFinal word).1 =
                proofNormalAtPrefix (first :: rest) :=
            congrArg proofNormalAtPrefix actualPrefix
          let proofNormalAtOccurrences : List Nat → Word Nat :=
            fun occurrence =>
              match occurrence with
              | [] => word
              | currentInitial :: currentRemaining =>
                  edmundsFourSixtyFourLongNormal
                    currentInitial currentRemaining
                      (splitPrefixFinal word).2
          have prefixBranch :
              proofNormalAtPrefix (first :: rest) =
                proofNormalAtOccurrences
                  (firstOccurrenceSequence (first :: rest)) := by
            rfl
          have occurrenceTransport :
              proofNormalAtOccurrences
                  (firstOccurrenceSequence (first :: rest)) =
                proofNormalAtOccurrences (initial :: remaining) :=
            congrArg proofNormalAtOccurrences firstEq
          have occurrenceValue :
              proofNormalAtOccurrences (initial :: remaining) =
                edmundsFourSixtyFourLongNormal initial remaining
                  (splitPrefixFinal word).2 := by
            rfl
          have finalTransport :
              edmundsFourSixtyFourLongNormal initial remaining
                  (splitPrefixFinal word).2 =
                edmundsFourSixtyFourLongNormal initial remaining split.2 :=
            congrArg (edmundsFourSixtyFourLongNormal initial remaining)
              splitFinalBridge.symm
          have targetStep1 :
              s4_64ProofNormal word =
                proofNormalAtPrefix (first :: rest) :=
            foldedNormal.trans prefixTransport
          have targetStep2 :
              s4_64ProofNormal word =
                proofNormalAtOccurrences
                  (firstOccurrenceSequence (first :: rest)) :=
            targetStep1.trans prefixBranch
          have targetStep3 :
              s4_64ProofNormal word =
                proofNormalAtOccurrences (initial :: remaining) :=
            targetStep2.trans occurrenceTransport
          have targetStep4 :
              s4_64ProofNormal word =
                edmundsFourSixtyFourLongNormal initial remaining
                  (splitPrefixFinal word).2 :=
            targetStep3.trans occurrenceValue
          have targetEq :
              s4_64ProofNormal word =
                edmundsFourSixtyFourLongNormal
                  initial remaining split.2 :=
            targetStep4.trans finalTransport
          have targetType :
              Derives edmundsFourSixtyFourBasis word
                  (s4_64ProofNormal word) =
                Derives edmundsFourSixtyFourBasis word
                  (edmundsFourSixtyFourLongNormal
                    initial remaining split.2) :=
            congrArg
              (fun target : Word Nat =>
                Derives edmundsFourSixtyFourBasis word target)
              targetEq
          exact Eq.mpr targetType normalizesAtSource

/-- The proof normal is one of the exact duplicate-free open/closed normal
words separated by `S4_64`. -/
theorem s4_64ProofNormal_shape (word : Word Nat) :
    ∃ initial remaining closed,
      (initial :: remaining).Nodup ∧
      s4_64ProofNormal word =
        edmundsFourSixtyFourNormalWord initial remaining closed := by
  let split := splitPrefixFinal word
  have splitRepresentation : split = splitPrefixFinal word := by
    rfl
  have splitPrefixBridge : split.1 = (splitPrefixFinal word).1 :=
    congrArg Prod.fst splitRepresentation
  have splitFinalBridge : split.2 = (splitPrefixFinal word).2 :=
    congrArg Prod.snd splitRepresentation
  have baseReconstruct :
      wordOfPrefixFinal (splitPrefixFinal word).1
          (splitPrefixFinal word).2 = word :=
    wordOfPrefixFinal_split word
  have reconstructAtSplit :
      wordOfPrefixFinal split.1 split.2 =
        wordOfPrefixFinal (splitPrefixFinal word).1
          (splitPrefixFinal word).2 :=
    congrArg
      (fun current : List Nat × Nat =>
        wordOfPrefixFinal current.1 current.2)
      splitRepresentation
  have reconstruct :
      wordOfPrefixFinal split.1 split.2 = word :=
    reconstructAtSplit.trans baseReconstruct
  let proofNormalAtPrefix : List Nat → Word Nat := fun prefixWord =>
    match prefixWord with
    | [] => word
    | first :: rest =>
        match firstOccurrenceSequence (first :: rest) with
        | [] => word
        | initial :: remaining =>
            edmundsFourSixtyFourLongNormal initial remaining
              (splitPrefixFinal word).2
  have foldedNormal :
      s4_64ProofNormal word =
        proofNormalAtPrefix (splitPrefixFinal word).1 := by
    rfl
  cases prefixEq : split.1 with
  | nil =>
      have actualPrefix : (splitPrefixFinal word).1 = [] :=
        splitPrefixBridge.symm.trans prefixEq
      have prefixTransport :
          proofNormalAtPrefix (splitPrefixFinal word).1 =
            proofNormalAtPrefix [] :=
        congrArg proofNormalAtPrefix actualPrefix
      have nilValue : proofNormalAtPrefix [] = word := by
        rfl
      have normalStep :
          s4_64ProofNormal word = proofNormalAtPrefix [] :=
        foldedNormal.trans prefixTransport
      have normalEq : s4_64ProofNormal word = word :=
        normalStep.trans nilValue
      have rebuiltAtNil :
          wordOfPrefixFinal split.1 split.2 =
            wordOfPrefixFinal [] split.2 :=
        congrArg (fun prefixWord => wordOfPrefixFinal prefixWord split.2) prefixEq
      have nilWord :
          wordOfPrefixFinal [] split.2 = Word.singleton split.2 := by
        rfl
      have singletonStep :
          Word.singleton split.2 =
            wordOfPrefixFinal split.1 split.2 :=
        nilWord.symm.trans rebuiltAtNil.symm
      have singleton : Word.singleton split.2 = word :=
        singletonStep.trans reconstruct
      have nodup : (split.2 :: ([] : List Nat)).Nodup :=
        List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩
      have shapeStep1 :
          s4_64ProofNormal word = Word.singleton split.2 :=
        normalEq.trans singleton.symm
      have shapeEquality :
          s4_64ProofNormal word =
            edmundsFourSixtyFourNormalWord split.2 [] false :=
        shapeStep1.trans
          (edmundsFourSixtyFourOpenSingleton_eq split.2)
      exact ⟨split.2, [], false, nodup, shapeEquality⟩
  | cons first rest =>
      have actualPrefix :
          (splitPrefixFinal word).1 = first :: rest :=
        splitPrefixBridge.symm.trans prefixEq
      have prefixTransport :
          proofNormalAtPrefix (splitPrefixFinal word).1 =
            proofNormalAtPrefix (first :: rest) :=
        congrArg proofNormalAtPrefix actualPrefix
      let proofNormalAtOccurrences : List Nat → Word Nat :=
        fun occurrence =>
          match occurrence with
          | [] => word
          | currentInitial :: currentRemaining =>
              edmundsFourSixtyFourLongNormal
                currentInitial currentRemaining
                  (splitPrefixFinal word).2
      have prefixBranch :
          proofNormalAtPrefix (first :: rest) =
            proofNormalAtOccurrences
              (firstOccurrenceSequence (first :: rest)) := by
        rfl
      cases firstEq : firstOccurrenceSequence (first :: rest) with
      | nil =>
          have foldedSequence :
              firstOccurrenceSequence (first :: rest) =
                first ::
                  (firstOccurrenceSequence rest).filter
                    (fun current => decide (current ≠ first)) := by
            rfl
          have impossible :
              first ::
                  (firstOccurrenceSequence rest).filter
                    (fun current => decide (current ≠ first)) = [] :=
            foldedSequence.symm.trans firstEq
          exact False.elim (List.cons_ne_nil first _ impossible)
      | cons initial remaining =>
          have allNodup :
              (firstOccurrenceSequence (first :: rest)).Nodup :=
            firstOccurrenceSequence_nodup (first :: rest)
          have nodupType :
              (firstOccurrenceSequence (first :: rest)).Nodup =
                (initial :: remaining).Nodup :=
            congrArg List.Nodup firstEq
          have keyNodup : (initial :: remaining).Nodup :=
            Eq.mp nodupType allNodup
          have occurrenceTransport :
              proofNormalAtOccurrences
                  (firstOccurrenceSequence (first :: rest)) =
                proofNormalAtOccurrences (initial :: remaining) :=
            congrArg proofNormalAtOccurrences firstEq
          have occurrenceValue :
              proofNormalAtOccurrences (initial :: remaining) =
                edmundsFourSixtyFourLongNormal initial remaining
                  (splitPrefixFinal word).2 := by
            rfl
          have finalTransport :
              edmundsFourSixtyFourLongNormal initial remaining
                  (splitPrefixFinal word).2 =
                edmundsFourSixtyFourLongNormal initial remaining split.2 :=
            congrArg (edmundsFourSixtyFourLongNormal initial remaining)
              splitFinalBridge.symm
          have targetStep1 :
              s4_64ProofNormal word =
                proofNormalAtPrefix (first :: rest) :=
            foldedNormal.trans prefixTransport
          have targetStep2 :
              s4_64ProofNormal word =
                proofNormalAtOccurrences
                  (firstOccurrenceSequence (first :: rest)) :=
            targetStep1.trans prefixBranch
          have targetStep3 :
              s4_64ProofNormal word =
                proofNormalAtOccurrences (initial :: remaining) :=
            targetStep2.trans occurrenceTransport
          have targetStep4 :
              s4_64ProofNormal word =
                edmundsFourSixtyFourLongNormal initial remaining
                  (splitPrefixFinal word).2 :=
            targetStep3.trans occurrenceValue
          have proofNormalLong :
              s4_64ProofNormal word =
                edmundsFourSixtyFourLongNormal
                  initial remaining split.2 :=
            targetStep4.trans finalTransport
          by_cases finalMem : split.2 ∈ initial :: remaining
          · have longClosed :
                edmundsFourSixtyFourLongNormal
                    initial remaining split.2 =
                  Word.mk initial (remaining ++ [initial]) := by
              exact if_pos finalMem
            have normalClosed :
                edmundsFourSixtyFourNormalWord
                    initial remaining true =
                  Word.mk initial (remaining ++ [initial]) := by
              rfl
            have closedStep :
                s4_64ProofNormal word =
                  Word.mk initial (remaining ++ [initial]) :=
              proofNormalLong.trans longClosed
            have closedShape :
                s4_64ProofNormal word =
                  edmundsFourSixtyFourNormalWord
                    initial remaining true :=
              closedStep.trans normalClosed.symm
            exact ⟨initial, remaining, true, keyNodup, closedShape⟩
          · have singletonNodup : ([split.2] : List Nat).Nodup :=
              List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩
            have disjoint :
                ∀ selected : Nat, selected ∈ initial :: remaining →
                  ∀ terminal : Nat, terminal ∈ [split.2] →
                    selected ≠ terminal := by
              intro selected selectedMem terminal terminalMem selectedEq
              have terminalEq : terminal = split.2 :=
                List.mem_singleton.mp terminalMem
              have selectedFinal : selected = split.2 :=
                selectedEq.trans terminalEq
              have finalSelected : split.2 ∈ initial :: remaining :=
                Eq.mp
                  (congrArg
                    (fun member : Nat => member ∈ initial :: remaining)
                    selectedFinal)
                  selectedMem
              exact finalMem finalSelected
            have extendedNodup :
                (initial :: remaining ++ [split.2]).Nodup :=
              List.nodup_append.2 ⟨keyNodup, singletonNodup, disjoint⟩
            have longOpen :
                edmundsFourSixtyFourLongNormal
                    initial remaining split.2 =
                  Word.mk initial (remaining ++ [split.2]) := by
              exact if_neg finalMem
            have normalOpen :
                edmundsFourSixtyFourNormalWord
                    initial (remaining ++ [split.2]) false =
                  Word.mk initial (remaining ++ [split.2]) := by
              rfl
            have openStep :
                s4_64ProofNormal word =
                  Word.mk initial (remaining ++ [split.2]) :=
              proofNormalLong.trans longOpen
            have openShape :
                s4_64ProofNormal word =
                  edmundsFourSixtyFourNormalWord
                    initial (remaining ++ [split.2]) false :=
              openStep.trans normalOpen.symm
            exact
              ⟨initial, remaining ++ [split.2], false,
                extendedNodup, openShape⟩

/-- Validity in `S4_64` makes the proof normal forms literally equal. -/
theorem s4_64ProofNormal_eq_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy FactorTables.s4_64.semigroup) :
    s4_64ProofNormal identity.lhs =
      s4_64ProofNormal identity.rhs := by
  obtain ⟨leftInitial, leftRemaining, leftClosed,
      leftNodup, leftShape⟩ :=
    s4_64ProofNormal_shape identity.lhs
  obtain ⟨rightInitial, rightRemaining, rightClosed,
      rightNodup, rightShape⟩ :=
    s4_64ProofNormal_shape identity.rhs
  have leftDerivation :
      Derives edmundsFourSixtyFourBasis identity.lhs
        (s4_64ProofNormal identity.lhs) :=
    derivesS4_64ProofNormal identity.lhs
  have rightDerivation :
      Derives edmundsFourSixtyFourBasis identity.rhs
        (s4_64ProofNormal identity.rhs) :=
    derivesS4_64ProofNormal identity.rhs
  have normalEvalEqual :
      ∀ valuation : Nat → Fin 4,
        FactorTables.s4_64.semigroup.eval valuation
            (edmundsFourSixtyFourNormalWord
              leftInitial leftRemaining leftClosed) =
          FactorTables.s4_64.semigroup.eval valuation
            (edmundsFourSixtyFourNormalWord
              rightInitial rightRemaining rightClosed) := by
    intro valuation
    have leftSound :
        FactorTables.s4_64.semigroup.eval valuation identity.lhs =
          FactorTables.s4_64.semigroup.eval valuation
            (s4_64ProofNormal identity.lhs) :=
      leftDerivation.sound Generated.S4_64.representative_basis.1 valuation
    have rightSound :
        FactorTables.s4_64.semigroup.eval valuation identity.rhs =
          FactorTables.s4_64.semigroup.eval valuation
            (s4_64ProofNormal identity.rhs) :=
      rightDerivation.sound Generated.S4_64.representative_basis.1 valuation
    have leftShapeEval :
        FactorTables.s4_64.semigroup.eval valuation
            (s4_64ProofNormal identity.lhs) =
          FactorTables.s4_64.semigroup.eval valuation
            (edmundsFourSixtyFourNormalWord
              leftInitial leftRemaining leftClosed) :=
      congrArg
        (FactorTables.s4_64.semigroup.eval valuation)
        leftShape
    have rightShapeEval :
        FactorTables.s4_64.semigroup.eval valuation
            (s4_64ProofNormal identity.rhs) =
          FactorTables.s4_64.semigroup.eval valuation
            (edmundsFourSixtyFourNormalWord
              rightInitial rightRemaining rightClosed) :=
      congrArg
        (FactorTables.s4_64.semigroup.eval valuation)
        rightShape
    have leftSourceToNormal :
        FactorTables.s4_64.semigroup.eval valuation identity.lhs =
          FactorTables.s4_64.semigroup.eval valuation
            (edmundsFourSixtyFourNormalWord
              leftInitial leftRemaining leftClosed) :=
      leftSound.trans leftShapeEval
    have rightSourceToNormal :
        FactorTables.s4_64.semigroup.eval valuation identity.rhs =
          FactorTables.s4_64.semigroup.eval valuation
            (edmundsFourSixtyFourNormalWord
              rightInitial rightRemaining rightClosed) :=
      rightSound.trans rightShapeEval
    have evaluationStep :
        FactorTables.s4_64.semigroup.eval valuation
            (edmundsFourSixtyFourNormalWord
              leftInitial leftRemaining leftClosed) =
          FactorTables.s4_64.semigroup.eval valuation identity.rhs :=
      leftSourceToNormal.symm.trans (valid valuation)
    exact evaluationStep.trans rightSourceToNormal
  have normalWordsEqual :
      edmundsFourSixtyFourNormalWord
          leftInitial leftRemaining leftClosed =
        edmundsFourSixtyFourNormalWord
          rightInitial rightRemaining rightClosed :=
    edmundsFourSixtyFourNormalWord_eq_of_eval_eq
      leftInitial rightInitial leftRemaining rightRemaining
      leftClosed rightClosed leftNodup rightNodup normalEvalEqual
  have shapeStep :
      s4_64ProofNormal identity.lhs =
        edmundsFourSixtyFourNormalWord
          rightInitial rightRemaining rightClosed :=
    leftShape.trans normalWordsEqual
  exact shapeStep.trans rightShape.symm

/-- Dropping the marker from the proof normal recovers exactly the
first-occurrence sequence of the prefix before the original final letter. -/
theorem s4_64ProofNormal_dropLast (word : Word Nat) :
    (s4_64ProofNormal word).toList.dropLast =
      prefixFirstOccurrences word := by
  let split := splitPrefixFinal word
  have splitRepresentation : split = splitPrefixFinal word := by
    rfl
  have splitPrefixBridge : split.1 = (splitPrefixFinal word).1 :=
    congrArg Prod.fst splitRepresentation
  have splitFinalBridge : split.2 = (splitPrefixFinal word).2 :=
    congrArg Prod.snd splitRepresentation
  have baseReconstruct :
      wordOfPrefixFinal (splitPrefixFinal word).1
          (splitPrefixFinal word).2 = word :=
    wordOfPrefixFinal_split word
  have reconstructAtSplit :
      wordOfPrefixFinal split.1 split.2 =
        wordOfPrefixFinal (splitPrefixFinal word).1
          (splitPrefixFinal word).2 :=
    congrArg
      (fun current : List Nat × Nat =>
        wordOfPrefixFinal current.1 current.2)
      splitRepresentation
  have reconstruct :
      wordOfPrefixFinal split.1 split.2 = word :=
    reconstructAtSplit.trans baseReconstruct
  let proofNormalAtPrefix : List Nat → Word Nat := fun prefixWord =>
    match prefixWord with
    | [] => word
    | first :: rest =>
        match firstOccurrenceSequence (first :: rest) with
        | [] => word
        | initial :: remaining =>
            edmundsFourSixtyFourLongNormal initial remaining
              (splitPrefixFinal word).2
  have foldedNormal :
      s4_64ProofNormal word =
        proofNormalAtPrefix (splitPrefixFinal word).1 := by
    rfl
  have foldedPrefix :
      prefixFirstOccurrences word =
        firstOccurrenceSequence (splitPrefixFinal word).1 := by
    rfl
  cases prefixEq : split.1 with
  | nil =>
      have actualPrefix : (splitPrefixFinal word).1 = [] :=
        splitPrefixBridge.symm.trans prefixEq
      have normalPrefixTransport :
          proofNormalAtPrefix (splitPrefixFinal word).1 =
            proofNormalAtPrefix [] :=
        congrArg proofNormalAtPrefix actualPrefix
      have nilNormal : proofNormalAtPrefix [] = word := by
        rfl
      have normalStep :
          s4_64ProofNormal word = proofNormalAtPrefix [] :=
        foldedNormal.trans normalPrefixTransport
      have normalEq : s4_64ProofNormal word = word :=
        normalStep.trans nilNormal
      have rebuiltAtNil :
          wordOfPrefixFinal split.1 split.2 =
            wordOfPrefixFinal [] split.2 :=
        congrArg (fun prefixWord => wordOfPrefixFinal prefixWord split.2) prefixEq
      have nilWord :
          wordOfPrefixFinal [] split.2 = Word.singleton split.2 := by
        rfl
      have singletonStep :
          Word.singleton split.2 =
            wordOfPrefixFinal split.1 split.2 :=
        nilWord.symm.trans rebuiltAtNil.symm
      have singleton : Word.singleton split.2 = word :=
        singletonStep.trans reconstruct
      have prefixTransport :
          firstOccurrenceSequence (splitPrefixFinal word).1 =
            firstOccurrenceSequence [] :=
        congrArg firstOccurrenceSequence actualPrefix
      have emptySequence : firstOccurrenceSequence [] = [] := by
        rfl
      have prefixStep :
          prefixFirstOccurrences word = firstOccurrenceSequence [] :=
        foldedPrefix.trans prefixTransport
      have prefixEmpty : prefixFirstOccurrences word = [] :=
        prefixStep.trans emptySequence
      have dropNormal :
          (s4_64ProofNormal word).toList.dropLast =
            word.toList.dropLast :=
        congrArg (fun current : Word Nat => current.toList.dropLast)
          normalEq
      have dropSingleton :
          word.toList.dropLast =
            (Word.singleton split.2).toList.dropLast :=
        congrArg (fun current : Word Nat => current.toList.dropLast)
          singleton.symm
      have singletonDrop :
          (Word.singleton split.2).toList.dropLast = [] := by
        rfl
      have resultStep1 :
          (s4_64ProofNormal word).toList.dropLast =
            (Word.singleton split.2).toList.dropLast :=
        dropNormal.trans dropSingleton
      have resultStep2 :
          (s4_64ProofNormal word).toList.dropLast = [] :=
        resultStep1.trans singletonDrop
      exact resultStep2.trans prefixEmpty.symm
  | cons first rest =>
      have actualPrefix :
          (splitPrefixFinal word).1 = first :: rest :=
        splitPrefixBridge.symm.trans prefixEq
      have normalPrefixTransport :
          proofNormalAtPrefix (splitPrefixFinal word).1 =
            proofNormalAtPrefix (first :: rest) :=
        congrArg proofNormalAtPrefix actualPrefix
      let proofNormalAtOccurrences : List Nat → Word Nat :=
        fun occurrence =>
          match occurrence with
          | [] => word
          | currentInitial :: currentRemaining =>
              edmundsFourSixtyFourLongNormal
                currentInitial currentRemaining
                  (splitPrefixFinal word).2
      have prefixBranch :
          proofNormalAtPrefix (first :: rest) =
            proofNormalAtOccurrences
              (firstOccurrenceSequence (first :: rest)) := by
        rfl
      cases firstEq : firstOccurrenceSequence (first :: rest) with
      | nil =>
          have foldedSequence :
              firstOccurrenceSequence (first :: rest) =
                first ::
                  (firstOccurrenceSequence rest).filter
                    (fun current => decide (current ≠ first)) := by
            rfl
          have impossible :
              first ::
                  (firstOccurrenceSequence rest).filter
                    (fun current => decide (current ≠ first)) = [] :=
            foldedSequence.symm.trans firstEq
          exact False.elim (List.cons_ne_nil first _ impossible)
      | cons initial remaining =>
          have occurrenceTransport :
              proofNormalAtOccurrences
                  (firstOccurrenceSequence (first :: rest)) =
                proofNormalAtOccurrences (initial :: remaining) :=
            congrArg proofNormalAtOccurrences firstEq
          have occurrenceValue :
              proofNormalAtOccurrences (initial :: remaining) =
                edmundsFourSixtyFourLongNormal initial remaining
                  (splitPrefixFinal word).2 := by
            rfl
          have finalTransport :
              edmundsFourSixtyFourLongNormal initial remaining
                  (splitPrefixFinal word).2 =
                edmundsFourSixtyFourLongNormal initial remaining split.2 :=
            congrArg (edmundsFourSixtyFourLongNormal initial remaining)
              splitFinalBridge.symm
          have normalStep1 :
              s4_64ProofNormal word =
                proofNormalAtPrefix (first :: rest) :=
            foldedNormal.trans normalPrefixTransport
          have normalStep2 :
              s4_64ProofNormal word =
                proofNormalAtOccurrences
                  (firstOccurrenceSequence (first :: rest)) :=
            normalStep1.trans prefixBranch
          have normalStep3 :
              s4_64ProofNormal word =
                proofNormalAtOccurrences (initial :: remaining) :=
            normalStep2.trans occurrenceTransport
          have normalStep4 :
              s4_64ProofNormal word =
                edmundsFourSixtyFourLongNormal initial remaining
                  (splitPrefixFinal word).2 :=
            normalStep3.trans occurrenceValue
          have normalLong :
              s4_64ProofNormal word =
                edmundsFourSixtyFourLongNormal
                  initial remaining split.2 :=
            normalStep4.trans finalTransport
          have prefixOccurrenceTransport :
              firstOccurrenceSequence (splitPrefixFinal word).1 =
                firstOccurrenceSequence (first :: rest) :=
            congrArg firstOccurrenceSequence actualPrefix
          have prefixStep :
              prefixFirstOccurrences word =
                firstOccurrenceSequence (first :: rest) :=
            foldedPrefix.trans prefixOccurrenceTransport
          have prefixNormal :
              prefixFirstOccurrences word = initial :: remaining :=
            prefixStep.trans firstEq
          have dropNormal :
              (s4_64ProofNormal word).toList.dropLast =
                (edmundsFourSixtyFourLongNormal
                  initial remaining split.2).toList.dropLast :=
            congrArg (fun current : Word Nat => current.toList.dropLast)
              normalLong
          have resultStep :
              (s4_64ProofNormal word).toList.dropLast =
                initial :: remaining :=
            dropNormal.trans
              (edmundsFourSixtyFourLongNormal_dropLast
                initial remaining split.2)
          exact resultStep.trans prefixNormal.symm

/-! ## Exact joint signature -/

/-- The two proof-normal coordinates retained by the selected factors. -/
structure SameJointSignature (left right : Word Nat) : Prop where
  factorNormal : s4_64ProofNormal left = s4_64ProofNormal right
  lastOccurrences :
    S5_1092.lastOccurrenceSequence left.toList =
      S5_1092.lastOccurrenceSequence right.toList

namespace SameJointSignature

theorem refl (word : Word Nat) : SameJointSignature word word :=
  ⟨rfl, rfl⟩

theorem symm {left right : Word Nat}
    (same : SameJointSignature left right) :
    SameJointSignature right left :=
  ⟨same.factorNormal.symm, same.lastOccurrences.symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameJointSignature left middle)
    (second : SameJointSignature middle right) :
    SameJointSignature left right :=
  ⟨first.factorNormal.trans second.factorNormal,
    first.lastOccurrences.trans second.lastOccurrences⟩

theorem prefixFirstOccurrences_eq {left right : Word Nat}
    (same : SameJointSignature left right) :
    prefixFirstOccurrences left = prefixFirstOccurrences right := by
  have normalCoordinate :
      (s4_64ProofNormal left).toList.dropLast =
        (s4_64ProofNormal right).toList.dropLast :=
    congrArg (fun current : Word Nat => current.toList.dropLast)
      same.factorNormal
  have leftCoordinate :
      (s4_64ProofNormal left).toList.dropLast =
        prefixFirstOccurrences left :=
    s4_64ProofNormal_dropLast left
  have rightCoordinate :
      (s4_64ProofNormal right).toList.dropLast =
        prefixFirstOccurrences right :=
    s4_64ProofNormal_dropLast right
  have coordinateStep :
      prefixFirstOccurrences left =
        (s4_64ProofNormal right).toList.dropLast :=
    leftCoordinate.symm.trans normalCoordinate
  exact coordinateStep.trans rightCoordinate

end SameJointSignature

/-! ## Last-occurrence coordinate of `S4_116op` -/

/-- Validity in the selected opposite band factor fixes the complete
last-occurrence sequence. -/
theorem s4_116opValid_lastOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy FactorTables.s4_116op.semigroup) :
    S5_1092.lastOccurrenceSequence identity.lhs.toList =
      S5_1092.lastOccurrenceSequence identity.rhs.toList := by
  have factorSemigroup :
      FactorTables.s4_116op.semigroup =
        Generated.Catalogue.S4_116.table.semigroup.opposite :=
    FactorTables.s4_116op_semigroup
  have oppositeValidityType :
      identity.SatisfiedBy FactorTables.s4_116op.semigroup =
        identity.SatisfiedBy
          Generated.Catalogue.S4_116.table.semigroup.opposite :=
    congrArg (fun current => identity.SatisfiedBy current)
      factorSemigroup
  have oppositeValid :
      identity.SatisfiedBy
        Generated.Catalogue.S4_116.table.semigroup.opposite :=
    Eq.mp oppositeValidityType valid
  have reversedValid :
      identity.reversed.SatisfiedBy
        Generated.Catalogue.S4_116.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed identity
      Generated.Catalogue.S4_116.table.semigroup).mp oppositeValid
  have lrbValid :
      identity.reversed.SatisfiedBy leftRegularBandThree.semigroup :=
    Generated.BandEmbeddingTransfers.S4_116.embedding.pullback_identity
      identity.reversed reversedValid
  have firstReversed :
      firstOccurrenceSequence identity.reversed.lhs.toList =
        firstOccurrenceSequence identity.reversed.rhs.toList :=
    firstOccurrenceSequence_eq_of_valid identity.reversed lrbValid
  have reversedLhsWord :
      identity.reversed.lhs = identity.lhs.reverse := by
    rfl
  have reversedRhsWord :
      identity.reversed.rhs = identity.rhs.reverse := by
    rfl
  have reversedLhsListStep :
      identity.reversed.lhs.toList = identity.lhs.reverse.toList :=
    congrArg Word.toList reversedLhsWord
  have reversedRhsListStep :
      identity.reversed.rhs.toList = identity.rhs.reverse.toList :=
    congrArg Word.toList reversedRhsWord
  have reversedLhsList :
      identity.reversed.lhs.toList = identity.lhs.toList.reverse :=
    reversedLhsListStep.trans (Word.toList_reverse identity.lhs)
  have reversedRhsList :
      identity.reversed.rhs.toList = identity.rhs.toList.reverse :=
    reversedRhsListStep.trans (Word.toList_reverse identity.rhs)
  have leftFirstBridge :
      firstOccurrenceSequence identity.reversed.lhs.toList =
        firstOccurrenceSequence identity.lhs.toList.reverse :=
    congrArg firstOccurrenceSequence reversedLhsList
  have rightFirstBridge :
      firstOccurrenceSequence identity.reversed.rhs.toList =
        firstOccurrenceSequence identity.rhs.toList.reverse :=
    congrArg firstOccurrenceSequence reversedRhsList
  have firstStep :
      firstOccurrenceSequence identity.lhs.toList.reverse =
        firstOccurrenceSequence identity.reversed.rhs.toList :=
    leftFirstBridge.symm.trans firstReversed
  have firstOnReversedLists :
      firstOccurrenceSequence identity.lhs.toList.reverse =
        firstOccurrenceSequence identity.rhs.toList.reverse :=
    firstStep.trans rightFirstBridge
  have reversedEquality :
      (firstOccurrenceSequence identity.lhs.toList.reverse).reverse =
        (firstOccurrenceSequence identity.rhs.toList.reverse).reverse :=
    congrArg List.reverse firstOnReversedLists
  have leftLastBridge :
      S5_1092.lastOccurrenceSequence identity.lhs.toList =
        (firstOccurrenceSequence identity.lhs.toList.reverse).reverse :=
    S5_1092.lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence
      identity.lhs.toList
  have rightLastBridge :
      S5_1092.lastOccurrenceSequence identity.rhs.toList =
        (firstOccurrenceSequence identity.rhs.toList.reverse).reverse :=
    S5_1092.lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence
      identity.rhs.toList
  have lastStep :
      S5_1092.lastOccurrenceSequence identity.lhs.toList =
        (firstOccurrenceSequence identity.rhs.toList.reverse).reverse :=
    leftLastBridge.trans reversedEquality
  exact lastStep.trans rightLastBridge.symm

/-- Validity in the selected factors supplies the complete signature used
by the unrestricted normalizer. -/
theorem sameJointSignature_of_factor_valid
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy FactorTables.s4_116op.semigroup)
    (rightValid :
      identity.SatisfiedBy FactorTables.s4_64.semigroup) :
    SameJointSignature identity.lhs identity.rhs :=
  ⟨s4_64ProofNormal_eq_of_valid identity rightValid,
    s4_116opValid_lastOccurrenceSequence_eq identity leftValid⟩

end SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469

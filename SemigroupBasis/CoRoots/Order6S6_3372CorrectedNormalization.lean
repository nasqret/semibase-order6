import SemigroupBasis.CoRoots.Order6S6_3372CorrectedBasis
import SemigroupBasis.Examples.FinalMarkerThree

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6S6_3372CorrectedBasis

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

/-- A word with an explicit prefix and its final two variables. -/
def wordOfTerminalPair
    (stem : List Nat) (penultimate final : Nat) : Word Nat :=
  wordOfPrefixFinal (stem ++ [penultimate]) final

@[simp]
theorem toList_wordOfTerminalPair
    (stem : List Nat) (penultimate final : Nat) :
    (wordOfTerminalPair stem penultimate final).toList =
      stem ++ [penultimate, final] := by
  simp [wordOfTerminalPair, toList_wordOfPrefixFinal,
    List.append_assoc]

@[simp]
private theorem wordOfPrefixFinal_append_singleton
    (stem : List Nat) (penultimate final : Nat) :
    wordOfPrefixFinal stem penultimate ++ Word.singleton final =
      wordOfPrefixFinal (stem ++ [penultimate]) final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal, toList_wordOfPrefixFinal]

private theorem perm_of_nodup_mem_iff :
    ∀ {xs ys : List Nat},
      xs.Nodup →
      ys.Nodup →
      (∀ z, z ∈ xs ↔ z ∈ ys) →
      xs.Perm ys
  | [], [], _, _, _ => List.Perm.refl []
  | [], y :: ys, _, _, hmem => by
      exact False.elim <| by
        have := (hmem y).2 (List.Mem.head ys)
        exact List.not_mem_nil this
  | x :: xs, [], _, _, hmem => by
      exact False.elim <| by
        have := (hmem x).1 (List.Mem.head xs)
        exact List.not_mem_nil this
  | x :: xs, y :: ys, hxs, hys, hmem => by
      have hxIn : x ∈ y :: ys :=
        (hmem x).1 (List.Mem.head xs)
      have targetPerm : (y :: ys).Perm (x :: (y :: ys).erase x) :=
        List.perm_cons_erase hxIn
      have tailNodup : xs.Nodup :=
        (List.nodup_cons.mp hxs).2
      have erasedNodup : ((y :: ys).erase x).Nodup :=
        hys.erase _
      have arrangedNodup :
          (x :: (y :: ys).erase x).Nodup :=
        targetPerm.nodup_iff.mp hys
      have xNotInErase : x ∉ (y :: ys).erase x :=
        (List.nodup_cons.mp arrangedNodup).1
      have tailMem :
          ∀ z, z ∈ xs ↔ z ∈ (y :: ys).erase x := by
        intro z
        have xNotInXs : x ∉ xs :=
          (List.nodup_cons.mp hxs).1
        by_cases hzx : z = x
        · subst z
          exact iff_of_false xNotInXs xNotInErase
        · constructor
          · intro hz
            have targetMem :=
              (targetPerm.mem_iff).mp <|
                (hmem z).1 (List.Mem.tail x hz)
            simp only [List.mem_cons] at targetMem
            rcases targetMem with targetHead | targetTail
            · exact False.elim (hzx targetHead)
            · exact targetTail
          · intro hz
            have targetMem : z ∈ x :: (y :: ys).erase x :=
              List.Mem.tail x hz
            have sourceMem :=
              (hmem z).2 ((targetPerm.mem_iff).mpr targetMem)
            simp only [List.mem_cons] at sourceMem
            rcases sourceMem with sourceHead | sourceTail
            · exact False.elim (hzx sourceHead)
            · exact sourceTail
      exact
        (List.Perm.cons x
          (perm_of_nodup_mem_iff
            tailNodup erasedNodup tailMem)).trans targetPerm.symm

/-- Any permutation before two fixed endpoint variables follows from the
four-variable prefix swap. -/
theorem derivesPrefixPermutation
    {prefix₁ prefix₂ : List Nat}
    (permutation : prefix₁.Perm prefix₂)
    (penultimate final : Nat) :
    Derives basis
      (wordOfTerminalPair prefix₁ penultimate final)
      (wordOfTerminalPair prefix₂ penultimate final) := by
  induction permutation with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
        List.append_assoc] using
        Derives.prepend (Word.singleton x) ih
  | swap x y xs =>
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
        wordOfPrefixFinal_append_singleton,
        Word.append_assoc, List.append_assoc] using
        derivesPrefixSwap
          (Word.singleton y) (Word.singleton x)
          (wordOfPrefixFinal xs penultimate)
          (Word.singleton final)
  | trans _ _ first second =>
      exact first.trans second

private theorem derivesDeleteLeadingPrefix
    (x : Nat) (stem : List Nat)
    (penultimate final : Nat)
    (member : x ∈ stem) :
    Derives basis
      (wordOfTerminalPair (x :: stem) penultimate final)
      (wordOfTerminalPair stem penultimate final) := by
  have expose : stem.Perm (x :: stem.erase x) :=
    List.perm_cons_erase member
  have sourcePermutation :
      (x :: stem).Perm (x :: x :: stem.erase x) :=
    List.Perm.cons x expose
  have contraction :
      Derives basis
        (wordOfTerminalPair
          (x :: x :: stem.erase x) penultimate final)
        (wordOfTerminalPair
          (x :: stem.erase x) penultimate final) := by
    have raw :=
      derivesPrefixContraction
        (Word.singleton x)
        (wordOfPrefixFinal (stem.erase x) penultimate)
        (Word.singleton final)
    have sourceWord :
        (((Word.singleton x ++ Word.singleton x) ++
            wordOfPrefixFinal (stem.erase x) penultimate) ++
          Word.singleton final) =
          wordOfTerminalPair
            (x :: x :: stem.erase x) penultimate final := by
      calc
        (((Word.singleton x ++ Word.singleton x) ++
              wordOfPrefixFinal (stem.erase x) penultimate) ++
            Word.singleton final) =
            (Word.singleton x ++ Word.singleton x) ++
              (wordOfPrefixFinal (stem.erase x) penultimate ++
                Word.singleton final) := Word.append_assoc _ _ _
        _ = (Word.singleton x ++ Word.singleton x) ++
              wordOfPrefixFinal
                (stem.erase x ++ [penultimate]) final := by
            rw [wordOfPrefixFinal_append_singleton]
        _ = Word.singleton x ++
              (Word.singleton x ++
                wordOfPrefixFinal
                  (stem.erase x ++ [penultimate]) final) :=
            Word.append_assoc _ _ _
        _ = wordOfTerminalPair
              (x :: x :: stem.erase x) penultimate final := rfl
    have targetWord :
        ((Word.singleton x ++
            wordOfPrefixFinal (stem.erase x) penultimate) ++
          Word.singleton final) =
          wordOfTerminalPair
            (x :: stem.erase x) penultimate final := by
      calc
        ((Word.singleton x ++
              wordOfPrefixFinal (stem.erase x) penultimate) ++
            Word.singleton final) =
            Word.singleton x ++
              (wordOfPrefixFinal (stem.erase x) penultimate ++
                Word.singleton final) := Word.append_assoc _ _ _
        _ = Word.singleton x ++
              wordOfPrefixFinal
                (stem.erase x ++ [penultimate]) final := by
            rw [wordOfPrefixFinal_append_singleton]
        _ = wordOfTerminalPair
              (x :: stem.erase x) penultimate final := rfl
    rw [sourceWord, targetWord] at raw
    exact raw
  exact
    (derivesPrefixPermutation
      sourcePermutation penultimate final).trans <|
      contraction.trans <|
        derivesPrefixPermutation expose.symm penultimate final

/-- Delete all duplicate variables from the prefix before the endpoint pair. -/
theorem derivesNormalizePrefix :
    ∀ (stem : List Nat) (penultimate final : Nat),
      Derives basis
        (wordOfTerminalPair stem penultimate final)
        (wordOfTerminalPair
          (finalMarkerPrefixReduce stem) penultimate final)
  | [], penultimate, final =>
      Derives.refl _
  | x :: xs, penultimate, final => by
      have tailNormal :=
        derivesNormalizePrefix xs penultimate final
      have prefixed :
          Derives basis
            (wordOfTerminalPair
              (x :: xs) penultimate final)
            (wordOfTerminalPair
              (x :: finalMarkerPrefixReduce xs)
              penultimate final) := by
        simpa [wordOfTerminalPair, wordOfPrefixFinal,
          List.append_assoc] using
          Derives.prepend (Word.singleton x) tailNormal
      by_cases member : x ∈ finalMarkerPrefixReduce xs
      · have reduced :
            finalMarkerPrefixReduce (x :: xs) =
              finalMarkerPrefixReduce xs := by
          simp [finalMarkerPrefixReduce, member]
        rw [reduced]
        exact prefixed.trans <|
          derivesDeleteLeadingPrefix
            x (finalMarkerPrefixReduce xs)
            penultimate final member
      · have reduced :
            finalMarkerPrefixReduce (x :: xs) =
              x :: finalMarkerPrefixReduce xs := by
          simp [finalMarkerPrefixReduce, member]
        rw [reduced]
        exact prefixed

private theorem perm_cons_to_end (a : Nat) :
    ∀ stem : List Nat,
      (a :: stem).Perm (stem ++ [a])
  | [] => List.Perm.refl _
  | x :: xs =>
      (List.Perm.swap x a xs).trans <|
        List.Perm.cons x (perm_cons_to_end a xs)

private theorem derivesGatherWithPrefix :
    ∀ (stem : List Nat) (left right : Nat),
      Derives basis
        (wordOfPrefixFinal (stem ++ [left, right]) left)
        (wordOfPrefixFinal (stem ++ [right, left]) left)
  | [], left, right => by
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        derivesGather
          (Word.singleton left) (Word.singleton right)
  | x :: xs, left, right => by
      simpa [wordOfPrefixFinal, List.append_assoc] using
        Derives.prepend (Word.singleton x)
          (derivesGatherWithPrefix xs left right)

private theorem derivesPowerContractionWithPrefix :
    ∀ (stem : List Nat) (marker : Nat),
      Derives basis
        (wordOfTerminalPair (stem ++ [marker]) marker marker)
        (wordOfTerminalPair stem marker marker)
  | [], marker => by
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
        Word.append_assoc] using
        derivesPowerContraction (Word.singleton marker)
  | x :: xs, marker => by
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
        List.append_assoc] using
        Derives.prepend (Word.singleton x)
          (derivesPowerContractionWithPrefix xs marker)

private theorem derivesMakeRepeatedFinal
    (stem : List Nat) (penultimate final : Nat)
    (repeated : final = penultimate ∨ final ∈ stem) :
    ∃ repeatedPrefix,
      Derives basis
        (wordOfTerminalPair stem penultimate final)
        (wordOfTerminalPair repeatedPrefix final final) ∧
      (∀ z,
        z ∈ repeatedPrefix ∨ z = final ↔
          z ∈ stem ∨ z = penultimate ∨ z = final) := by
  rcases repeated with equal | finalMember
  · subst penultimate
    refine ⟨stem, Derives.refl _, ?_⟩
    intro z
    simp [or_assoc]
  · have arrange :
        stem.Perm (stem.erase final ++ [final]) := by
      exact
        (List.perm_cons_erase finalMember).trans <|
          perm_cons_to_end final (stem.erase final)
    have arranged :=
      derivesPrefixPermutation arrange penultimate final
    have gathered :
        Derives basis
          (wordOfTerminalPair
            (stem.erase final ++ [final])
            penultimate final)
          (wordOfTerminalPair
            (stem.erase final ++ [penultimate])
            final final) := by
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
        Word.append_assoc, List.append_assoc] using
        derivesGatherWithPrefix
          (stem.erase final) final penultimate
    refine
      ⟨stem.erase final ++ [penultimate],
        arranged.trans gathered, ?_⟩
    intro z
    simp only [List.mem_append, List.mem_singleton]
    by_cases zFinal : z = final
    · subst z
      simp [finalMember]
    · rw [List.mem_erase_of_ne zFinal]
      simp [zFinal, or_assoc, or_left_comm, or_comm]

/-- Repeated-final normalization.  The prefix contains every support variable
other than the final marker exactly once. -/
theorem derivesRepeatedFinalNormal
    (stem : List Nat) (penultimate final : Nat)
    (repeated : final = penultimate ∨ final ∈ stem) :
    ∃ normalPrefix,
      Derives basis
        (wordOfTerminalPair stem penultimate final)
        (wordOfTerminalPair normalPrefix final final) ∧
      normalPrefix.Nodup ∧
      final ∉ normalPrefix ∧
      (∀ z,
        z ∈ normalPrefix ↔
          (z ∈ stem ∨ z = penultimate ∨ z = final) ∧
            z ≠ final) := by
  obtain ⟨repeatedPrefix, makeRepeated, repeatedSupport⟩ :=
    derivesMakeRepeatedFinal stem penultimate final repeated
  let reduced := finalMarkerPrefixReduce repeatedPrefix
  have normalize :
      Derives basis
        (wordOfTerminalPair repeatedPrefix final final)
        (wordOfTerminalPair reduced final final) := by
    simpa [reduced] using
      derivesNormalizePrefix repeatedPrefix final final
  by_cases finalMember : final ∈ reduced
  · have reducedNodup : reduced.Nodup := by
      simpa [reduced] using
        finalMarkerPrefixReduce_nodup repeatedPrefix
    have fronted :
        reduced.Perm (final :: reduced.erase final) :=
      List.perm_cons_erase finalMember
    have finalAbsent : final ∉ reduced.erase final :=
      (List.nodup_cons.mp
        (fronted.nodup_iff.mp reducedNodup)).1
    have arrange :
        reduced.Perm (reduced.erase final ++ [final]) := by
      exact
        (List.perm_cons_erase finalMember).trans <|
          perm_cons_to_end final (reduced.erase final)
    have arranged :=
      derivesPrefixPermutation arrange final final
    have contracted :=
      derivesPowerContractionWithPrefix
        (reduced.erase final) final
    refine
      ⟨reduced.erase final,
        makeRepeated.trans <|
          normalize.trans <| arranged.trans contracted,
        reducedNodup.erase final,
        finalAbsent,
        ?_⟩
    intro z
    have reducedMemberIff :
        z ∈ reduced ↔ z ∈ repeatedPrefix := by
      simpa [reduced] using
        finalMarkerPrefixReduce_mem z repeatedPrefix
    have repeatedIff := repeatedSupport z
    constructor
    · intro erasedMember
      have member : z ∈ reduced :=
        List.mem_of_mem_erase erasedMember
      have different : z ≠ final := by
        intro equal
        subst z
        exact finalAbsent erasedMember
      exact
        ⟨repeatedIff.mp (Or.inl (reducedMemberIff.mp member)),
          different⟩
    · rintro ⟨sourceMember, different⟩
      have repeatedMember :
          z ∈ repeatedPrefix ∨ z = final :=
        repeatedIff.mpr sourceMember
      rcases repeatedMember with member | equal
      · exact
          (List.mem_erase_of_ne different).mpr
            (reducedMemberIff.mpr member)
      · exact False.elim (different equal)
  · refine
      ⟨reduced,
        makeRepeated.trans normalize,
        finalMarkerPrefixReduce_nodup repeatedPrefix,
        finalMember,
        ?_⟩
    intro z
    rw [finalMarkerPrefixReduce_mem]
    have repeatedIff := repeatedSupport z
    constructor
    · intro member
      exact
        ⟨repeatedIff.mp (Or.inl member),
          fun equal => by
            subst z
            apply finalMember
            exact
              (finalMarkerPrefixReduce_mem
                final repeatedPrefix).mpr member⟩
    · rintro ⟨sourceMember, different⟩
      have repeatedMember :
          z ∈ repeatedPrefix ∨ z = final :=
        repeatedIff.mpr sourceMember
      exact repeatedMember.resolve_right different

/-- Unique-final normalization deliberately retains the penultimate variable
in the prefix exactly when it occurred in the original stem. -/
theorem derivesUniqueFinalNormal
    (stem : List Nat) (penultimate final : Nat)
    (unique : final ≠ penultimate ∧ final ∉ stem) :
    ∃ normalPrefix,
      Derives basis
        (wordOfTerminalPair stem penultimate final)
        (wordOfTerminalPair normalPrefix penultimate final) ∧
      normalPrefix.Nodup ∧
      final ∉ normalPrefix ∧
      (∀ z, z ∈ normalPrefix ↔ z ∈ stem) := by
  let reduced := finalMarkerPrefixReduce stem
  have normalize :
      Derives basis
        (wordOfTerminalPair stem penultimate final)
        (wordOfTerminalPair reduced penultimate final) := by
    simpa [reduced] using
      derivesNormalizePrefix stem penultimate final
  refine
    ⟨reduced,
      normalize,
      finalMarkerPrefixReduce_nodup stem,
      ?_,
      ?_⟩
  · intro finalMember
    exact unique.2 <|
      (finalMarkerPrefixReduce_mem final stem).mp finalMember
  · intro z
    simpa [reduced] using finalMarkerPrefixReduce_mem z stem

private theorem normalizedPairDerives
    (leftPrefix rightPrefix : List Nat)
    (penultimate final : Nat)
    (leftNodup : leftPrefix.Nodup)
    (rightNodup : rightPrefix.Nodup)
    (samePrefix : ∀ z, z ∈ leftPrefix ↔ z ∈ rightPrefix) :
    Derives basis
      (wordOfTerminalPair leftPrefix penultimate final)
      (wordOfTerminalPair rightPrefix penultimate final) :=
  derivesPrefixPermutation
    (perm_of_nodup_mem_iff leftNodup rightNodup samePrefix)
    penultimate final

/-- The two lower-order signatures jointly imply derivability from the
corrected basis. -/
theorem derives_of_signatures
    {left right : Word Nat}
    (content :
      SemigroupBasis.CoRoots.S5_303.SameContentEndpointSignature
        left right)
    (terminal : SameTerminalUniqueSuffixSignature left right) :
    Derives basis left right := by
  classical
  have leftReconstruct := terminalSplit_renderWord left
  have rightReconstruct := terminalSplit_renderWord right
  cases leftSplitEq : terminalSplit left with
  | singleton leftFinal =>
      cases rightSplitEq : terminalSplit right with
      | singleton rightFinal =>
          have rightFinalProperty :
              SemigroupBasis.CoRoots.S5_303.FinalLetter right leftFinal :=
            (content.finalLetter leftFinal).mp <| by
              simp [SemigroupBasis.CoRoots.S5_303.FinalLetter, leftSplitEq]
          have finals : rightFinal = leftFinal := by
            simpa [SemigroupBasis.CoRoots.S5_303.FinalLetter,
              rightSplitEq] using rightFinalProperty
          subst rightFinal
          rw [leftSplitEq] at leftReconstruct
          rw [rightSplitEq] at rightReconstruct
          rw [← leftReconstruct, ← rightReconstruct]
          exact Derives.refl _
      | pair rightPrefix rightPenultimate rightFinal =>
          have leftSingleton : IsSingletonWord left := by
            simp [IsSingletonWord, leftSplitEq]
          have rightSingleton := content.singleton.mp leftSingleton
          simp [IsSingletonWord, rightSplitEq] at rightSingleton
  | pair leftPrefix leftPenultimate leftFinal =>
      cases rightSplitEq : terminalSplit right with
      | singleton rightFinal =>
          have rightSingleton : IsSingletonWord right := by
            simp [IsSingletonWord, rightSplitEq]
          have leftSingleton := content.singleton.mpr rightSingleton
          simp [IsSingletonWord, leftSplitEq] at leftSingleton
      | pair rightPrefix rightPenultimate rightFinal =>
          have rightFinalProperty :
              SemigroupBasis.CoRoots.S5_303.FinalLetter right leftFinal :=
            (content.finalLetter leftFinal).mp <| by
              simp [SemigroupBasis.CoRoots.S5_303.FinalLetter, leftSplitEq]
          have finals : rightFinal = leftFinal := by
            simpa [SemigroupBasis.CoRoots.S5_303.FinalLetter,
              rightSplitEq] using rightFinalProperty
          subst rightFinal
          rw [leftSplitEq] at leftReconstruct
          rw [rightSplitEq] at rightReconstruct
          rw [← leftReconstruct, ← rightReconstruct]
          by_cases leftRepeated :
              leftFinal = leftPenultimate ∨
                leftFinal ∈ leftPrefix
          · have rightRepeated :
                leftFinal = rightPenultimate ∨
                  leftFinal ∈ rightPrefix := by
              apply Decidable.byContradiction
              intro rightNotRepeated
              have rightParts := not_or.mp rightNotRepeated
              have rightPair :
                  SemigroupBasis.CoRoots.S5_303.UniqueFinalPair right
                    rightPenultimate leftFinal := by
                simp [SemigroupBasis.CoRoots.S5_303.UniqueFinalPair,
                  rightSplitEq, rightParts.1, rightParts.2]
              have leftPair :=
                (content.uniqueFinalPair
                  rightPenultimate leftFinal).mpr rightPair
              have leftParts :
                  leftPenultimate = rightPenultimate ∧
                    leftFinal = leftFinal ∧
                    leftFinal ≠ leftPenultimate ∧
                    leftFinal ∉ leftPrefix := by
                simpa [SemigroupBasis.CoRoots.S5_303.UniqueFinalPair,
                  leftSplitEq] using leftPair
              rcases leftRepeated with equal | member
              · exact leftParts.2.2.1 equal
              · exact leftParts.2.2.2 member
            obtain
                ⟨leftNormal, leftDerivation, leftNodup,
                  leftFinalAbsent, leftNormalMem⟩ :=
              derivesRepeatedFinalNormal
                leftPrefix leftPenultimate leftFinal leftRepeated
            obtain
                ⟨rightNormal, rightDerivation, rightNodup,
                  rightFinalAbsent, rightNormalMem⟩ :=
              derivesRepeatedFinalNormal
                rightPrefix rightPenultimate leftFinal rightRepeated
            have normalMem :
                ∀ z, z ∈ leftNormal ↔ z ∈ rightNormal := by
              intro z
              rw [leftNormalMem, rightNormalMem]
              apply and_congr
              · have supportIff := content.support z
                rw [← terminalSplit_renderList left,
                  ← terminalSplit_renderList right,
                  leftSplitEq, rightSplitEq] at supportIff
                simpa [TerminalSplit.renderList,
                  List.append_assoc, or_assoc] using supportIff
              · exact Iff.rfl
            have middle :=
              normalizedPairDerives
                leftNormal rightNormal leftFinal leftFinal
                leftNodup rightNodup normalMem
            exact leftDerivation.trans <|
              middle.trans rightDerivation.symm
          · have leftUniqueParts := not_or.mp leftRepeated
            have leftPair :
                SemigroupBasis.CoRoots.S5_303.UniqueFinalPair left
                  leftPenultimate leftFinal := by
              simp [SemigroupBasis.CoRoots.S5_303.UniqueFinalPair,
                leftSplitEq, leftUniqueParts.1, leftUniqueParts.2]
            have rightPair :=
              (content.uniqueFinalPair
                leftPenultimate leftFinal).mp leftPair
            have rightParts :
                rightPenultimate = leftPenultimate ∧
                  leftFinal = leftFinal ∧
                  leftFinal ≠ rightPenultimate ∧
                  leftFinal ∉ rightPrefix := by
              simpa [SemigroupBasis.CoRoots.S5_303.UniqueFinalPair,
                rightSplitEq] using rightPair
            have rightPenultimateEq :
                rightPenultimate = leftPenultimate :=
              rightParts.1
            subst rightPenultimate
            have penultimateAbsentIff :
                leftPenultimate ∉ leftPrefix ↔
                  leftPenultimate ∉ rightPrefix := by
              calc
                leftPenultimate ∉ leftPrefix ↔
                    UniqueTerminalPair left
                      leftPenultimate leftFinal := by
                  simp [UniqueTerminalPair, leftSplitEq,
                    leftUniqueParts.1, leftUniqueParts.2]
                _ ↔ UniqueTerminalPair right
                      leftPenultimate leftFinal :=
                  terminal.uniqueTerminalPair
                    leftPenultimate leftFinal
                _ ↔ leftPenultimate ∉ rightPrefix := by
                  simp [UniqueTerminalPair, rightSplitEq,
                    rightParts.2.2.1, rightParts.2.2.2]
            have penultimateMemIff :
                leftPenultimate ∈ leftPrefix ↔
                  leftPenultimate ∈ rightPrefix := by
              constructor
              · intro leftMember
                apply Decidable.byContradiction
                intro rightAbsent
                exact (penultimateAbsentIff.mpr rightAbsent) leftMember
              · intro rightMember
                apply Decidable.byContradiction
                intro leftAbsent
                exact (penultimateAbsentIff.mp leftAbsent) rightMember
            obtain
                ⟨leftNormal, leftDerivation, leftNodup,
                  leftFinalAbsent, leftNormalMem⟩ :=
              derivesUniqueFinalNormal
                leftPrefix leftPenultimate leftFinal leftUniqueParts
            obtain
                ⟨rightNormal, rightDerivation, rightNodup,
                  rightFinalAbsent, rightNormalMem⟩ :=
              derivesUniqueFinalNormal
                rightPrefix leftPenultimate leftFinal
                ⟨rightParts.2.2.1, rightParts.2.2.2⟩
            have normalMem :
                ∀ z, z ∈ leftNormal ↔ z ∈ rightNormal := by
              intro z
              rw [leftNormalMem, rightNormalMem]
              by_cases zPenultimate : z = leftPenultimate
              · subst z
                exact penultimateMemIff
              · by_cases zFinal : z = leftFinal
                · subst z
                  exact iff_of_false
                    leftUniqueParts.2 rightParts.2.2.2
                · have supportIff := content.support z
                  rw [← terminalSplit_renderList left,
                    ← terminalSplit_renderList right,
                    leftSplitEq, rightSplitEq] at supportIff
                  simpa [TerminalSplit.renderList,
                    List.append_assoc, zPenultimate, zFinal] using supportIff
            have middle :=
              normalizedPairDerives
                leftNormal rightNormal
                leftPenultimate leftFinal
                leftNodup rightNodup normalMem
            exact leftDerivation.trans <|
              middle.trans rightDerivation.symm

/-- Completeness of the corrected basis for the intersection of the two
embedded lower-order identity theories. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (s5_303Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup)
    (s5_83Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derives_of_signatures
    (SemigroupBasis.CoRoots.S5_303.valid_signature
      identity s5_303Valid)
    (SemigroupBasis.CoRoots.S5_83Factors.S5_83.valid_signature
      identity s5_83Valid)

/-- Unrestricted finite-basis theorem for the exact six-element target. -/
theorem basis_complete : BasisFor Recorded.table.semigroup basis := by
  refine ⟨basis_models, ?_⟩
  intro identity valid
  exact derives_of_factor_valid identity
    (s5_303Embedding.pullback_identity identity valid)
    (s5_83Embedding.pullback_identity identity valid)

end SemigroupBasis.CoRoots.Order6S6_3372CorrectedBasis

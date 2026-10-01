import SemigroupBasis.CoRoots.S5_303Invariant
import SemigroupBasis.Examples.FinalMarkerThree

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_303

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

/-- A word with an explicit prefix and its last two variables. -/
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

/-- Every permutation of the prefix before two fixed endpoint variables is
derivable from the prefix-commutation consequence. -/
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
    simpa [wordOfTerminalPair, wordOfPrefixFinal,
      Word.append_assoc, List.append_assoc] using
      derivesPrefixContraction
        (Word.singleton x)
        (wordOfTerminalPair
          (stem.erase x) penultimate final)
  exact
    (derivesPrefixPermutation
      sourcePermutation penultimate final).trans <|
      contraction.trans <|
        derivesPrefixPermutation expose.symm penultimate final

/-- Sort-insensitive duplicate deletion in the prefix before the two endpoint
positions. -/
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

private theorem derivesRotateWithPrefix :
    ∀ (stem : List Nat) (left right : Nat),
      Derives basis
        (wordOfPrefixFinal (stem ++ [left, right]) left)
        (wordOfPrefixFinal (stem ++ [right, left]) left)
  | [], left, right => by
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        derivesRotate
          (Word.singleton left) (Word.singleton right)
  | x :: xs, left, right => by
      simpa [wordOfPrefixFinal, List.append_assoc] using
        Derives.prepend (Word.singleton x)
          (derivesRotateWithPrefix xs left right)

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

private theorem derivesPairContractionWithPrefix :
    ∀ (stem : List Nat) (penultimate final : Nat),
      Derives basis
        (wordOfTerminalPair
          (stem ++ [penultimate]) penultimate final)
        (wordOfTerminalPair stem penultimate final)
  | [], penultimate, final => by
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
        Word.append_assoc] using
        derivesPrefixContraction
          (Word.singleton penultimate) (Word.singleton final)
  | x :: xs, penultimate, final => by
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
        List.append_assoc] using
        Derives.prepend (Word.singleton x)
          (derivesPairContractionWithPrefix xs penultimate final)

private theorem derivesMakeRepeatedFinal
    (stem : List Nat) (penultimate final : Nat)
    (repeated :
      final = penultimate ∨ final ∈ stem) :
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
    have rotated :
        Derives basis
          (wordOfTerminalPair
            (stem.erase final ++ [final])
            penultimate final)
          (wordOfTerminalPair
            (stem.erase final ++ [penultimate])
            final final) := by
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
        Word.append_assoc, List.append_assoc] using
        derivesRotateWithPrefix
          (stem.erase final) final penultimate
    refine
      ⟨stem.erase final ++ [penultimate],
        arranged.trans rotated, ?_⟩
    intro z
    simp only [List.mem_append, List.mem_singleton]
    by_cases zFinal : z = final
    · subst z
      simp [finalMember]
    · rw [List.mem_erase_of_ne zFinal]
      simp [zFinal, or_assoc, or_left_comm, or_comm]

/-- Repeated-final normalization. The prefix is duplicate-free, omits the
final marker, and contains every other support variable exactly once. -/
theorem derivesRepeatedFinalNormal
    (stem : List Nat) (penultimate final : Nat)
    (repeated :
      final = penultimate ∨ final ∈ stem) :
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

/-- Unique-final normalization. The prefix is duplicate-free, omits both
endpoint variables, and contains every other support variable once. -/
theorem derivesUniqueFinalNormal
    (stem : List Nat) (penultimate final : Nat)
    (unique :
      final ≠ penultimate ∧ final ∉ stem) :
    ∃ normalPrefix,
      Derives basis
        (wordOfTerminalPair stem penultimate final)
        (wordOfTerminalPair normalPrefix penultimate final) ∧
      normalPrefix.Nodup ∧
      penultimate ∉ normalPrefix ∧
      final ∉ normalPrefix ∧
      (∀ z,
        z ∈ normalPrefix ↔
          (z ∈ stem ∨ z = penultimate ∨ z = final) ∧
            z ≠ penultimate ∧ z ≠ final) := by
  let reduced := finalMarkerPrefixReduce stem
  have normalize :
      Derives basis
        (wordOfTerminalPair stem penultimate final)
        (wordOfTerminalPair reduced penultimate final) := by
    simpa [reduced] using
      derivesNormalizePrefix stem penultimate final
  by_cases penultimateMember : penultimate ∈ reduced
  · have reducedNodup : reduced.Nodup := by
      simpa [reduced] using
        finalMarkerPrefixReduce_nodup stem
    have fronted :
        reduced.Perm (penultimate :: reduced.erase penultimate) :=
      List.perm_cons_erase penultimateMember
    have penultimateAbsent :
        penultimate ∉ reduced.erase penultimate :=
      (List.nodup_cons.mp
        (fronted.nodup_iff.mp reducedNodup)).1
    have arrange :
        reduced.Perm
          (reduced.erase penultimate ++ [penultimate]) := by
      exact
        (List.perm_cons_erase penultimateMember).trans <|
          perm_cons_to_end penultimate (reduced.erase penultimate)
    have arranged :=
      derivesPrefixPermutation arrange penultimate final
    have contracted :=
      derivesPairContractionWithPrefix
        (reduced.erase penultimate) penultimate final
    refine
      ⟨reduced.erase penultimate,
        normalize.trans <| arranged.trans contracted,
        reducedNodup.erase penultimate,
        penultimateAbsent,
        ?_,
        ?_⟩
    · intro finalMember
      exact unique.2 <|
        (finalMarkerPrefixReduce_mem final stem).mp
          (List.mem_of_mem_erase finalMember)
    · intro z
      have reducedMemberIff : z ∈ reduced ↔ z ∈ stem := by
        simpa [reduced] using
          finalMarkerPrefixReduce_mem z stem
      constructor
      · intro erasedMember
        have member : z ∈ reduced :=
          List.mem_of_mem_erase erasedMember
        have different : z ≠ penultimate := by
          intro equal
          subst z
          exact penultimateAbsent erasedMember
        have prefixMember : z ∈ stem :=
          reducedMemberIff.mp member
        refine
          ⟨Or.inl prefixMember,
            different,
            ?_⟩
        intro equal
        subst z
        exact unique.2 prefixMember
      · rintro ⟨sourceMember, zNotPenultimate, zNotFinal⟩
        have prefixMember : z ∈ stem := by
          rcases sourceMember with member | equal | equal
          · exact member
          · exact False.elim (zNotPenultimate equal)
          · exact False.elim (zNotFinal equal)
        exact (List.mem_erase_of_ne zNotPenultimate).mpr <|
          reducedMemberIff.mpr prefixMember
  · refine
      ⟨reduced,
        normalize,
        finalMarkerPrefixReduce_nodup stem,
        penultimateMember,
        ?_,
        ?_⟩
    · intro finalMember
      exact unique.2 <|
        (finalMarkerPrefixReduce_mem final stem).mp finalMember
    · intro z
      rw [finalMarkerPrefixReduce_mem]
      constructor
      · intro member
        refine
          ⟨Or.inl member,
            fun equal => by
              subst z
              apply penultimateMember
              exact
                (finalMarkerPrefixReduce_mem
                  penultimate stem).mpr member,
            ?_⟩
        intro equal
        subst z
        exact unique.2 member
      · rintro ⟨sourceMember, zNotPenultimate, zNotFinal⟩
        rcases sourceMember with member | equal | equal
        · exact member
        · exact False.elim (zNotPenultimate equal)
        · exact False.elim (zNotFinal equal)

private theorem normalizedPairDerives
    (leftPrefix rightPrefix : List Nat)
    (penultimate final : Nat)
    (leftNodup : leftPrefix.Nodup)
    (rightNodup : rightPrefix.Nodup)
    (samePrefix :
      ∀ z, z ∈ leftPrefix ↔ z ∈ rightPrefix) :
    Derives basis
      (wordOfTerminalPair leftPrefix penultimate final)
      (wordOfTerminalPair rightPrefix penultimate final) :=
  derivesPrefixPermutation
    (perm_of_nodup_mem_iff leftNodup rightNodup samePrefix)
    penultimate final

/-- Constructive unrestricted normalization theorem for the complete
content plus penultimate/final invariant. -/
theorem derives_of_sameContentEndpointSignature
    {left right : Word Nat}
    (same : SameContentEndpointSignature left right) :
    Derives basis left right := by
  classical
  have leftReconstruct := terminalSplit_renderWord left
  have rightReconstruct := terminalSplit_renderWord right
  cases leftSplitEq : terminalSplit left with
  | singleton leftFinal =>
      cases rightSplitEq : terminalSplit right with
      | singleton rightFinal =>
          have rightFinalProperty :
              FinalLetter right leftFinal :=
            (same.finalLetter leftFinal).mp <| by
              simp [FinalLetter, leftSplitEq]
          have finals : rightFinal = leftFinal := by
            simpa [FinalLetter, rightSplitEq] using
              rightFinalProperty
          subst rightFinal
          rw [leftSplitEq] at leftReconstruct
          rw [rightSplitEq] at rightReconstruct
          rw [← leftReconstruct, ← rightReconstruct]
          exact Derives.refl _
      | pair rightPrefix rightPenultimate rightFinal =>
          have leftSingleton : IsSingletonWord left := by
            simp [IsSingletonWord, leftSplitEq]
          have rightSingleton := same.singleton.mp leftSingleton
          simp [IsSingletonWord, rightSplitEq] at rightSingleton
  | pair leftPrefix leftPenultimate leftFinal =>
      cases rightSplitEq : terminalSplit right with
      | singleton rightFinal =>
          have rightSingleton : IsSingletonWord right := by
            simp [IsSingletonWord, rightSplitEq]
          have leftSingleton := same.singleton.mpr rightSingleton
          simp [IsSingletonWord, leftSplitEq] at leftSingleton
      | pair rightPrefix rightPenultimate rightFinal =>
          have rightFinalProperty :
              FinalLetter right leftFinal :=
            (same.finalLetter leftFinal).mp <| by
              simp [FinalLetter, leftSplitEq]
          have finals : rightFinal = leftFinal := by
            simpa [FinalLetter, rightSplitEq] using
              rightFinalProperty
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
                  UniqueFinalPair right
                    rightPenultimate leftFinal := by
                simp [UniqueFinalPair, rightSplitEq,
                  rightParts.1, rightParts.2]
              have leftPair :=
                (same.uniqueFinalPair
                  rightPenultimate leftFinal).mpr rightPair
              have leftParts :
                  leftPenultimate = rightPenultimate ∧
                    leftFinal = leftFinal ∧
                    leftFinal ≠ leftPenultimate ∧
                    leftFinal ∉ leftPrefix := by
                simpa [UniqueFinalPair, leftSplitEq] using leftPair
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
              · have supportIff := same.support z
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
                UniqueFinalPair left
                  leftPenultimate leftFinal := by
              simp [UniqueFinalPair, leftSplitEq,
                leftUniqueParts.1, leftUniqueParts.2]
            have rightPair :=
              (same.uniqueFinalPair
                leftPenultimate leftFinal).mp leftPair
            have rightParts :
                rightPenultimate = leftPenultimate ∧
                  leftFinal = leftFinal ∧
                  leftFinal ≠ rightPenultimate ∧
                  leftFinal ∉ rightPrefix := by
              simpa [UniqueFinalPair, rightSplitEq] using rightPair
            have rightPenultimateEq :
                rightPenultimate = leftPenultimate :=
              rightParts.1
            subst rightPenultimate
            obtain
                ⟨leftNormal, leftDerivation, leftNodup,
                  leftPenultimateAbsent, leftFinalAbsent,
                  leftNormalMem⟩ :=
              derivesUniqueFinalNormal
                leftPrefix leftPenultimate leftFinal leftUniqueParts
            obtain
                ⟨rightNormal, rightDerivation, rightNodup,
                  rightPenultimateAbsent, rightFinalAbsent,
                  rightNormalMem⟩ :=
              derivesUniqueFinalNormal
                rightPrefix leftPenultimate leftFinal
                ⟨rightParts.2.2.1, rightParts.2.2.2⟩
            have normalMem :
                ∀ z, z ∈ leftNormal ↔ z ∈ rightNormal := by
              intro z
              rw [leftNormalMem, rightNormalMem]
              apply and_congr
              · have supportIff := same.support z
                rw [← terminalSplit_renderList left,
                  ← terminalSplit_renderList right,
                  leftSplitEq, rightSplitEq] at supportIff
                simpa [TerminalSplit.renderList,
                  List.append_assoc, or_assoc] using supportIff
              · exact Iff.rfl
            have middle :=
              normalizedPairDerives
                leftNormal rightNormal
                leftPenultimate leftFinal
                leftNodup rightNodup normalMem
            exact leftDerivation.trans <|
              middle.trans rightDerivation.symm

/-- Any semigroup whose valid identities preserve the exact signature has
the displayed three-law basis. -/
theorem basis_complete_of_contentEndpoint
    {carrier : Type}
    (semigroup : Semigroup carrier)
    (models : Models semigroup basis)
    (separates :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy semigroup →
          SameContentEndpointSignature
            identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derives_of_sameContentEndpointSignature
    (separates identity valid)

end SemigroupBasis.CoRoots.S5_303

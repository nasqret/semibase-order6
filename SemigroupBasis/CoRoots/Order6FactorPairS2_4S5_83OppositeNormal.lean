import SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83Opposite

namespace SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83Opposite
namespace DualNormal

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

private theorem perm_of_nodup_mem_iff :
    ∀ {xs ys : List Nat},
      xs.Nodup →
      ys.Nodup →
      (∀ z, z ∈ xs ↔ z ∈ ys) →
      xs.Perm ys
  | [], [], _, _, _ => List.Perm.refl []
  | [], y :: ys, _, _, members => by
      exact False.elim <| by
        have := (members y).2 (List.Mem.head ys)
        exact List.not_mem_nil this
  | x :: xs, [], _, _, members => by
      exact False.elim <| by
        have := (members x).1 (List.Mem.head xs)
        exact List.not_mem_nil this
  | x :: xs, y :: ys, leftNodup, rightNodup, members => by
      have xInRight : x ∈ y :: ys :=
        (members x).1 (List.Mem.head xs)
      have targetPerm : (y :: ys).Perm (x :: (y :: ys).erase x) :=
        List.perm_cons_erase xInRight
      have tailNodup : xs.Nodup :=
        (List.nodup_cons.mp leftNodup).2
      have erasedNodup : ((y :: ys).erase x).Nodup :=
        rightNodup.erase _
      have arrangedNodup :
          (x :: (y :: ys).erase x).Nodup :=
        targetPerm.nodup_iff.mp rightNodup
      have xNotInErase : x ∉ (y :: ys).erase x :=
        (List.nodup_cons.mp arrangedNodup).1
      have tailMembers :
          ∀ z, z ∈ xs ↔ z ∈ (y :: ys).erase x := by
        intro z
        have xNotInXs : x ∉ xs :=
          (List.nodup_cons.mp leftNodup).1
        by_cases equal : z = x
        · subst z
          exact iff_of_false xNotInXs xNotInErase
        · constructor
          · intro member
            have targetMember :=
              (targetPerm.mem_iff).mp <|
                (members z).1 (List.Mem.tail x member)
            simp only [List.mem_cons] at targetMember
            rcases targetMember with headEqual | tailMember
            · exact False.elim (equal headEqual)
            · exact tailMember
          · intro member
            have targetMember : z ∈ x :: (y :: ys).erase x :=
              List.Mem.tail x member
            have sourceMember :=
              (members z).2 ((targetPerm.mem_iff).mpr targetMember)
            simp only [List.mem_cons] at sourceMember
            rcases sourceMember with headEqual | tailMember
            · exact False.elim (equal headEqual)
            · exact tailMember
      exact
        (List.Perm.cons x
          (perm_of_nodup_mem_iff
            tailNodup erasedNodup tailMembers)).trans targetPerm.symm

@[simp]
private theorem wordOfPrefixFinal_append_singleton
    (stem : List Nat) (penultimate final : Nat) :
    wordOfPrefixFinal stem penultimate ++ Word.singleton final =
      wordOfPrefixFinal (stem ++ [penultimate]) final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal, toList_wordOfPrefixFinal]

/-- Every permutation strictly before two retained final variables follows
from the final-preserving prefix swap. -/
theorem derivesPrefixPermutation
    {stem1 stem2 : List Nat}
    (permutation : stem1.Perm stem2)
    (penultimate final : Nat) :
    Derives dualBasis
      (wordOfTerminalPair stem1 penultimate final)
      (wordOfTerminalPair stem2 penultimate final) := by
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
        derivesDualPrefixSwap
          (Word.singleton y) (Word.singleton x)
          (wordOfPrefixFinal xs penultimate)
          (Word.singleton final)
  | trans _ _ first second =>
      exact first.trans second

private theorem derivesDeleteLeadingPrefix
    (x : Nat) (stem : List Nat)
    (penultimate final : Nat)
    (member : x ∈ stem) :
    Derives dualBasis
      (wordOfTerminalPair (x :: stem) penultimate final)
      (wordOfTerminalPair stem penultimate final) := by
  have expose : stem.Perm (x :: stem.erase x) :=
    List.perm_cons_erase member
  have sourcePermutation :
      (x :: stem).Perm (x :: x :: stem.erase x) :=
    List.Perm.cons x expose
  have contraction :
      Derives dualBasis
        (wordOfTerminalPair
          (x :: x :: stem.erase x) penultimate final)
        (wordOfTerminalPair
          (x :: stem.erase x) penultimate final) := by
    have raw :=
      derivesDualLongContraction
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

/-- Deduplicate the freely permutable prefix while retaining both terminal
variables literally. -/
theorem derivesNormalizePrefix :
    ∀ (stem : List Nat) (penultimate final : Nat),
      Derives dualBasis
        (wordOfTerminalPair stem penultimate final)
        (wordOfTerminalPair
          (finalMarkerPrefixReduce stem) penultimate final)
  | [], penultimate, final =>
      Derives.refl _
  | x :: xs, penultimate, final => by
      have tailNormal :=
        derivesNormalizePrefix xs penultimate final
      have prefixed :
          Derives dualBasis
            (wordOfTerminalPair (x :: xs) penultimate final)
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

private theorem perm_two_to_end (a b : Nat) :
    ∀ stem : List Nat,
      (a :: b :: stem).Perm (stem ++ [a, b])
  | [] => List.Perm.refl _
  | x :: xs =>
      (List.Perm.cons a (List.Perm.swap x b xs)).trans <|
        (List.Perm.swap x a (b :: xs)).trans <|
          List.Perm.cons x (perm_two_to_end a b xs)

private theorem perm_cons_to_end (a : Nat) :
    ∀ stem : List Nat,
      (a :: stem).Perm (stem ++ [a])
  | [] => List.Perm.refl _
  | x :: xs =>
      (List.Perm.swap x a xs).trans <|
        List.Perm.cons x (perm_cons_to_end a xs)

private theorem perm_swap_at_end (a b : Nat) :
    ∀ stem : List Nat,
      (stem ++ [a, b]).Perm (stem ++ [b, a])
  | [] => List.Perm.swap b a []
  | x :: xs =>
      List.Perm.cons x (perm_swap_at_end a b xs)

private theorem derivesTransferWithPrefixAndSuffix :
    ∀ (stem : List Nat) (left right : Nat) (suffix : Word Nat),
      Derives dualBasis
        (wordOfPrefixFinal (stem ++ [left, right]) right ++ suffix)
        (wordOfPrefixFinal (stem ++ [right, left]) left ++ suffix)
  | [], left, right, suffix => by
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        derivesDualTransferWithSuffix
          (Word.singleton left) (Word.singleton right) suffix
  | x :: xs, left, right, suffix => by
      simpa [wordOfPrefixFinal, List.append_assoc,
        Word.append_assoc] using
        Derives.prepend (Word.singleton x)
          (derivesTransferWithPrefixAndSuffix
            xs left right suffix)

/-- Change a repeated penultimate marker to another supported marker without
changing the unique final variable. -/
theorem derivesRepeatedPenultimateSwitch
    (stem : List Nat) (oldMarker newMarker final : Nat)
    (oldMember : oldMarker ∈ stem)
    (newMember : newMarker ∈ stem) :
    Derives dualBasis
      (wordOfTerminalPair stem oldMarker final)
      (wordOfTerminalPair stem newMarker final) := by
  by_cases equal : oldMarker = newMarker
  · subst newMarker
    exact Derives.refl _
  · have oldInErase :
        oldMarker ∈ stem.erase newMarker :=
      (List.mem_erase_of_ne equal).mpr oldMember
    let remainder := (stem.erase newMarker).erase oldMarker
    have arrangeFront :
        stem.Perm (newMarker :: oldMarker :: remainder) := by
      exact (List.perm_cons_erase newMember).trans <|
        List.Perm.cons newMarker <| by
          simpa [remainder] using
            List.perm_cons_erase oldInErase
    have arrange :
        stem.Perm (remainder ++ [newMarker, oldMarker]) :=
      arrangeFront.trans <|
        perm_two_to_end newMarker oldMarker remainder
    have switchAtEnd :
        Derives dualBasis
          (wordOfTerminalPair
            (remainder ++ [newMarker, oldMarker])
            oldMarker final)
          (wordOfTerminalPair
            (remainder ++ [oldMarker, newMarker])
            newMarker final) := by
      have switched :=
        derivesTransferWithPrefixAndSuffix
          remainder newMarker oldMarker (Word.singleton final)
      simpa [wordOfTerminalPair,
        wordOfPrefixFinal_append_singleton,
        Word.append_assoc, List.append_assoc] using switched
    have restore :
        (remainder ++ [oldMarker, newMarker]).Perm stem :=
      (perm_swap_at_end oldMarker newMarker remainder).trans
        arrange.symm
    exact
      (derivesPrefixPermutation arrange oldMarker final).trans <|
        switchAtEnd.trans <|
          derivesPrefixPermutation restore newMarker final

private theorem derivesPowerContractionWithPrefix :
    ∀ (stem : List Nat) (marker : Nat),
      Derives dualBasis
        (wordOfTerminalPair (stem ++ [marker]) marker marker)
        (wordOfTerminalPair stem marker marker)
  | [], marker => by
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
        Word.append_assoc] using
        derivesDualPowerContraction (Word.singleton marker)
  | x :: xs, marker => by
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
        List.append_assoc] using
        Derives.prepend (Word.singleton x)
          (derivesPowerContractionWithPrefix xs marker)

private theorem derivesRotateWithPrefix :
    ∀ (stem : List Nat) (left right : Nat),
      Derives dualBasis
        (wordOfPrefixFinal (stem ++ [left, right]) left)
        (wordOfPrefixFinal (stem ++ [right, left]) left)
  | [], left, right => by
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        derivesDualRotate (Word.singleton left) (Word.singleton right)
  | x :: xs, left, right => by
      simpa [wordOfPrefixFinal, List.append_assoc] using
        Derives.prepend (Word.singleton x)
          (derivesRotateWithPrefix xs left right)

private theorem derivesMakeRepeatedFinal
    (stem : List Nat) (penultimate final : Nat)
    (repeated : final = penultimate ∨ final ∈ stem) :
    ∃ repeatedPrefix,
      Derives dualBasis
        (wordOfTerminalPair stem penultimate final)
        (wordOfTerminalPair repeatedPrefix final final) ∧
      (∀ z,
        z ∈ repeatedPrefix ∨ z = final ↔
          z ∈ stem ∨ z = penultimate ∨ z = final) := by
  rcases repeated with equal | finalMember
  · subst penultimate
    exact ⟨stem, Derives.refl _, fun z => by simp [or_assoc]⟩
  · by_cases equal : final = penultimate
    · subst penultimate
      exact ⟨stem, Derives.refl _, fun z => by simp [or_assoc]⟩
    · have arrange :
          stem.Perm (stem.erase final ++ [final]) :=
        (List.perm_cons_erase finalMember).trans <|
          perm_cons_to_end final (stem.erase final)
      have arranged :=
        derivesPrefixPermutation arrange penultimate final
      have rotated :
          Derives dualBasis
            (wordOfTerminalPair
              (stem.erase final ++ [final]) penultimate final)
            (wordOfTerminalPair
              (stem.erase final ++ [penultimate]) final final) := by
        simpa [wordOfTerminalPair, List.append_assoc] using
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

/-- Repeated-final normalization with the literal final variable fixed. The
normal prefix is duplicate-free, excludes the final marker, and contains
every other support variable exactly once. -/
theorem derivesRepeatedFinalNormal
    (stem : List Nat) (penultimate final : Nat)
    (repeated : final = penultimate ∨ final ∈ stem) :
    ∃ normalPrefix,
      Derives dualBasis
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
      Derives dualBasis
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
        reduced.Perm (reduced.erase final ++ [final]) :=
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
    constructor
    · intro erasedMember
      have member : z ∈ reduced :=
        List.mem_of_mem_erase erasedMember
      have different : z ≠ final := by
        intro equal
        subst z
        exact finalAbsent erasedMember
      exact
        ⟨(repeatedSupport z).mp
            (Or.inl (reducedMemberIff.mp member)),
          different⟩
    · rintro ⟨sourceMember, different⟩
      have repeatedMember :
          z ∈ repeatedPrefix ∨ z = final :=
        (repeatedSupport z).mpr sourceMember
      exact (List.mem_erase_of_ne different).mpr <|
        reducedMemberIff.mpr <|
          repeatedMember.resolve_right different
  · refine
      ⟨reduced,
        makeRepeated.trans normalize,
        finalMarkerPrefixReduce_nodup repeatedPrefix,
        finalMember,
        ?_⟩
    intro z
    rw [finalMarkerPrefixReduce_mem]
    constructor
    · intro member
      have sourceOrFinal :=
        (repeatedSupport z).mp (Or.inl member)
      exact ⟨sourceOrFinal, fun equal => by
        subst z
        apply finalMember
        exact (finalMarkerPrefixReduce_mem
          final repeatedPrefix).mpr member⟩
    · rintro ⟨sourceMember, different⟩
      have repeatedMember :
          z ∈ repeatedPrefix ∨ z = final :=
        (repeatedSupport z).mpr sourceMember
      exact repeatedMember.resolve_right different

private theorem normalizedUniquePairDerives
    (leftPrefix rightPrefix : List Nat)
    (penultimate final : Nat)
    (leftNodup : leftPrefix.Nodup)
    (rightNodup : rightPrefix.Nodup)
    (samePrefix :
      ∀ z, z ∈ leftPrefix ↔ z ∈ rightPrefix) :
    Derives dualBasis
      (wordOfTerminalPair leftPrefix penultimate final)
      (wordOfTerminalPair rightPrefix penultimate final) :=
  derivesPrefixPermutation
    (perm_of_nodup_mem_iff leftNodup rightNodup samePrefix)
    penultimate final

private theorem evalRightZeroPrefixFinal
    (valuation : Nat → Fin 2) :
    ∀ (stem : List Nat) (final : Nat),
      SemigroupBasis.Generated.S2_4.table.semigroup.opposite.eval
          valuation (wordOfPrefixFinal stem final) =
        valuation final
  | [], final => rfl
  | x :: xs, final => by
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton,
        evalRightZeroPrefixFinal valuation xs final]
      rfl

private theorem evalRightZeroTerminalPair
    (valuation : Nat → Fin 2)
    (stem : List Nat) (penultimate final : Nat) :
    SemigroupBasis.Generated.S2_4.table.semigroup.opposite.eval
        valuation (wordOfTerminalPair stem penultimate final) =
      valuation final := by
  exact evalRightZeroPrefixFinal valuation
    (stem ++ [penultimate]) final

/-- Constructive unrestricted normal form for the intersection of the
`S5_83` terminal-signature theory with the right-zero final-letter theory. -/
theorem derivesOfSignatureAndRightZero
    (left right : Word Nat)
    (same : SameTerminalUniqueSuffixSignature left right)
    (rightZeroValid :
      (⟨left, right⟩ : Identity Nat).SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup.opposite) :
    Derives dualBasis left right := by
  classical
  have leftReconstruct := terminalSplit_renderWord left
  have rightReconstruct := terminalSplit_renderWord right
  cases leftSplitEq : terminalSplit left with
  | singleton leftFinal =>
      cases rightSplitEq : terminalSplit right with
      | singleton rightFinal =>
          have rightUnique : UniqueFinal right leftFinal :=
            (same.uniqueFinal leftFinal).mp <| by
              simp [UniqueFinal, leftSplitEq]
          have finals : rightFinal = leftFinal := by
            simpa [UniqueFinal, rightSplitEq] using rightUnique
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
          rw [leftSplitEq] at leftReconstruct
          rw [rightSplitEq] at rightReconstruct
          change
            wordOfTerminalPair leftPrefix leftPenultimate leftFinal = left
              at leftReconstruct
          change
            wordOfTerminalPair rightPrefix rightPenultimate rightFinal = right
              at rightReconstruct
          have finals : leftFinal = rightFinal := by
            apply Decidable.byContradiction
            intro different
            let valuation : Nat → Fin 2 := fun z =>
              if z = leftFinal then 0 else 1
            have evaluated := rightZeroValid valuation
            rw [← leftReconstruct, ← rightReconstruct,
              evalRightZeroTerminalPair,
              evalRightZeroTerminalPair] at evaluated
            simp [valuation, different, Ne.symm different] at evaluated
          subst rightFinal
          rw [← leftReconstruct, ← rightReconstruct]
          by_cases leftFinalRepeated :
              leftFinal = leftPenultimate ∨
                leftFinal ∈ leftPrefix
          · have rightFinalRepeated :
                leftFinal = rightPenultimate ∨
                  leftFinal ∈ rightPrefix := by
              apply Decidable.byContradiction
              intro rightNotRepeated
              have rightParts := not_or.mp rightNotRepeated
              have rightUnique : UniqueFinal right leftFinal := by
                simp [UniqueFinal, rightSplitEq,
                  rightParts.1, rightParts.2]
              have leftUnique :=
                (same.uniqueFinal leftFinal).mpr rightUnique
              have leftParts :
                  leftFinal = leftFinal ∧
                    leftFinal ≠ leftPenultimate ∧
                    leftFinal ∉ leftPrefix := by
                simpa [UniqueFinal, leftSplitEq] using leftUnique
              rcases leftFinalRepeated with equal | member
              · exact leftParts.2.1 equal
              · exact leftParts.2.2 member
            obtain
                ⟨leftNormal, leftDerivation, leftNodup,
                  leftMarkerAbsent, leftNormalMem⟩ :=
              derivesRepeatedFinalNormal
                leftPrefix leftPenultimate leftFinal
                leftFinalRepeated
            obtain
                ⟨rightNormal, rightDerivation, rightNodup,
                  rightMarkerAbsent, rightNormalMem⟩ :=
              derivesRepeatedFinalNormal
                rightPrefix rightPenultimate leftFinal
                rightFinalRepeated
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
              normalizedUniquePairDerives
                leftNormal rightNormal leftFinal leftFinal
                leftNodup rightNodup normalMem
            exact leftDerivation.trans <|
              middle.trans rightDerivation.symm
          · have leftFinalParts := not_or.mp leftFinalRepeated
            have leftUnique : UniqueFinal left leftFinal := by
              simp [UniqueFinal, leftSplitEq,
                leftFinalParts.1, leftFinalParts.2]
            have rightUnique :=
              (same.uniqueFinal leftFinal).mp leftUnique
            have rightFinalParts :
                leftFinal = leftFinal ∧
                  leftFinal ≠ rightPenultimate ∧
                  leftFinal ∉ rightPrefix := by
              simpa [UniqueFinal, rightSplitEq] using rightUnique
            by_cases leftPenultimateRepeated :
                leftPenultimate ∈ leftPrefix
            · have rightPenultimateRepeated :
                  rightPenultimate ∈ rightPrefix := by
                apply Decidable.byContradiction
                intro rightPenultimateUnique
                have rightPair :
                    UniqueTerminalPair right
                      rightPenultimate leftFinal := by
                  simp [UniqueTerminalPair, rightSplitEq,
                    rightPenultimateUnique,
                    rightFinalParts.2.1,
                    rightFinalParts.2.2]
                have leftPair :=
                  (same.uniqueTerminalPair
                    rightPenultimate leftFinal).mpr rightPair
                have leftPairParts :
                    leftPenultimate = rightPenultimate ∧
                      leftFinal = leftFinal ∧
                      rightPenultimate ∉ leftPrefix ∧
                      leftFinal ≠ rightPenultimate ∧
                      leftFinal ∉ leftPrefix := by
                  simpa [UniqueTerminalPair, leftSplitEq] using leftPair
                exact leftPairParts.2.2.1 <| by
                  simpa [leftPairParts.1] using
                    leftPenultimateRepeated
              let leftReduced :=
                finalMarkerPrefixReduce leftPrefix
              let rightReduced :=
                finalMarkerPrefixReduce rightPrefix
              have leftNormal :=
                derivesNormalizePrefix
                  leftPrefix leftPenultimate leftFinal
              have rightNormal :=
                derivesNormalizePrefix
                  rightPrefix rightPenultimate leftFinal
              have leftOldMember :
                  leftPenultimate ∈ leftReduced :=
                (finalMarkerPrefixReduce_mem
                  leftPenultimate leftPrefix).mpr
                  leftPenultimateRepeated
              have rightOldMember :
                  rightPenultimate ∈ rightReduced :=
                (finalMarkerPrefixReduce_mem
                  rightPenultimate rightPrefix).mpr
                  rightPenultimateRepeated
              have leftMarkerInRight :
                  leftPenultimate ∈ rightReduced := by
                apply (finalMarkerPrefixReduce_mem
                  leftPenultimate rightPrefix).mpr
                have leftMember : leftPenultimate ∈ left.toList := by
                  rw [← terminalSplit_renderList left, leftSplitEq]
                  simp [TerminalSplit.renderList]
                have rightMember :=
                  (same.support leftPenultimate).mp leftMember
                rw [← terminalSplit_renderList right,
                  rightSplitEq] at rightMember
                have rightRendered :
                    leftPenultimate ∈
                      rightPrefix ++ [rightPenultimate, leftFinal] := by
                  simpa [TerminalSplit.renderList] using rightMember
                rcases List.mem_append.mp rightRendered with
                  member | terminalMember
                · exact member
                · rcases List.mem_cons.mp terminalMember with
                    equal | finalMember
                  · exact equal.symm ▸ rightPenultimateRepeated
                  · have equal : leftPenultimate = leftFinal :=
                      List.mem_singleton.mp finalMember
                    exact False.elim
                      (leftFinalParts.1 equal.symm)
              have switchedRight :=
                derivesRepeatedPenultimateSwitch
                  rightReduced rightPenultimate
                  leftPenultimate leftFinal
                  rightOldMember leftMarkerInRight
              have reducedMem :
                  ∀ z, z ∈ leftReduced ↔ z ∈ rightReduced := by
                intro z
                simp only [leftReduced, rightReduced,
                  finalMarkerPrefixReduce_mem]
                have supportIff := same.support z
                rw [← terminalSplit_renderList left,
                  ← terminalSplit_renderList right,
                  leftSplitEq, rightSplitEq] at supportIff
                by_cases zFinal : z = leftFinal
                · subst z
                  simp [leftFinalParts.2,
                    rightFinalParts.2.2]
                · simp [TerminalSplit.renderList, zFinal] at supportIff
                  constructor
                  · intro member
                    rcases supportIff.mp (Or.inl member) with
                      rightMember | equal
                    · exact rightMember
                    · exact equal.symm ▸ rightPenultimateRepeated
                  · intro member
                    rcases supportIff.mpr (Or.inl member) with
                      leftMember | equal
                    · exact leftMember
                    · exact equal.symm ▸ leftPenultimateRepeated
              have middle :=
                normalizedUniquePairDerives
                  leftReduced rightReduced
                  leftPenultimate leftFinal
                  (finalMarkerPrefixReduce_nodup leftPrefix)
                  (finalMarkerPrefixReduce_nodup rightPrefix)
                  reducedMem
              exact leftNormal.trans <|
                middle.trans <|
                  switchedRight.symm.trans rightNormal.symm
            · have leftPair :
                  UniqueTerminalPair left
                    leftPenultimate leftFinal := by
                simp [UniqueTerminalPair, leftSplitEq,
                  leftPenultimateRepeated,
                  leftFinalParts.1, leftFinalParts.2]
              have rightPair :=
                (same.uniqueTerminalPair
                  leftPenultimate leftFinal).mp leftPair
              have rightPairParts :
                  rightPenultimate = leftPenultimate ∧
                    leftFinal = leftFinal ∧
                    leftPenultimate ∉ rightPrefix ∧
                    leftFinal ≠ leftPenultimate ∧
                    leftFinal ∉ rightPrefix := by
                simpa [UniqueTerminalPair, rightSplitEq] using rightPair
              have rightPenultimateEq :
                  rightPenultimate = leftPenultimate :=
                rightPairParts.1
              subst rightPenultimate
              let leftReduced :=
                finalMarkerPrefixReduce leftPrefix
              let rightReduced :=
                finalMarkerPrefixReduce rightPrefix
              have leftNormal :=
                derivesNormalizePrefix
                  leftPrefix leftPenultimate leftFinal
              have rightNormal :=
                derivesNormalizePrefix
                  rightPrefix leftPenultimate leftFinal
              have reducedMem :
                  ∀ z, z ∈ leftReduced ↔ z ∈ rightReduced := by
                intro z
                simp only [leftReduced, rightReduced,
                  finalMarkerPrefixReduce_mem]
                have supportIff := same.support z
                rw [← terminalSplit_renderList left,
                  ← terminalSplit_renderList right,
                  leftSplitEq, rightSplitEq] at supportIff
                by_cases zPen : z = leftPenultimate
                · subst z
                  simp [leftPenultimateRepeated,
                    rightPairParts.2.2.1]
                · by_cases zFinal : z = leftFinal
                  · subst z
                    simp [leftFinalParts.2,
                      rightPairParts.2.2.2.2]
                  · simp [TerminalSplit.renderList,
                      List.append_assoc, zPen, zFinal] at supportIff
                    exact supportIff
              have middle :=
                normalizedUniquePairDerives
                  leftReduced rightReduced
                  leftPenultimate leftFinal
                  (finalMarkerPrefixReduce_nodup leftPrefix)
                  (finalMarkerPrefixReduce_nodup rightPrefix)
                  reducedMem
              exact leftNormal.trans <|
                middle.trans rightNormal.symm

theorem dualCompleteS5_83
    (identity : Identity Nat)
    (rightZeroValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup.opposite)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup) :
    Derives dualBasis identity.lhs identity.rhs :=
  derivesOfSignatureAndRightZero identity.lhs identity.rhs
    (SemigroupBasis.CoRoots.S5_83Factors.S5_83.valid_signature
      identity s5Valid)
    rightZeroValid

theorem dualCompleteS5_84
    (identity : Identity Nat)
    (rightZeroValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup.opposite)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup) :
    Derives dualBasis identity.lhs identity.rhs :=
  derivesOfSignatureAndRightZero identity.lhs identity.rhs
    (SemigroupBasis.CoRoots.S5_83Factors.S5_84.valid_signature
      identity s5Valid)
    rightZeroValid

def dualIntersectionS5_83 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup
      dualBasis where
  leftModels := modelsRightZero
  rightModels := modelsS5_83
  complete := dualCompleteS5_83

def dualIntersectionS5_84 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup
      dualBasis where
  leftModels := modelsRightZero
  rightModels := modelsS5_84
  complete := dualCompleteS5_84

private theorem modelsLeftZero :
    Models SemigroupBasis.Generated.S2_4.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    intro valuation <;> rfl

private theorem modelsS5_83Opposite :
    Models
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite
      basis := by
  rw [← reversedDualBasis_eq_basis]
  exact modelsS5_83.oppositeReversed

private theorem modelsS5_84Opposite :
    Models
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite
      basis := by
  rw [← reversedDualBasis_eq_basis]
  exact modelsS5_84.oppositeReversed

private theorem reverseCompleteS5_83
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite) :
    Derives basis identity.lhs identity.rhs := by
  have leftReversed :
      identity.reversed.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup.opposite :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity.reversed
      SemigroupBasis.Generated.S2_4.table.semigroup).mpr <| by
        simpa using leftValid
  have rightReversed :
      identity.reversed.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup).mp
        rightValid
  have dualDerivation :=
    dualCompleteS5_83 identity.reversed leftReversed rightReversed
  simpa [Identity.reversed, reversedDualBasis_eq_basis] using
    dualDerivation.reverse

private theorem reverseCompleteS5_84
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite) :
    Derives basis identity.lhs identity.rhs := by
  have leftReversed :
      identity.reversed.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup.opposite :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity.reversed
      SemigroupBasis.Generated.S2_4.table.semigroup).mpr <| by
        simpa using leftValid
  have rightReversed :
      identity.reversed.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup).mp
        rightValid
  have dualDerivation :=
    dualCompleteS5_84 identity.reversed leftReversed rightReversed
  simpa [Identity.reversed, reversedDualBasis_eq_basis] using
    dualDerivation.reverse

/-- Unrestricted intersection basis for the `S2_4` and `S5_83^op` route. -/
def intersectionS5_83Opposite :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite
      basis where
  leftModels := modelsLeftZero
  rightModels := modelsS5_83Opposite
  complete := reverseCompleteS5_83

/-- Unrestricted intersection basis for the `S2_4` and `S5_84^op` route. -/
def intersectionS5_84Opposite :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite
      basis where
  leftModels := modelsLeftZero
  rightModels := modelsS5_84Opposite
  complete := reverseCompleteS5_84

theorem basisForS5_83Opposite
    {carrier : Type}
    {semigroup : Semigroup carrier}
    (pair : SubdirectPair semigroup
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite) :
    BasisFor semigroup basis :=
  intersectionS5_83Opposite.basisFor pair

theorem basisForS5_84Opposite
    {carrier : Type}
    {semigroup : Semigroup carrier}
    (pair : SubdirectPair semigroup
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite) :
    BasisFor semigroup basis :=
  intersectionS5_84Opposite.basisFor pair

end DualNormal
end SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83Opposite

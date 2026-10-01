import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_83Invariant

namespace SemigroupBasis.CoRoots.S5_83

open SemigroupBasis
open SemigroupBasis.Examples

/-- A word with an explicit stem and its last two variables. -/
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

@[simp]
theorem terminalSplit_pair_renderWord
    (stem : List Nat) (penultimate final : Nat) :
    (TerminalSplit.pair stem penultimate final).renderWord =
      wordOfTerminalPair stem penultimate final := rfl

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

/-- Every permutation of the stem before two fixed terminal variables is
derivable. The swap step is exactly `xyzt = yxzt`. -/
theorem derivesPrefixPermutation
    {stem₁ stem₂ : List Nat}
    (permutation : stem₁.Perm stem₂)
    (penultimate final : Nat) :
    Derives basis
      (wordOfTerminalPair stem₁ penultimate final)
      (wordOfTerminalPair stem₂ penultimate final) := by
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
      derivesLongContraction
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

/-- Deduplicate the commutative stem, retaining one occurrence of every
supported stem variable. -/
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

private theorem derivesTransferWithPrefix :
    ∀ (stem : List Nat) (left right : Nat),
      Derives basis
        (wordOfPrefixFinal (stem ++ [left, right]) right)
        (wordOfPrefixFinal (stem ++ [right, left]) left)
  | [], left, right => by
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        derivesTransfer
          (Word.singleton left) (Word.singleton right)
  | x :: xs, left, right => by
      simpa [wordOfPrefixFinal, List.append_assoc] using
        Derives.prepend (Word.singleton x)
          (derivesTransferWithPrefix xs left right)

private theorem derivesCopyWithPrefix :
    ∀ (stem : List Nat) (left right : Nat),
      Derives basis
        (wordOfPrefixFinal (stem ++ [left, right]) left)
        (wordOfPrefixFinal (stem ++ [left, right]) right)
  | [], left, right => by
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        derivesCopy
          (Word.singleton left) (Word.singleton right)
  | x :: xs, left, right => by
      simpa [wordOfPrefixFinal, List.append_assoc] using
        Derives.prepend (Word.singleton x)
          (derivesCopyWithPrefix xs left right)

/-- If the penultimate variable already occurs in the stem, its repeated
marker can be changed to any other stem variable while the unique final
variable stays fixed. -/
theorem derivesRepeatedPenultimateSwitch
    (stem : List Nat) (oldMarker newMarker final : Nat)
    (oldMember : oldMarker ∈ stem)
    (newMember : newMarker ∈ stem) :
    Derives basis
      (wordOfTerminalPair stem oldMarker final)
      (wordOfTerminalPair stem newMarker final) := by
  by_cases equal : oldMarker = newMarker
  · subst newMarker
    exact Derives.refl _
  · have oldInErase :
        oldMarker ∈ stem.erase newMarker := by
      exact (List.mem_erase_of_ne equal).mpr oldMember
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
        Derives basis
          (wordOfTerminalPair
            (remainder ++ [newMarker, oldMarker])
            oldMarker final)
          (wordOfTerminalPair
            (remainder ++ [oldMarker, newMarker])
            newMarker final) := by
      have switched :=
        Derives.appendRight
          (derivesTransferWithPrefix
            remainder newMarker oldMarker)
          (Word.singleton final)
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
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
    (repeated :
      final = penultimate ∨ final ∈ stem) :
    ∃ repeatedPrefix marker,
      Derives basis
        (wordOfTerminalPair stem penultimate final)
        (wordOfTerminalPair repeatedPrefix marker marker) ∧
      (∀ z,
        z ∈ repeatedPrefix ∨ z = marker ↔
          z ∈ stem ∨ z = penultimate ∨ z = final) := by
  rcases repeated with equal | finalMember
  · subst penultimate
    refine ⟨stem, final, Derives.refl _, ?_⟩
    intro z
    simp [or_assoc]
  · by_cases equal : final = penultimate
    · subst penultimate
      refine ⟨stem, final, Derives.refl _, ?_⟩
      intro z
      simp [or_assoc]
    · have arrangeDirect :
          stem.Perm (stem.erase final ++ [final]) := by
        exact
          (List.perm_cons_erase finalMember).trans <|
            perm_cons_to_end final (stem.erase final)
      have arranged :=
        derivesPrefixPermutation
          arrangeDirect penultimate final
      have copied :
          Derives basis
            (wordOfTerminalPair
              (stem.erase final ++ [final])
              penultimate final)
            (wordOfTerminalPair
              (stem.erase final ++ [final])
              penultimate penultimate) := by
        simpa [wordOfTerminalPair, wordOfPrefixFinal,
          Word.append_assoc, List.append_assoc] using
          derivesCopyWithPrefix
            (stem.erase final) final penultimate
      refine
        ⟨stem.erase final ++ [final], penultimate,
          arranged.trans copied, ?_⟩
      intro z
      simp only [List.mem_append, List.mem_singleton]
      by_cases zFinal : z = final
      · subst z
        simp [finalMember]
      · rw [List.mem_erase_of_ne zFinal]
        simp [zFinal, or_assoc, or_left_comm, or_comm]

private theorem derivesSwitchRepeatedFinal
    (stem : List Nat) (oldMarker newMarker : Nat)
    (newMember : newMarker ∈ stem) :
    ∃ switchedPrefix,
      Derives basis
        (wordOfTerminalPair stem oldMarker oldMarker)
        (wordOfTerminalPair switchedPrefix newMarker newMarker) ∧
      (∀ z,
        z ∈ switchedPrefix ∨ z = newMarker ↔
          z ∈ stem ∨ z = oldMarker) := by
  by_cases equal : oldMarker = newMarker
  · subst newMarker
    exact ⟨stem, Derives.refl _, fun _ => Iff.rfl⟩
  · have arrange :
        stem.Perm (stem.erase newMarker ++ [newMarker]) := by
      exact
        (List.perm_cons_erase newMember).trans <|
          perm_cons_to_end newMarker (stem.erase newMarker)
    have arranged :=
      derivesPrefixPermutation arrange oldMarker oldMarker
    have switched :
        Derives basis
          (wordOfTerminalPair
            (stem.erase newMarker ++ [newMarker])
            oldMarker oldMarker)
          (wordOfTerminalPair
            (stem.erase newMarker ++ [oldMarker])
            newMarker newMarker) := by
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
        Word.append_assoc, List.append_assoc] using
        derivesTransferWithPrefix
          (stem.erase newMarker) newMarker oldMarker
    refine
      ⟨stem.erase newMarker ++ [oldMarker],
        arranged.trans switched, ?_⟩
    intro z
    simp only [List.mem_append, List.mem_singleton]
    by_cases zNew : z = newMarker
    · subst z
      simp [newMember]
    · rw [List.mem_erase_of_ne zNew]
      simp [zNew, or_assoc, or_left_comm, or_comm]

/-- Repeated-final normalization. The chosen marker may be any supported
variable. The returned stem is duplicate-free, excludes that marker, and
contains every other support variable exactly once. -/
theorem derivesRepeatedFinalNormal
    (stem : List Nat) (penultimate final marker : Nat)
    (repeated :
      final = penultimate ∨ final ∈ stem)
    (markerSupported :
      marker ∈ stem ∨ marker = penultimate ∨ marker = final) :
    ∃ normalPrefix,
      Derives basis
        (wordOfTerminalPair stem penultimate final)
        (wordOfTerminalPair normalPrefix marker marker) ∧
      normalPrefix.Nodup ∧
      marker ∉ normalPrefix ∧
      (∀ z,
        z ∈ normalPrefix ↔
          (z ∈ stem ∨ z = penultimate ∨ z = final) ∧
            z ≠ marker) := by
  obtain ⟨repeatedPrefix, oldMarker, makeRepeated, repeatedSupport⟩ :=
    derivesMakeRepeatedFinal stem penultimate final repeated
  have markerInRepeated :
      marker ∈ repeatedPrefix ∨ marker = oldMarker :=
    (repeatedSupport marker).mpr markerSupported
  have switchedResult :
      ∃ switchedPrefix,
        Derives basis
          (wordOfTerminalPair repeatedPrefix oldMarker oldMarker)
          (wordOfTerminalPair switchedPrefix marker marker) ∧
        (∀ z,
          z ∈ switchedPrefix ∨ z = marker ↔
            z ∈ repeatedPrefix ∨ z = oldMarker) := by
    by_cases markerOld : marker = oldMarker
    · subst marker
      exact
        ⟨repeatedPrefix, Derives.refl _,
          fun z => by simp⟩
    · have markerMember : marker ∈ repeatedPrefix :=
        markerInRepeated.resolve_right markerOld
      exact
        derivesSwitchRepeatedFinal
          repeatedPrefix oldMarker marker markerMember
  obtain ⟨switchedPrefix, switchRepeated, switchedSupport⟩ :=
    switchedResult
  let reduced := finalMarkerPrefixReduce switchedPrefix
  have normalize :
      Derives basis
        (wordOfTerminalPair switchedPrefix marker marker)
        (wordOfTerminalPair reduced marker marker) := by
    simpa [reduced] using
      derivesNormalizePrefix switchedPrefix marker marker
  by_cases markerMember : marker ∈ reduced
  · have reducedNodup : reduced.Nodup := by
      simpa [reduced] using
        finalMarkerPrefixReduce_nodup switchedPrefix
    have fronted :
        reduced.Perm (marker :: reduced.erase marker) :=
      List.perm_cons_erase markerMember
    have markerAbsent : marker ∉ reduced.erase marker :=
      (List.nodup_cons.mp
        (fronted.nodup_iff.mp reducedNodup)).1
    have arrange :
        reduced.Perm (reduced.erase marker ++ [marker]) := by
      exact
        (List.perm_cons_erase markerMember).trans <|
          perm_cons_to_end marker (reduced.erase marker)
    have arranged :=
      derivesPrefixPermutation arrange marker marker
    have contracted :=
      derivesPowerContractionWithPrefix
        (reduced.erase marker) marker
    refine
      ⟨reduced.erase marker,
        makeRepeated.trans <|
          switchRepeated.trans <|
            normalize.trans <| arranged.trans contracted,
        reducedNodup.erase marker,
        markerAbsent,
        ?_⟩
    intro z
    have reducedMemberIff :
        z ∈ reduced ↔ z ∈ switchedPrefix := by
      simpa [reduced] using
        finalMarkerPrefixReduce_mem z switchedPrefix
    have switchedIff := switchedSupport z
    have repeatedIff := repeatedSupport z
    constructor
    · intro erasedMember
      have member : z ∈ reduced :=
        List.mem_of_mem_erase erasedMember
      have different : z ≠ marker := by
        intro equal
        subst z
        exact markerAbsent erasedMember
      exact
        ⟨repeatedIff.mp
            (switchedIff.mp (Or.inl (reducedMemberIff.mp member))),
          different⟩
    · rintro ⟨sourceMember, different⟩
      have switchedMember :
          z ∈ switchedPrefix ∨ z = marker :=
        switchedIff.mpr (repeatedIff.mpr sourceMember)
      rcases switchedMember with member | equal
      · exact
          (List.mem_erase_of_ne different).mpr
            (reducedMemberIff.mpr member)
      · exact False.elim (different equal)
  · refine
      ⟨reduced,
        makeRepeated.trans <|
          switchRepeated.trans normalize,
        finalMarkerPrefixReduce_nodup switchedPrefix,
        markerMember,
        ?_⟩
    intro z
    rw [finalMarkerPrefixReduce_mem]
    have switchedIff := switchedSupport z
    have repeatedIff := repeatedSupport z
    constructor
    · intro member
      have sourceOrMarker :=
        repeatedIff.mp (switchedIff.mp (Or.inl member))
      exact
        ⟨sourceOrMarker, fun equal => by
          subst z
          apply markerMember
          exact
            (finalMarkerPrefixReduce_mem
              marker switchedPrefix).mpr member⟩
    · rintro ⟨sourceMember, different⟩
      have switchedMember :
          z ∈ switchedPrefix ∨ z = marker :=
        switchedIff.mpr (repeatedIff.mpr sourceMember)
      exact switchedMember.resolve_right different

private theorem normalizedUniquePairDerives
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

/-- Constructive unrestricted normalization theorem for the exact invariant. -/
theorem derives_of_sameTerminalUniqueSuffixSignature
    (left right : Word Nat)
    (same :
      SameTerminalUniqueSuffixSignature left right) :
    Derives basis left right := by
  classical
  have leftReconstruct := terminalSplit_renderWord left
  have rightReconstruct := terminalSplit_renderWord right
  cases leftSplitEq : terminalSplit left with
  | singleton leftFinal =>
      cases rightSplitEq : terminalSplit right with
      | singleton rightFinal =>
          have rightUnique :
              UniqueFinal right leftFinal :=
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
          rw [← leftReconstruct, ← rightReconstruct]
          by_cases leftFinalRepeated :
              leftFinal = leftPenultimate ∨
                leftFinal ∈ leftPrefix
          · have rightFinalRepeated :
                rightFinal = rightPenultimate ∨
                  rightFinal ∈ rightPrefix := by
              apply Decidable.byContradiction
              intro rightNotRepeated
              have rightParts := not_or.mp rightNotRepeated
              have rightUnique :
                  UniqueFinal right rightFinal := by
                simp [UniqueFinal, rightSplitEq,
                  rightParts.1, rightParts.2]
              have leftUnique :=
                (same.uniqueFinal rightFinal).mpr rightUnique
              have leftParts :
                  leftFinal = rightFinal ∧
                    leftFinal ≠ leftPenultimate ∧
                    leftFinal ∉ leftPrefix := by
                simpa [UniqueFinal, leftSplitEq] using leftUnique
              rcases leftFinalRepeated with equal | member
              · exact leftParts.2.1 equal
              · exact leftParts.2.2 member
            have markerSupportedRight :
                leftFinal ∈ rightPrefix ∨
                  leftFinal = rightPenultimate ∨
                  leftFinal = rightFinal := by
              have leftMember :
                  leftFinal ∈
                    (TerminalSplit.pair
                      leftPrefix leftPenultimate leftFinal).renderList := by
                simp [TerminalSplit.renderList]
              have inLeft : leftFinal ∈ left.toList := by
                rw [← terminalSplit_renderList left, leftSplitEq]
                exact leftMember
              have inRight := (same.support leftFinal).mp inLeft
              rw [← terminalSplit_renderList right, rightSplitEq] at inRight
              simpa [TerminalSplit.renderList, List.append_assoc,
                or_assoc] using inRight
            obtain
                ⟨leftNormal, leftDerivation, leftNodup,
                  leftMarkerAbsent, leftNormalMem⟩ :=
              derivesRepeatedFinalNormal
                leftPrefix leftPenultimate leftFinal leftFinal
                leftFinalRepeated (Or.inr (Or.inr rfl))
            obtain
                ⟨rightNormal, rightDerivation, rightNodup,
                  rightMarkerAbsent, rightNormalMem⟩ :=
              derivesRepeatedFinalNormal
                rightPrefix rightPenultimate rightFinal leftFinal
                rightFinalRepeated markerSupportedRight
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
            have leftUnique :
                UniqueFinal left leftFinal := by
              simp [UniqueFinal, leftSplitEq,
                leftFinalParts.1, leftFinalParts.2]
            have rightUnique :=
              (same.uniqueFinal leftFinal).mp leftUnique
            have rightFinalParts :
                rightFinal = leftFinal ∧
                  rightFinal ≠ rightPenultimate ∧
                  rightFinal ∉ rightPrefix := by
              simpa [UniqueFinal, rightSplitEq] using rightUnique
            have rightFinalEq : rightFinal = leftFinal :=
              rightFinalParts.1
            subst rightFinal
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
                  leftPenultimate ∈ leftReduced := by
                exact
                  (finalMarkerPrefixReduce_mem
                    leftPenultimate leftPrefix).mpr
                    leftPenultimateRepeated
              have rightOldMember :
                  rightPenultimate ∈ rightReduced := by
                exact
                  (finalMarkerPrefixReduce_mem
                    rightPenultimate rightPrefix).mpr
                    rightPenultimateRepeated
              have leftMarkerInRight :
                  leftPenultimate ∈ rightReduced := by
                apply
                  (finalMarkerPrefixReduce_mem
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
                  rightPenultimate = leftPenultimate := rightPairParts.1
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

/-- Any semigroup whose valid identities preserve the exact signature has
the displayed four-law basis. -/
theorem basis_complete_of_terminalUniqueSuffix
    {carrier : Type}
    (semigroup : Semigroup carrier)
    (models : Models semigroup basis)
    (separates :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy semigroup →
          SameTerminalUniqueSuffixSignature
            identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derives_of_sameTerminalUniqueSuffixSignature
    identity.lhs identity.rhs (separates identity valid)

end SemigroupBasis.CoRoots.S5_83

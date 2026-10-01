import SemigroupBasis.CoRoots.S5_240Invariant
import SemigroupBasis.Examples.FinalMarkerThree

namespace SemigroupBasis.CoRoots.S5_240

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
derivable from `xyzt = yxzt`. -/
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

private theorem derivesMarkerSwitchWithPrefix :
    ∀ (stem : List Nat) (left right : Nat),
      Derives basis
        (wordOfPrefixFinal (stem ++ [left, right]) right)
        (wordOfPrefixFinal (stem ++ [right, left]) left)
  | [], left, right => by
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        derivesMarkerSwitch
          (Word.singleton left) (Word.singleton right)
  | x :: xs, left, right => by
      simpa [wordOfPrefixFinal, List.append_assoc] using
        Derives.prepend (Word.singleton x)
          (derivesMarkerSwitchWithPrefix xs left right)

/-- If the penultimate variable already occurs in the prefix, its repeated
marker can be changed to any other prefix variable while the simple final
variable remains fixed. -/
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
          (derivesMarkerSwitchWithPrefix
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

private theorem derivesTerminalCollapseWithPrefix :
    ∀ (stem : List Nat) (penultimate final : Nat),
      Derives basis
        (wordOfTerminalPair
          (stem ++ [penultimate, final]) penultimate final)
        (wordOfTerminalPair
          (stem ++ [penultimate]) final final)
  | [], penultimate, final => by
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
        Word.append_assoc] using
        derivesTerminalCollapse
          (Word.singleton penultimate)
          (Word.singleton final)
  | x :: xs, penultimate, final => by
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
        List.append_assoc] using
        Derives.prepend (Word.singleton x)
          (derivesTerminalCollapseWithPrefix
            xs penultimate final)

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

private theorem derivesMakeTerminalSquare
    (stem : List Nat) (penultimate final : Nat)
    (penultimateRepeated :
      penultimate ∈ stem ∨ final = penultimate)
    (finalRepeated :
      final = penultimate ∨ final ∈ stem) :
    ∃ squarePrefix oldMarker,
      Derives basis
        (wordOfTerminalPair stem penultimate final)
        (wordOfTerminalPair squarePrefix oldMarker oldMarker) ∧
      (∀ z,
        z ∈ squarePrefix ∨ z = oldMarker ↔
          z ∈ stem ∨ z = penultimate ∨ z = final) := by
  by_cases equal : final = penultimate
  · subst penultimate
    refine ⟨stem, final, Derives.refl _, ?_⟩
    intro z
    simp [or_assoc]
  · have penultimateMember : penultimate ∈ stem :=
      penultimateRepeated.resolve_right equal
    have finalMember : final ∈ stem :=
      finalRepeated.resolve_left equal
    have finalInErase :
        final ∈ stem.erase penultimate := by
      rw [List.mem_erase_of_ne equal]
      exact finalMember
    let remainder := (stem.erase penultimate).erase final
    have arrangeFront :
        stem.Perm (penultimate :: final :: remainder) := by
      exact (List.perm_cons_erase penultimateMember).trans <|
        List.Perm.cons penultimate <| by
          simpa [remainder] using
            List.perm_cons_erase finalInErase
    have arrange :
        stem.Perm (remainder ++ [penultimate, final]) :=
      arrangeFront.trans <|
        perm_two_to_end penultimate final remainder
    have arranged :=
      derivesPrefixPermutation arrange penultimate final
    have collapsed :=
      derivesTerminalCollapseWithPrefix
        remainder penultimate final
    refine
      ⟨remainder ++ [penultimate], final,
        arranged.trans collapsed, ?_⟩
    intro z
    have arrangedMem :
        z ∈ stem ↔ z ∈ remainder ++ [penultimate, final] :=
      arrange.mem_iff
    constructor
    · intro member
      have targetMember :
          z ∈ remainder ++ [penultimate, final] := by
        simpa [List.mem_append, or_assoc] using member
      have sourceMember := arrangedMem.mpr targetMember
      exact Or.inl sourceMember
    · intro member
      rcases member with sourceMember | equalPen | equalFinal
      · have targetMember := arrangedMem.mp sourceMember
        simpa [List.mem_append, or_assoc] using targetMember
      · subst z
        simp
      · subst z
        simp

private theorem derivesSwitchTerminalSquare
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
        derivesMarkerSwitchWithPrefix
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

/-- If both endpoint variables are repeated, normalize to a terminal square
of any chosen supported marker. The prefix contains every other support
variable exactly once. -/
theorem derivesBothRepeatedNormal
    (stem : List Nat) (penultimate final marker : Nat)
    (penultimateRepeated :
      penultimate ∈ stem ∨ final = penultimate)
    (finalRepeated :
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
  obtain ⟨squarePrefix, oldMarker, makeSquare, squareSupport⟩ :=
    derivesMakeTerminalSquare
      stem penultimate final penultimateRepeated finalRepeated
  have markerInSquare :
      marker ∈ squarePrefix ∨ marker = oldMarker :=
    (squareSupport marker).mpr markerSupported
  have switchedResult :
      ∃ switchedPrefix,
        Derives basis
          (wordOfTerminalPair squarePrefix oldMarker oldMarker)
          (wordOfTerminalPair switchedPrefix marker marker) ∧
        (∀ z,
          z ∈ switchedPrefix ∨ z = marker ↔
            z ∈ squarePrefix ∨ z = oldMarker) := by
    by_cases markerOld : marker = oldMarker
    · subst marker
      exact ⟨squarePrefix, Derives.refl _, fun _ => Iff.rfl⟩
    · have markerMember : marker ∈ squarePrefix :=
        markerInSquare.resolve_right markerOld
      exact
        derivesSwitchTerminalSquare
          squarePrefix oldMarker marker markerMember
  obtain ⟨switchedPrefix, switchSquare, switchedSupport⟩ :=
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
        makeSquare.trans <|
          switchSquare.trans <|
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
    have squareIff := squareSupport z
    constructor
    · intro erasedMember
      have member : z ∈ reduced :=
        List.mem_of_mem_erase erasedMember
      have different : z ≠ marker := by
        intro equal
        subst z
        exact markerAbsent erasedMember
      exact
        ⟨squareIff.mp
            (switchedIff.mp (Or.inl (reducedMemberIff.mp member))),
          different⟩
    · rintro ⟨sourceMember, different⟩
      have switchedMember :
          z ∈ switchedPrefix ∨ z = marker :=
        switchedIff.mpr (squareIff.mpr sourceMember)
      rcases switchedMember with member | equal
      · exact
          (List.mem_erase_of_ne different).mpr
            (reducedMemberIff.mpr member)
      · exact False.elim (different equal)
  · refine
      ⟨reduced,
        makeSquare.trans <|
          switchSquare.trans normalize,
        finalMarkerPrefixReduce_nodup switchedPrefix,
        markerMember,
        ?_⟩
    intro z
    rw [finalMarkerPrefixReduce_mem]
    have switchedIff := switchedSupport z
    have squareIff := squareSupport z
    constructor
    · intro member
      have sourceOrMarker :=
        squareIff.mp (switchedIff.mp (Or.inl member))
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
        switchedIff.mpr (squareIff.mpr sourceMember)
      exact switchedMember.resolve_right different

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

/-- Constructive unrestricted normalization for the exact S5_240
endpoint-suffix signature. -/
theorem derives_of_sameEndpointSuffixSignature
    (left right : Word Nat)
    (same : SameEndpointSuffixSignature left right) :
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
          by_cases leftPenultimateSimple :
              leftPenultimate ∉ leftPrefix ∧
                leftFinal ≠ leftPenultimate
          · have leftPair :
                SimplePenultimatePair left
                  leftPenultimate leftFinal := by
              simp [SimplePenultimatePair, leftSplitEq,
                leftPenultimateSimple]
            have rightPair :=
              (same.simplePenultimatePair
                leftPenultimate leftFinal).mp leftPair
            have rightPairParts :
                rightPenultimate = leftPenultimate ∧
                  rightFinal = leftFinal ∧
                  leftPenultimate ∉ rightPrefix ∧
                  leftFinal ≠ leftPenultimate := by
              simpa [SimplePenultimatePair, rightSplitEq] using
                rightPair
            have rightPenultimateEq :
                rightPenultimate = leftPenultimate :=
              rightPairParts.1
            have rightFinalEq : rightFinal = leftFinal :=
              rightPairParts.2.1
            subst rightPenultimate
            subst rightFinal
            let leftReduced := finalMarkerPrefixReduce leftPrefix
            let rightReduced := finalMarkerPrefixReduce rightPrefix
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
              by_cases zPen : z = leftPenultimate
              · subst z
                simp [leftPenultimateSimple.1,
                  rightPairParts.2.2.1]
              · by_cases zFinal : z = leftFinal
                · subst z
                  have uniqueIff := same.uniqueFinal leftFinal
                  simp [UniqueFinal, leftSplitEq, rightSplitEq,
                    leftPenultimateSimple.2,
                    rightPairParts.2.2.2, zPen] at uniqueIff
                  constructor
                  · intro leftMember
                    apply Decidable.byContradiction
                    intro rightAbsent
                    exact (uniqueIff.mpr rightAbsent) leftMember
                  · intro rightMember
                    apply Decidable.byContradiction
                    intro leftAbsent
                    exact (uniqueIff.mp leftAbsent) rightMember
                · have supportIff := same.support z
                  rw [← terminalSplit_renderList left,
                    ← terminalSplit_renderList right,
                    leftSplitEq, rightSplitEq] at supportIff
                  simpa [TerminalSplit.renderList,
                    List.append_assoc, zPen, zFinal] using supportIff
            have middle :=
              normalizedPairDerives
                leftReduced rightReduced
                leftPenultimate leftFinal
                (finalMarkerPrefixReduce_nodup leftPrefix)
                (finalMarkerPrefixReduce_nodup rightPrefix)
                reducedMem
            exact leftNormal.trans <|
              middle.trans rightNormal.symm
          · have leftPenultimateRepeated :
                leftPenultimate ∈ leftPrefix ∨
                  leftFinal = leftPenultimate := by
              by_cases member : leftPenultimate ∈ leftPrefix
              · exact Or.inl member
              · exact Or.inr <| by
                  apply Decidable.byContradiction
                  intro different
                  exact leftPenultimateSimple ⟨member, different⟩
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
              have rightPenultimateRepeated :
                  rightPenultimate ∈ rightPrefix ∨
                    rightFinal = rightPenultimate := by
                apply Decidable.byContradiction
                intro rightNotRepeated
                have rightParts := not_or.mp rightNotRepeated
                have rightPair :
                    SimplePenultimatePair right
                      rightPenultimate rightFinal := by
                  simp [SimplePenultimatePair, rightSplitEq,
                    rightParts.1, rightParts.2]
                have leftPair :=
                  (same.simplePenultimatePair
                    rightPenultimate rightFinal).mpr rightPair
                have leftParts :
                    leftPenultimate = rightPenultimate ∧
                      leftFinal = rightFinal ∧
                      rightPenultimate ∉ leftPrefix ∧
                      rightFinal ≠ rightPenultimate := by
                  simpa [SimplePenultimatePair, leftSplitEq] using
                    leftPair
                rcases leftPenultimateRepeated with member | equal
                · exact leftParts.2.2.1 <| by
                    simpa [leftParts.1] using member
                · exact leftParts.2.2.2 <| by
                    simpa [leftParts.1, leftParts.2.1] using equal
              have markerSupportedRight :
                  leftPenultimate ∈ rightPrefix ∨
                    leftPenultimate = rightPenultimate ∨
                    leftPenultimate = rightFinal := by
                have leftMember : leftPenultimate ∈ left.toList := by
                  rw [← terminalSplit_renderList left, leftSplitEq]
                  simp [TerminalSplit.renderList]
                have rightMember :=
                  (same.support leftPenultimate).mp leftMember
                rw [← terminalSplit_renderList right,
                  rightSplitEq] at rightMember
                simpa [TerminalSplit.renderList,
                  List.append_assoc, or_assoc] using rightMember
              obtain
                  ⟨leftNormal, leftDerivation, leftNodup,
                    leftMarkerAbsent, leftNormalMem⟩ :=
                derivesBothRepeatedNormal
                  leftPrefix leftPenultimate leftFinal
                  leftPenultimate
                  leftPenultimateRepeated leftFinalRepeated
                  (Or.inr (Or.inl rfl))
              obtain
                  ⟨rightNormal, rightDerivation, rightNodup,
                    rightMarkerAbsent, rightNormalMem⟩ :=
                derivesBothRepeatedNormal
                  rightPrefix rightPenultimate rightFinal
                  leftPenultimate
                  rightPenultimateRepeated rightFinalRepeated
                  markerSupportedRight
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
                  leftPenultimate leftPenultimate
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
              have leftPenultimateMember :
                  leftPenultimate ∈ leftPrefix :=
                leftPenultimateRepeated.resolve_right
                  leftFinalParts.1
              have rightPenultimateMember :
                  rightPenultimate ∈ rightPrefix := by
                apply Decidable.byContradiction
                intro rightPenultimateAbsent
                have rightPair :
                    SimplePenultimatePair right
                      rightPenultimate leftFinal := by
                  simp [SimplePenultimatePair, rightSplitEq,
                    rightPenultimateAbsent,
                    rightFinalParts.2.1]
                have leftPair :=
                  (same.simplePenultimatePair
                    rightPenultimate leftFinal).mpr rightPair
                have leftPairParts :
                    leftPenultimate = rightPenultimate ∧
                      leftFinal = leftFinal ∧
                      rightPenultimate ∉ leftPrefix ∧
                      leftFinal ≠ rightPenultimate := by
                  simpa [SimplePenultimatePair, leftSplitEq] using
                    leftPair
                exact leftPairParts.2.2.1 <| by
                  simpa [leftPairParts.1] using
                    leftPenultimateMember
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
                  leftPenultimateMember
              have rightOldMember :
                  rightPenultimate ∈ rightReduced :=
                (finalMarkerPrefixReduce_mem
                  rightPenultimate rightPrefix).mpr
                  rightPenultimateMember
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
                simp only [TerminalSplit.renderList,
                  List.mem_append, List.mem_cons,
                  List.not_mem_nil, or_false] at rightMember
                rcases rightMember with member | equal | equal
                · exact member
                · subst rightPenultimate
                  exact rightPenultimateMember
                · exact False.elim
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
                · simp [TerminalSplit.renderList,
                    List.append_assoc, zFinal,
                    leftPenultimateMember,
                    rightPenultimateMember] at supportIff
                  constructor
                  · intro leftMember
                    rcases supportIff.mp (Or.inl leftMember) with
                      rightMember | equal
                    · exact rightMember
                    · subst z
                      exact rightPenultimateMember
                  · intro rightMember
                    rcases supportIff.mpr (Or.inl rightMember) with
                      leftMember | equal
                    · exact leftMember
                    · subst z
                      exact leftPenultimateMember
              have middle :=
                normalizedPairDerives
                  leftReduced rightReduced
                  leftPenultimate leftFinal
                  (finalMarkerPrefixReduce_nodup leftPrefix)
                  (finalMarkerPrefixReduce_nodup rightPrefix)
                  reducedMem
              exact leftNormal.trans <|
                middle.trans <|
                  switchedRight.symm.trans rightNormal.symm

/-- Any semigroup whose valid identities preserve the exact endpoint-suffix
signature has the displayed three-law basis. -/
theorem basis_complete_of_endpointSuffix
    {carrier : Type}
    (semigroup : Semigroup carrier)
    (models : Models semigroup basis)
    (separates :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy semigroup →
          SameEndpointSuffixSignature
            identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derives_of_sameEndpointSuffixSignature
    identity.lhs identity.rhs (separates identity valid)

end SemigroupBasis.CoRoots.S5_240

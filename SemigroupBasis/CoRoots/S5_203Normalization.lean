import SemigroupBasis.CoRoots.S5_203

namespace SemigroupBasis.CoRoots.S5_203

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83
open DirectCompletenessArchitecture

/-- A word with an explicit stem and its last two variables. -/
def terminalPairWord
    (stem : List Nat) (penultimate final : Nat) : Word Nat :=
  wordOfPrefixFinal (stem ++ [penultimate]) final

@[simp]
theorem toList_terminalPairWord
    (stem : List Nat) (penultimate final : Nat) :
    (terminalPairWord stem penultimate final).toList =
      stem ++ [penultimate, final] := by
  simp [terminalPairWord, toList_wordOfPrefixFinal,
    List.append_assoc]

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
            have targetMember :=
              (targetPerm.mem_iff).mp <|
                (hmem z).1 (List.Mem.tail x hz)
            simp only [List.mem_cons] at targetMember
            rcases targetMember with targetHead | targetTail
            · exact False.elim (hzx targetHead)
            · exact targetTail
          · intro hz
            have targetMember : z ∈ x :: (y :: ys).erase x :=
              List.Mem.tail x hz
            have sourceMember :=
              (hmem z).2 ((targetPerm.mem_iff).mpr targetMember)
            simp only [List.mem_cons] at sourceMember
            rcases sourceMember with sourceHead | sourceTail
            · exact False.elim (hzx sourceHead)
            · exact sourceTail
      exact
        (List.Perm.cons x
          (perm_of_nodup_mem_iff
            tailNodup erasedNodup tailMem)).trans targetPerm.symm

/-- Every permutation of the stem before two fixed terminal variables is
derivable from `xyzt = yxzt`. -/
theorem derivesPrefixPermutation
    {stem₁ stem₂ : List Nat}
    (permutation : stem₁.Perm stem₂)
    (penultimate final : Nat) :
    Derives basis
      (terminalPairWord stem₁ penultimate final)
      (terminalPairWord stem₂ penultimate final) := by
  induction permutation with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      simpa [terminalPairWord, wordOfPrefixFinal,
        List.append_assoc] using
        Derives.prepend (Word.singleton x) ih
  | swap x y xs =>
      simpa [terminalPairWord, wordOfPrefixFinal,
        Word.append_assoc, List.append_assoc] using
        derivesPrefixCommutation
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
      (terminalPairWord (x :: stem) penultimate final)
      (terminalPairWord stem penultimate final) := by
  have expose : stem.Perm (x :: stem.erase x) :=
    List.perm_cons_erase member
  have sourcePermutation :
      (x :: stem).Perm (x :: x :: stem.erase x) :=
    List.Perm.cons x expose
  have contraction :
      Derives basis
        (terminalPairWord
          (x :: x :: stem.erase x) penultimate final)
        (terminalPairWord
          (x :: stem.erase x) penultimate final) := by
    have raw :=
      (derivesPrefixDuplication
        (Word.singleton x)
        (wordOfPrefixFinal (stem.erase x) penultimate)
        (Word.singleton final)).symm
    have sourceWord :
        (((Word.singleton x ++ Word.singleton x) ++
            wordOfPrefixFinal (stem.erase x) penultimate) ++
          Word.singleton final) =
          terminalPairWord
            (x :: x :: stem.erase x) penultimate final := by
      apply Word.toList_injective
      simp only [terminalPairWord, Word.toList_append,
        Word.toList_singleton, toList_wordOfPrefixFinal]
      simp [List.append_assoc]
    have targetWord :
        ((Word.singleton x ++
            wordOfPrefixFinal (stem.erase x) penultimate) ++
          Word.singleton final) =
          terminalPairWord
            (x :: stem.erase x) penultimate final := by
      apply Word.toList_injective
      simp only [terminalPairWord, Word.toList_append,
        Word.toList_singleton, toList_wordOfPrefixFinal]
      simp [List.append_assoc]
    rw [sourceWord, targetWord] at raw
    exact raw
  exact
    (derivesPrefixPermutation
      sourcePermutation penultimate final).trans <|
      contraction.trans <|
        derivesPrefixPermutation expose.symm penultimate final

/-- Deduplicate the relational stem while retaining one occurrence of every
stem variable. The two terminal positions remain fixed. -/
theorem derivesNormalizePrefix :
    ∀ (stem : List Nat) (penultimate final : Nat),
      Derives basis
        (terminalPairWord stem penultimate final)
        (terminalPairWord
          (finalMarkerPrefixReduce stem) penultimate final)
  | [], penultimate, final =>
      Derives.refl _
  | x :: xs, penultimate, final => by
      have tailNormal :=
        derivesNormalizePrefix xs penultimate final
      have prefixed :
          Derives basis
            (terminalPairWord
              (x :: xs) penultimate final)
            (terminalPairWord
              (x :: finalMarkerPrefixReduce xs)
              penultimate final) := by
        simpa [terminalPairWord, wordOfPrefixFinal,
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

/-- The repeated-final unary-support branch contracts to the canonical cube.
The hypothesis says that the stem is nonempty and contains no other marker. -/
theorem derivesRepeatedFinalUnary
    (stem : List Nat) (marker : Nat)
    (markerMember : marker ∈ stem)
    (unary : ∀ z, z ∈ stem → z = marker) :
    Derives basis
      (terminalPairWord stem marker marker)
      (terminalPairWord [marker] marker marker) := by
  let reduced := finalMarkerPrefixReduce stem
  have normalize :
      Derives basis
        (terminalPairWord stem marker marker)
        (terminalPairWord reduced marker marker) := by
    simpa [reduced] using
      derivesNormalizePrefix stem marker marker
  have reducedMem : ∀ z, z ∈ reduced ↔ z ∈ [marker] := by
    intro z
    rw [List.mem_singleton]
    constructor
    · intro member
      exact unary z <|
        (finalMarkerPrefixReduce_mem z stem).mp member
    · intro equal
      subst z
      exact
        (finalMarkerPrefixReduce_mem marker stem).mpr
          markerMember
  have permutation : reduced.Perm [marker] :=
    perm_of_nodup_mem_iff
      (finalMarkerPrefixReduce_nodup stem)
      (by simp) reducedMem
  exact normalize.trans <|
    derivesPrefixPermutation permutation marker marker

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

private theorem derivesPenultimateSwitchWithPrefix :
    ∀ (stem : List Nat) (newMarker oldMarker final : Nat),
      Derives basis
        (terminalPairWord
          (stem ++ [newMarker, oldMarker]) oldMarker final)
        (terminalPairWord
          (stem ++ [oldMarker, newMarker]) newMarker final)
  | [], newMarker, oldMarker, final => by
      simpa [terminalPairWord, wordOfPrefixFinal,
        Word.append_assoc] using
        derivesPenultimateSwitch
          (Word.singleton newMarker)
          (Word.singleton oldMarker)
          (Word.singleton final)
  | x :: xs, newMarker, oldMarker, final => by
      simpa [terminalPairWord, wordOfPrefixFinal,
        List.append_assoc] using
        Derives.prepend (Word.singleton x)
          (derivesPenultimateSwitchWithPrefix
            xs newMarker oldMarker final)

/-- When the penultimate variable already occurs in the stem, it can be
replaced by any other repeated stem marker while a unique final stays fixed. -/
theorem derivesRepeatedPenultimateSwitch
    (stem : List Nat) (oldMarker newMarker final : Nat)
    (oldMember : oldMarker ∈ stem)
    (newMember : newMarker ∈ stem) :
    Derives basis
      (terminalPairWord stem oldMarker final)
      (terminalPairWord stem newMarker final) := by
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
    have restore :
        (remainder ++ [oldMarker, newMarker]).Perm stem :=
      (perm_swap_at_end oldMarker newMarker remainder).trans
        arrange.symm
    exact
      (derivesPrefixPermutation arrange oldMarker final).trans <|
        (derivesPenultimateSwitchWithPrefix
          remainder newMarker oldMarker final).trans <|
          derivesPrefixPermutation restore newMarker final

private theorem derivesTerminalCubeWithPrefix :
    ∀ (stem : List Nat) (left right : Nat),
      Derives basis
        (terminalPairWord (stem ++ [left]) right left)
        (terminalPairWord (stem ++ [left, right]) right right)
  | [], left, right => by
      simpa [terminalPairWord, wordOfPrefixFinal,
        Word.append_assoc] using
        derivesTerminalCube
          (Word.singleton left) (Word.singleton right)
  | x :: xs, left, right => by
      simpa [terminalPairWord, wordOfPrefixFinal,
        List.append_assoc] using
        Derives.prepend (Word.singleton x)
          (derivesTerminalCubeWithPrefix xs left right)

private theorem derivesTerminalCubeSwitchWithPrefix :
    ∀ (stem : List Nat) (newMarker oldMarker : Nat),
      Derives basis
        (terminalPairWord
          (stem ++ [newMarker, oldMarker]) oldMarker oldMarker)
        (terminalPairWord
          (stem ++ [oldMarker, newMarker]) newMarker newMarker)
  | [], newMarker, oldMarker => by
      simpa [terminalPairWord, wordOfPrefixFinal,
        Word.append_assoc] using
        derivesTerminalCubeSwitch
          (Word.singleton newMarker) (Word.singleton oldMarker)
  | x :: xs, newMarker, oldMarker => by
      simpa [terminalPairWord, wordOfPrefixFinal,
        List.append_assoc] using
        Derives.prepend (Word.singleton x)
          (derivesTerminalCubeSwitchWithPrefix
            xs newMarker oldMarker)

private theorem derivesMakeTerminalCube
    (stem : List Nat) (penultimate final : Nat)
    (finalMember : final ∈ stem) :
    ∃ cubePrefix oldMarker,
      Derives basis
        (terminalPairWord stem penultimate final)
        (terminalPairWord cubePrefix oldMarker oldMarker) ∧
      oldMarker ∈ cubePrefix ∧
      (∀ z,
        z ∈ cubePrefix ↔
          z ∈ stem ∨ z = penultimate ∨ z = final) := by
  have arrange :
      stem.Perm (stem.erase final ++ [final]) :=
    (List.perm_cons_erase finalMember).trans <|
      perm_cons_to_end final (stem.erase final)
  have arranged :=
    derivesPrefixPermutation arrange penultimate final
  by_cases equal : penultimate = final
  · subst penultimate
    refine
      ⟨stem.erase final ++ [final], final,
        arranged, by simp, ?_⟩
    intro z
    have arrangedMem :
        z ∈ stem ↔ z ∈ stem.erase final ++ [final] :=
      arrange.mem_iff
    have arrangedMem' :
        z ∈ stem ↔ z ∈ stem.erase final ∨ z = final := by
      simpa only [List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] using arrangedMem
    simp only [List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · intro member
      exact Or.inl (arrangedMem'.symm.mp member)
    · intro member
      rcases member with member | equal | equal
      · exact arrangedMem'.mp member
      · exact Or.inr equal
      · exact Or.inr equal
  · have cubed :=
      derivesTerminalCubeWithPrefix
        (stem.erase final) final penultimate
    refine
      ⟨stem.erase final ++ [final, penultimate], penultimate,
        arranged.trans cubed, by simp, ?_⟩
    intro z
    have arrangedMem :
        z ∈ stem ↔ z ∈ stem.erase final ++ [final] :=
      arrange.mem_iff
    constructor
    · intro member
      simp only [List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with remainderMember | finalEq | penultimateEq
      · have arrangedMember :
            z ∈ stem.erase final ++ [final] := by
          exact List.mem_append.mpr (Or.inl remainderMember)
        exact Or.inl (arrangedMem.mpr arrangedMember)
      · exact Or.inr (Or.inr finalEq)
      · exact Or.inr (Or.inl penultimateEq)
    · intro member
      rcases member with stemMember | penultimateEq | finalEq
      · have arrangedMember := arrangedMem.mp stemMember
        rcases List.mem_append.mp arrangedMember with
          remainderMember | finalMemberAtEnd
        · exact List.mem_append.mpr (Or.inl remainderMember)
        · have finalEq' := List.mem_singleton.mp finalMemberAtEnd
          simp [finalEq']
      · simp [penultimateEq]
      · simp [finalEq]

private theorem derivesSwitchTerminalCube
    (stem : List Nat) (oldMarker newMarker : Nat)
    (oldMember : oldMarker ∈ stem)
    (newMember : newMarker ∈ stem) :
    ∃ switchedPrefix,
      Derives basis
        (terminalPairWord stem oldMarker oldMarker)
        (terminalPairWord switchedPrefix newMarker newMarker) ∧
      newMarker ∈ switchedPrefix ∧
      (∀ z, z ∈ switchedPrefix ↔ z ∈ stem) := by
  by_cases equal : oldMarker = newMarker
  · subst newMarker
    exact ⟨stem, Derives.refl _, oldMember, fun _ => Iff.rfl⟩
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
    have restore :
        (remainder ++ [oldMarker, newMarker]).Perm stem :=
      (perm_swap_at_end oldMarker newMarker remainder).trans
        arrange.symm
    refine
      ⟨remainder ++ [oldMarker, newMarker],
        (derivesPrefixPermutation arrange oldMarker oldMarker).trans <|
          derivesTerminalCubeSwitchWithPrefix
            remainder newMarker oldMarker,
        by simp, ?_⟩
    intro z
    exact restore.mem_iff

/-- Every non-doubleton repeated-final word can be normalized to a terminal
cube of any chosen supported marker. The returned stem is duplicate-free and
contains each supported variable, including the cube marker, exactly once. -/
theorem derivesRepeatedFinalNormal
    (stem : List Nat) (penultimate final marker : Nat)
    (finalMember : final ∈ stem)
    (markerSupported :
      marker ∈ stem ∨ marker = penultimate ∨ marker = final) :
    ∃ normalPrefix,
      Derives basis
        (terminalPairWord stem penultimate final)
        (terminalPairWord normalPrefix marker marker) ∧
      normalPrefix.Nodup ∧
      marker ∈ normalPrefix ∧
      (∀ z,
        z ∈ normalPrefix ↔
          z ∈ stem ∨ z = penultimate ∨ z = final) := by
  obtain
      ⟨cubePrefix, oldMarker, makeCube, oldMember, cubeSupport⟩ :=
    derivesMakeTerminalCube
      stem penultimate final finalMember
  have markerInCube : marker ∈ cubePrefix :=
    (cubeSupport marker).mpr markerSupported
  obtain
      ⟨switchedPrefix, switchCube, markerMember, switchedSupport⟩ :=
    derivesSwitchTerminalCube
      cubePrefix oldMarker marker oldMember markerInCube
  let reduced := finalMarkerPrefixReduce switchedPrefix
  have normalize :
      Derives basis
        (terminalPairWord switchedPrefix marker marker)
        (terminalPairWord reduced marker marker) := by
    simpa [reduced] using
      derivesNormalizePrefix switchedPrefix marker marker
  refine
    ⟨reduced, makeCube.trans <| switchCube.trans normalize,
      finalMarkerPrefixReduce_nodup switchedPrefix,
      (finalMarkerPrefixReduce_mem marker switchedPrefix).mpr
        markerMember, ?_⟩
  intro z
  rw [finalMarkerPrefixReduce_mem, switchedSupport, cubeSupport]

private theorem normalizedPairDerives
    (leftPrefix rightPrefix : List Nat)
    (penultimate final : Nat)
    (leftNodup : leftPrefix.Nodup)
    (rightNodup : rightPrefix.Nodup)
    (samePrefix :
      ∀ z, z ∈ leftPrefix ↔ z ∈ rightPrefix) :
    Derives basis
      (terminalPairWord leftPrefix penultimate final)
      (terminalPairWord rightPrefix penultimate final) :=
  derivesPrefixPermutation
    (perm_of_nodup_mem_iff leftNodup rightNodup samePrefix)
    penultimate final

/-- Constructive global derivation for the exact support/terminal-state
signature. This theorem is purely syntactic: it does not assert that the
catalogue table separates the signature. -/
theorem derivesOfSameSupportTerminalStateSignature
    (left right : Word Nat)
    (same : SameSupportTerminalStateSignature left right) :
    Derives basis left right := by
  classical
  have leftReconstruct := terminalSplit_renderWord left
  have rightReconstruct := terminalSplit_renderWord right
  cases leftSplitEq : terminalSplit left with
  | singleton leftFinal =>
      cases rightSplitEq : terminalSplit right with
      | singleton rightFinal =>
          have rightUnique :
              SemigroupBasis.CoRoots.S5_83.UniqueFinal
                right leftFinal :=
            (same.uniqueFinal leftFinal).mp <| by
              simp [SemigroupBasis.CoRoots.S5_83.UniqueFinal,
                leftSplitEq]
          have finals : rightFinal = leftFinal := by
            simpa [SemigroupBasis.CoRoots.S5_83.UniqueFinal,
              rightSplitEq] using rightUnique
          subst rightFinal
          rw [leftSplitEq] at leftReconstruct
          rw [rightSplitEq] at rightReconstruct
          rw [← leftReconstruct, ← rightReconstruct]
          exact Derives.refl _
      | pair rightPrefix rightPenultimate rightFinal =>
          have leftSingleton :
              SemigroupBasis.CoRoots.S5_83.IsSingletonWord left := by
            simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord,
              leftSplitEq]
          have rightSingleton := same.singleton.mp leftSingleton
          simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord,
            rightSplitEq] at rightSingleton
  | pair leftPrefix leftPenultimate leftFinal =>
      cases rightSplitEq : terminalSplit right with
      | singleton rightFinal =>
          have rightSingleton :
              SemigroupBasis.CoRoots.S5_83.IsSingletonWord right := by
            simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord,
              rightSplitEq]
          have leftSingleton := same.singleton.mpr rightSingleton
          simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord,
            leftSplitEq] at leftSingleton
      | pair rightPrefix rightPenultimate rightFinal =>
          rw [leftSplitEq] at leftReconstruct
          rw [rightSplitEq] at rightReconstruct
          rw [← leftReconstruct, ← rightReconstruct]
          by_cases leftDoubleton :
              TerminalDoubleton left leftFinal
          · have rightDoubleton :=
              (same.terminalDoubleton leftFinal).mp leftDoubleton
            have leftParts :
                leftPenultimate = leftFinal ∧
                  leftFinal ∉ leftPrefix := by
              simpa [TerminalDoubleton, leftSplitEq] using
                leftDoubleton
            have rightParts :
                rightPenultimate = leftFinal ∧
                  rightFinal = leftFinal ∧
                  leftFinal ∉ rightPrefix := by
              simpa [TerminalDoubleton, rightSplitEq] using
                rightDoubleton
            have leftPenultimateEq :
                leftPenultimate = leftFinal := leftParts.1
            have rightPenultimateEq :
                rightPenultimate = leftFinal := rightParts.1
            have rightFinalEq : rightFinal = leftFinal :=
              rightParts.2.1
            subst leftPenultimate
            subst rightPenultimate
            subst rightFinal
            let leftReduced :=
              finalMarkerPrefixReduce leftPrefix
            let rightReduced :=
              finalMarkerPrefixReduce rightPrefix
            have leftNormal :=
              derivesNormalizePrefix
                leftPrefix leftFinal leftFinal
            have rightNormal :=
              derivesNormalizePrefix
                rightPrefix leftFinal leftFinal
            have reducedMem :
                ∀ z, z ∈ leftReduced ↔ z ∈ rightReduced := by
              intro z
              simp only [leftReduced, rightReduced,
                finalMarkerPrefixReduce_mem]
              by_cases zFinal : z = leftFinal
              · subst z
                exact iff_of_false leftParts.2 rightParts.2.2
              · have supportIff := same.support z
                rw [← terminalSplit_renderList left,
                  ← terminalSplit_renderList right,
                  leftSplitEq, rightSplitEq] at supportIff
                simpa [TerminalSplit.renderList,
                  List.append_assoc, zFinal] using supportIff
            have middle :=
              normalizedPairDerives
                leftReduced rightReduced leftFinal leftFinal
                (finalMarkerPrefixReduce_nodup leftPrefix)
                (finalMarkerPrefixReduce_nodup rightPrefix)
                reducedMem
            exact leftNormal.trans <|
              middle.trans rightNormal.symm
          · by_cases leftFinalUnique :
                SemigroupBasis.CoRoots.S5_83.UniqueFinal
                  left leftFinal
            · have rightUnique :=
                (same.uniqueFinal leftFinal).mp leftFinalUnique
              have leftFinalParts :
                  leftFinal ≠ leftPenultimate ∧
                    leftFinal ∉ leftPrefix := by
                simpa [SemigroupBasis.CoRoots.S5_83.UniqueFinal,
                  leftSplitEq] using
                  leftFinalUnique
              have rightFinalParts :
                  rightFinal = leftFinal ∧
                    rightFinal ≠ rightPenultimate ∧
                    rightFinal ∉ rightPrefix := by
                simpa [SemigroupBasis.CoRoots.S5_83.UniqueFinal,
                  rightSplitEq] using rightUnique
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
                      SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair right
                        rightPenultimate leftFinal := by
                    simp [SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair,
                      rightSplitEq,
                      rightPenultimateUnique,
                      rightFinalParts.2.1,
                      rightFinalParts.2.2]
                  have leftPair :=
                    (same.uniqueTerminalPairOfUniqueFinal
                      rightPenultimate leftFinal
                      leftFinalUnique).mpr rightPair
                  have leftPairParts :
                      leftPenultimate = rightPenultimate ∧
                        leftFinal = leftFinal ∧
                        rightPenultimate ∉ leftPrefix ∧
                        leftFinal ≠ rightPenultimate ∧
                        leftFinal ∉ leftPrefix := by
                    simpa [
                      SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair,
                      leftSplitEq] using
                      leftPair
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
                  · exact equal.symm ▸ rightPenultimateRepeated
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
                  normalizedPairDerives
                    leftReduced rightReduced
                    leftPenultimate leftFinal
                    (finalMarkerPrefixReduce_nodup leftPrefix)
                    (finalMarkerPrefixReduce_nodup rightPrefix)
                    reducedMem
                exact leftNormal.trans <|
                  middle.trans <|
                    switchedRight.symm.trans rightNormal.symm
              · have leftPair :
                    SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair left
                      leftPenultimate leftFinal := by
                  simp [SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair,
                    leftSplitEq,
                    leftPenultimateRepeated,
                    leftFinalParts.1, leftFinalParts.2]
                have rightPair :=
                  (same.uniqueTerminalPairOfUniqueFinal
                    leftPenultimate leftFinal
                    leftFinalUnique).mp leftPair
                have rightPairParts :
                    rightPenultimate = leftPenultimate ∧
                      leftFinal = leftFinal ∧
                      leftPenultimate ∉ rightPrefix ∧
                      leftFinal ≠ leftPenultimate ∧
                      leftFinal ∉ rightPrefix := by
                  simpa [
                    SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair,
                    rightSplitEq] using
                    rightPair
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
                  by_cases zPenultimate : z = leftPenultimate
                  · subst z
                    simp [leftPenultimateRepeated,
                      rightPairParts.2.2.1]
                  · by_cases zFinal : z = leftFinal
                    · subst z
                      simp [leftFinalParts.2,
                        rightPairParts.2.2.2.2]
                    · simpa [TerminalSplit.renderList,
                        List.append_assoc, zPenultimate, zFinal] using
                        supportIff
                have middle :=
                  normalizedPairDerives
                    leftReduced rightReduced
                    leftPenultimate leftFinal
                    (finalMarkerPrefixReduce_nodup leftPrefix)
                    (finalMarkerPrefixReduce_nodup rightPrefix)
                    reducedMem
                exact leftNormal.trans <|
                  middle.trans rightNormal.symm
            · have leftFinalMember : leftFinal ∈ leftPrefix := by
                apply Decidable.byContradiction
                intro leftFinalAbsent
                by_cases equal : leftPenultimate = leftFinal
                · apply leftDoubleton
                  simp [TerminalDoubleton, leftSplitEq,
                    equal, leftFinalAbsent]
                · apply leftFinalUnique
                  simp [SemigroupBasis.CoRoots.S5_83.UniqueFinal,
                    leftSplitEq,
                    Ne.symm equal, leftFinalAbsent]
              have rightFinalMember : rightFinal ∈ rightPrefix := by
                apply Decidable.byContradiction
                intro rightFinalAbsent
                by_cases equal : rightPenultimate = rightFinal
                · have rightDoubleton :
                      TerminalDoubleton right rightFinal := by
                    simp [TerminalDoubleton, rightSplitEq,
                      equal, rightFinalAbsent]
                  have leftRightDoubleton :=
                    (same.terminalDoubleton rightFinal).mpr
                      rightDoubleton
                  have leftParts :
                      leftPenultimate = rightFinal ∧
                        leftFinal = rightFinal ∧
                        rightFinal ∉ leftPrefix := by
                    simpa [TerminalDoubleton, leftSplitEq] using
                      leftRightDoubleton
                  have finalEq : leftFinal = rightFinal :=
                    leftParts.2.1
                  exact leftDoubleton <|
                    finalEq.symm ▸ leftRightDoubleton
                · have rightUnique :
                      SemigroupBasis.CoRoots.S5_83.UniqueFinal
                        right rightFinal := by
                    simp [SemigroupBasis.CoRoots.S5_83.UniqueFinal,
                      rightSplitEq,
                      Ne.symm equal, rightFinalAbsent]
                  have leftRightUnique :=
                    (same.uniqueFinal rightFinal).mpr rightUnique
                  have leftParts :
                      leftFinal = rightFinal ∧
                        leftFinal ≠ leftPenultimate ∧
                        leftFinal ∉ leftPrefix := by
                    simpa [SemigroupBasis.CoRoots.S5_83.UniqueFinal,
                      leftSplitEq] using
                      leftRightUnique
                  have finalEq : leftFinal = rightFinal :=
                    leftParts.1
                  exact leftFinalUnique <|
                    finalEq.symm ▸ leftRightUnique
              have markerSupportedRight :
                  leftFinal ∈ rightPrefix ∨
                    leftFinal = rightPenultimate ∨
                    leftFinal = rightFinal := by
                have leftMember : leftFinal ∈ left.toList := by
                  rw [← terminalSplit_renderList left, leftSplitEq]
                  simp [TerminalSplit.renderList]
                have rightMember :=
                  (same.support leftFinal).mp leftMember
                rw [← terminalSplit_renderList right,
                  rightSplitEq] at rightMember
                simpa [TerminalSplit.renderList,
                  List.append_assoc, or_assoc] using rightMember
              obtain
                  ⟨leftNormal, leftDerivation, leftNodup,
                    leftMarkerMember, leftNormalMem⟩ :=
                derivesRepeatedFinalNormal
                  leftPrefix leftPenultimate leftFinal leftFinal
                  leftFinalMember (Or.inr (Or.inr rfl))
              obtain
                  ⟨rightNormal, rightDerivation, rightNodup,
                    rightMarkerMember, rightNormalMem⟩ :=
                derivesRepeatedFinalNormal
                  rightPrefix rightPenultimate rightFinal leftFinal
                  rightFinalMember markerSupportedRight
              have normalMem :
                  ∀ z, z ∈ leftNormal ↔ z ∈ rightNormal := by
                intro z
                rw [leftNormalMem, rightNormalMem]
                have supportIff := same.support z
                rw [← terminalSplit_renderList left,
                  ← terminalSplit_renderList right,
                  leftSplitEq, rightSplitEq] at supportIff
                simpa [TerminalSplit.renderList,
                  List.append_assoc, or_assoc] using supportIff
              have middle :=
                normalizedPairDerives
                  leftNormal rightNormal leftFinal leftFinal
                  leftNodup rightNodup normalMem
              exact leftDerivation.trans <|
                middle.trans rightDerivation.symm

/-- Any semigroup whose valid identities preserve the exact S5_203 signature
has the displayed ten-law basis. This conditional theorem does not discharge
the concrete catalogue table's separation obligation. -/
theorem basis_complete_of_supportTerminalState
    {carrier : Type}
    (semigroup : Semigroup carrier)
    (models : Models semigroup basis)
    (separates :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy semigroup →
          SameSupportTerminalStateSignature
            identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameSupportTerminalStateSignature
    identity.lhs identity.rhs (separates identity valid)

end SemigroupBasis.CoRoots.S5_203

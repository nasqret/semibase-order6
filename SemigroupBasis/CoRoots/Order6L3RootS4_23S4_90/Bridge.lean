import SemigroupBasis.CoRoots.Order6L3RootS4_23S4_90.GeneratedAppend
import SemigroupBasis.CoRoots.Order6L3RootS4_23S4_90.GeneratedContexts
import SemigroupBasis.CoRoots.Order6FactorPairS2S594Normal
import SemigroupBasis.Subdirect

/-!
# Unrestricted completeness for the rank-13 light root

The two factors jointly retain the first letter, every multiplicity capped at
two, every multiplicity modulo two, and a final letter exactly when that final
is simple.  The endpoint-aware threshold/parity reducer therefore leaves
canonical multiplicities in `{0,1,2,3}`.  The generated displayed-law macros
supply four-to-two contraction, protected interior permutation, and balanced
repeated-final switches.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6L3RootS4_23S4_90

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6FactorPairS2S594

private def wordOfPrefixFinal : List Nat → Nat → Word Nat
  | [], final => Word.singleton final
  | head :: tail, final => ⟨head, tail ++ [final]⟩

@[simp]
private theorem toList_wordOfPrefixFinal
    (front : List Nat) (final : Nat) :
    (wordOfPrefixFinal front final).toList = front ++ [final] := by
  cases front <;> simp [wordOfPrefixFinal, Word.toList, Word.singleton]

@[simp]
private theorem wordOfPrefixFinal_cons
    (head : Nat) (tail : List Nat) (final : Nat) :
    wordOfPrefixFinal (head :: tail) final =
      Word.singleton head ++ wordOfPrefixFinal tail final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal, toList_wordOfPrefixFinal]
  rfl

private theorem wordOfEndpoints_eq
    (initial : Nat) (middle : List Nat) (final : Nat) :
    wordOfEndpoints initial middle final =
      Word.singleton initial ++ wordOfPrefixFinal middle final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal, toList_wordOfEndpoints]
  rfl

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-! ## Kernel-green generated primitives -/

/-- Contract four consecutive copies of a nonempty block to two. -/
theorem derivesFourToTwo (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (u ++ u) := by
  simpa [Word.append_assoc] using
    (Derives.symm (derivesLaw00 u))

/-- Contract two separated endpoint pairs to one pair. -/
theorem derivesSplitEndpointContraction (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ u) ++ u) ((u ++ v) ++ u) := by
  simpa [Word.append_assoc] using derivesLaw03 u v

theorem derivesSquareFinalSwitch (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v)) (((u ++ v) ++ v) ++ u) := by
  simpa [Word.append_assoc] using derivesLaw05 u v

theorem derivesAttachmentXYYZX (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ v) ++ z) ++ u) := by
  simpa [Word.append_assoc] using derivesLaw08 u v z

/-- Adjacent nonempty blocks may be swapped strictly inside fixed nonempty
prefix and suffix contexts. -/
theorem derivesOpenInteriorSwap (u v z t : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ t)
      (((u ++ z) ++ v) ++ t) := by
  simpa [Word.append_assoc] using
    (Derives.symm (derivesLaw12 u v z t))

theorem derivesMiddlePermutation
    (initial final : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives basis
      (wordOfEndpoints initial left final)
      (wordOfEndpoints initial right final) :=
  derivesMiddlePermutationOfOpenSwap derivesOpenInteriorSwap
    initial final permutation

/-! ## Endpoint-aware threshold/parity normalization -/

private theorem derivesDeleteInteriorPair
    (initial final x : Nat) (pre reduced : List Nat)
    (countEq : reduced.count x = 3) :
    Derives basis
      (wordOfEndpoints initial (pre ++ x :: reduced) final)
      (wordOfEndpoints initial (pre ++ reduced.erase x) final) := by
  let remainder := ((reduced.erase x).erase x).erase x
  have firstErase : (reduced.erase x).count x = 2 := by
    rw [List.count_erase_self, countEq]
  have secondErase : ((reduced.erase x).erase x).count x = 1 := by
    rw [List.count_erase_self, firstErase]
  have thirdErase : remainder.count x = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, secondErase]
  have sourcePerm :
      (pre ++ x :: reduced).Perm
        (x :: x :: x :: x :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = x
    · subst tested
      simp [countEq, thirdErase]
    · simp [remainder, equal, Ne.symm equal]
  have targetPerm :
      (pre ++ reduced.erase x).Perm
        (x :: x :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = x
    · subst tested
      simp [firstErase, thirdErase]
    · simp [remainder, equal, Ne.symm equal]
  have contract :=
    Derives.appendRight
      (Derives.prepend (Word.singleton initial)
        (derivesFourToTwo (Word.singleton x)))
      (wordOfPrefixFinal (pre ++ remainder) final)
  exact Derives.trans
    (derivesMiddlePermutation initial final sourcePerm) <|
    Derives.trans
      (by
        simpa [wordOfEndpoints_eq, Word.append_assoc] using contract)
      (derivesMiddlePermutation initial final targetPerm.symm)

private theorem derivesDeleteInitialInteriorPair
    (initial final : Nat) (pre reduced : List Nat)
    (countEq : reduced.count initial = 2) :
    Derives basis
      (wordOfEndpoints initial (pre ++ initial :: reduced) final)
      (wordOfEndpoints initial (pre ++ reduced.erase initial) final) := by
  let remainder := (reduced.erase initial).erase initial
  have firstErase : (reduced.erase initial).count initial = 1 := by
    rw [List.count_erase_self, countEq]
  have secondErase : remainder.count initial = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, firstErase]
  have sourcePerm :
      (pre ++ initial :: reduced).Perm
        (initial :: initial :: initial :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = initial
    · subst tested
      simp [countEq, secondErase]
    · simp [remainder, equal, Ne.symm equal]
  have targetPerm :
      (pre ++ reduced.erase initial).Perm
        (initial :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = initial
    · subst tested
      simp [firstErase, secondErase]
    · simp [remainder, equal, Ne.symm equal]
  have contract :=
    Derives.appendRight
      (derivesFourToTwo (Word.singleton initial))
      (wordOfPrefixFinal (pre ++ remainder) final)
  exact Derives.trans
    (derivesMiddlePermutation initial final sourcePerm) <|
    Derives.trans
      (by
        simpa [wordOfEndpoints_eq, Word.append_assoc] using contract)
      (derivesMiddlePermutation initial final targetPerm.symm)

private theorem derivesDeleteFinalInteriorPair
    (initial final : Nat) (pre reduced : List Nat)
    (countEq : reduced.count final = 2) :
    Derives basis
      (wordOfEndpoints initial (pre ++ final :: reduced) final)
      (wordOfEndpoints initial (pre ++ reduced.erase final) final) := by
  let remainder := (reduced.erase final).erase final
  have firstErase : (reduced.erase final).count final = 1 := by
    rw [List.count_erase_self, countEq]
  have secondErase : remainder.count final = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, firstErase]
  have sourcePerm :
      (pre ++ final :: reduced).Perm
        ((pre ++ remainder) ++ [final, final, final]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = final
    · subst tested
      simp [countEq, secondErase]
    · simp [remainder, equal, Ne.symm equal]
  have targetPerm :
      (pre ++ reduced.erase final).Perm
        ((pre ++ remainder) ++ [final]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = final
    · subst tested
      simp [firstErase, secondErase]
    · simp [remainder, equal, Ne.symm equal]
  have contract :=
    Derives.prepend (wordOfCons initial (pre ++ remainder))
      (derivesFourToTwo (Word.singleton final))
  have contractSource :
      wordOfEndpoints initial
          ((pre ++ remainder) ++ [final, final, final]) final =
        wordOfCons initial (pre ++ remainder) ++
          (((Word.singleton final ++ Word.singleton final) ++
            Word.singleton final) ++ Word.singleton final) := by
    apply Word.toList_injective
    simp [wordOfEndpoints, wordOfCons, Word.toList,
      List.append_assoc]
  have contractTarget :
      wordOfEndpoints initial ((pre ++ remainder) ++ [final]) final =
        wordOfCons initial (pre ++ remainder) ++
          (Word.singleton final ++ Word.singleton final) := by
    apply Word.toList_injective
    simp [wordOfEndpoints, wordOfCons, Word.toList,
      List.append_assoc]
  exact Derives.trans
    (derivesMiddlePermutation initial final sourcePerm) <|
    Derives.trans
      (by
        rw [contractSource, contractTarget]
        exact contract)
      (derivesMiddlePermutation initial final targetPerm.symm)

private theorem derivesDeleteBetweenEqualEndpointsPair
    (endpoint : Nat) (pre reduced : List Nat)
    (countEq : reduced.count endpoint = 1) :
    Derives basis
      (wordOfEndpoints endpoint (pre ++ endpoint :: reduced) endpoint)
      (wordOfEndpoints endpoint (pre ++ reduced.erase endpoint) endpoint) := by
  let remainder := reduced.erase endpoint
  have remainderCount : remainder.count endpoint = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, countEq]
  have sourcePerm :
      (pre ++ endpoint :: reduced).Perm
        (endpoint :: (pre ++ remainder) ++ [endpoint]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = endpoint
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, equal, Ne.symm equal]
  have targetPerm :
      (pre ++ reduced.erase endpoint).Perm (pre ++ remainder) := by
    simp [remainder]
  have arranged :=
    derivesMiddlePermutation endpoint endpoint sourcePerm
  have contracted :
      Derives basis
        (wordOfEndpoints endpoint
          (endpoint :: (pre ++ remainder) ++ [endpoint]) endpoint)
        (wordOfEndpoints endpoint (pre ++ remainder) endpoint) := by
    cases restEq : pre ++ remainder with
    | nil =>
        simpa [wordOfEndpoints, Word.append, Word.singleton,
          Word.append_assoc] using
            derivesFourToTwo (Word.singleton endpoint)
    | cons next rest =>
        have contraction :=
          derivesSplitEndpointContraction
            (Word.singleton endpoint) (wordOfCons next rest)
        simpa [restEq, wordOfEndpoints, wordOfCons, Word.append,
          Word.singleton, Word.append_assoc, List.append_assoc] using
            contraction
  exact arranged.trans <|
    contracted.trans
      (derivesMiddlePermutation endpoint endpoint targetPerm.symm)

private theorem derivesNormalizeEndpointsAux :
    ∀ (initial : Nat) (pre middle : List Nat) (final : Nat),
      Derives basis
        (wordOfEndpoints initial (pre ++ middle) final)
        (wordOfEndpoints initial
          (pre ++ endpointThresholdParityReduce initial final middle) final)
  | initial, pre, [], final => by
      exact Derives.refl _
  | initial, pre, x :: xs, final => by
      have suffixNormal :=
        derivesNormalizeEndpointsAux initial (pre ++ [x]) xs final
      let reduced := endpointThresholdParityReduce initial final xs
      have firstStep :
          Derives basis
            (wordOfEndpoints initial (pre ++ x :: xs) final)
            (wordOfEndpoints initial (pre ++ x :: reduced) final) := by
        simpa [reduced, List.append_assoc] using suffixNormal
      by_cases countLt :
          endpointCopies initial final x + reduced.count x < 3
      · have reducedEq :
            endpointThresholdParityReduce initial final (x :: xs) =
              x :: reduced := by
          simp [endpointThresholdParityReduce, reduced, countLt]
        rw [reducedEq]
        exact firstStep
      · have totalLe :
            endpointCopies initial final x + reduced.count x ≤ 3 := by
          simpa [reduced] using
            endpointThresholdParityReduce_total_le_three
              initial final x xs
        have totalEq :
            endpointCopies initial final x + reduced.count x = 3 := by
          omega
        have reducedEq :
            endpointThresholdParityReduce initial final (x :: xs) =
              reduced.erase x := by
          simp [endpointThresholdParityReduce, reduced, countLt]
        rw [reducedEq]
        by_cases initialEq : x = initial
        · subst x
          by_cases finalEq : initial = final
          · subst final
            have reducedCount : reduced.count initial = 1 := by
              simp [endpointCopies] at totalEq
              omega
            exact firstStep.trans
              (derivesDeleteBetweenEqualEndpointsPair
                initial pre reduced reducedCount)
          · have reducedCount : reduced.count initial = 2 := by
              simp [endpointCopies, finalEq, Ne.symm finalEq] at totalEq
              omega
            exact firstStep.trans
              (derivesDeleteInitialInteriorPair
                initial final pre reduced reducedCount)
        · by_cases finalEq : x = final
          · subst x
            have reducedCount : reduced.count final = 2 := by
              simp [endpointCopies, initialEq, Ne.symm initialEq] at totalEq
              omega
            exact firstStep.trans
              (derivesDeleteFinalInteriorPair
                initial final pre reduced reducedCount)
          · have reducedCount : reduced.count x = 3 := by
              simpa [endpointCopies, initialEq, finalEq,
                Ne.symm initialEq, Ne.symm finalEq] using totalEq
            exact firstStep.trans
              (derivesDeleteInteriorPair
                initial final x pre reduced reducedCount)
termination_by
  _ _ middle _ => middle.length

/-- Normalize every whole-word multiplicity to the unique value in
`{0,1,2,3}` selected by capped count and parity, while fixing both endpoints. -/
theorem derivesNormalizeEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (endpointThresholdParityReduce initial final middle) final) := by
  simpa using derivesNormalizeEndpointsAux initial [] middle final

/-! ## Balanced repeated-final changes -/

private theorem perm_cons_to_end (x : Nat) :
    ∀ letters : List Nat, (x :: letters).Perm (letters ++ [x])
  | [] => List.Perm.refl _
  | y :: ys =>
      (List.Perm.swap y x ys).trans <|
        List.Perm.cons y (perm_cons_to_end x ys)

private theorem perm_two_to_end (x : Nat) (rest : List Nat) :
    (x :: x :: rest).Perm (rest ++ [x, x]) := by
  apply (List.Perm.cons x (perm_cons_to_end x rest)).trans
  simpa [List.append_assoc] using perm_cons_to_end x (rest ++ [x])

private theorem perm_three_to_end
    (a b c : Nat) (rest : List Nat) :
    (a :: b :: c :: rest).Perm (rest ++ [a, b, c]) := by
  rw [List.perm_iff_count]
  intro tested
  simp only [List.count_cons, List.count_append, List.count_nil]
  omega

/-- Move a repeated final endpoint to the initial endpoint without changing
the multiset. -/
theorem derivesRepeatedFirstFinalSwitch
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (wordOfEndpoints initial (initial :: middle ++ [final]) final)
      (wordOfEndpoints initial (middle ++ [final, final]) initial) := by
  cases middle with
  | nil =>
      simpa [wordOfEndpoints, Word.append, Word.singleton,
        Word.append_assoc] using
          derivesSquareFinalSwitch
            (Word.singleton initial) (Word.singleton final)
  | cons next rest =>
      have sourcePerm :
          (initial :: next :: rest ++ [final]).Perm
            (initial :: final :: next :: rest) := by
        exact List.Perm.cons initial <|
          (perm_cons_to_end final (next :: rest)).symm
      have targetPerm :
          (final :: final :: next :: rest).Perm
            (next :: rest ++ [final, final]) := by
        exact perm_two_to_end final (next :: rest)
      have arrange :=
        derivesMiddlePermutation initial final sourcePerm
      have switch :=
        derivesAttachmentXYYZX
          (Word.singleton initial) (Word.singleton final)
          (wordOfCons next rest)
      have switched :
          Derives basis
            (wordOfEndpoints initial
              (initial :: final :: next :: rest) final)
            (wordOfEndpoints initial
              (final :: final :: next :: rest) initial) := by
        simpa [wordOfEndpoints, wordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using switch
      exact arrange.trans <|
        switched.trans
          (derivesMiddlePermutation initial initial targetPerm)

private theorem normalizedCount_at_least_two
    (initial : Nat) (middle : List Nat) (final tested : Nat)
    (multiple :
      2 ≤ (wordOfEndpoints initial middle final).toList.count tested) :
    2 ≤
      (wordOfEndpoints initial
        (endpointThresholdParityReduce initial final middle) final).toList.count
          tested := by
  have capped :=
    endpointThresholdParityReduce_total_capped
      initial final tested middle
  rw [count_wordOfEndpoints] at multiple ⊢
  omega

private theorem normalizedCount_eq_one
    (initial : Nat) (middle : List Nat) (final tested : Nat)
    (single :
      (wordOfEndpoints initial middle final).toList.count tested = 1) :
    (wordOfEndpoints initial
      (endpointThresholdParityReduce initial final middle) final).toList.count
        tested = 1 := by
  have capped :=
    endpointThresholdParityReduce_total_capped
      initial final tested middle
  rw [count_wordOfEndpoints] at single ⊢
  have bound :=
    endpointThresholdParityReduce_total_le_three
      initial final tested middle
  omega

private theorem middlePerm_of_wholeCountEq
    (initial final : Nat) (left right : List Nat)
    (counts : ∀ tested,
      (wordOfEndpoints initial left final).toList.count tested =
        (wordOfEndpoints initial right final).toList.count tested) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro tested
  have countEq := counts tested
  rw [count_wordOfEndpoints, count_wordOfEndpoints] at countEq
  omega

private theorem derivesRepeatedFinalToInitial
    (initial : Nat) (middle : List Nat) (final : Nat)
    (initialMultiple :
      2 ≤ (wordOfEndpoints initial middle final).toList.count initial)
    (finalMultiple :
      2 ≤ (wordOfEndpoints initial middle final).toList.count final) :
    ∃ switchedMiddle,
      Derives basis
        (wordOfEndpoints initial middle final)
        (wordOfEndpoints initial switchedMiddle initial) ∧
      (wordOfEndpoints initial middle final).toList.Perm
        (wordOfEndpoints initial switchedMiddle initial).toList := by
  by_cases different : initial = final
  · subst final
    exact ⟨middle, Derives.refl _, List.Perm.refl _⟩
  have endpointsNe : initial ≠ final := different
  have middleInitialPositive : 0 < middle.count initial := by
    rw [count_wordOfEndpoints] at initialMultiple
    simp [endpointCopies, endpointsNe, Ne.symm endpointsNe] at initialMultiple
    omega
  have initialMem : initial ∈ middle :=
    List.count_pos_iff.mp middleInitialPositive
  have finalCountAfterInitial :
      (middle.erase initial).count final = middle.count final := by
    rw [List.count_erase_of_ne (Ne.symm endpointsNe)]
  have middleFinalPositive : 0 < middle.count final := by
    rw [count_wordOfEndpoints] at finalMultiple
    simp [endpointCopies, endpointsNe, Ne.symm endpointsNe] at finalMultiple
    omega
  have finalMemAfter : final ∈ middle.erase initial := by
    apply List.count_pos_iff.mp
    rw [finalCountAfterInitial]
    exact middleFinalPositive
  let rest := (middle.erase initial).erase final
  have arrangeFront :
      middle.Perm (initial :: final :: rest) := by
    exact (List.perm_cons_erase initialMem).trans <|
      List.Perm.cons initial <| by
        simpa [rest] using List.perm_cons_erase finalMemAfter
  have arrange :
      middle.Perm (initial :: rest ++ [final]) := by
    exact arrangeFront.trans <|
      List.Perm.cons initial (perm_cons_to_end final rest)
  have arranged := derivesMiddlePermutation initial final arrange
  let switchedMiddle := rest ++ [final, final]
  have switch :
      Derives basis
        (wordOfEndpoints initial (initial :: rest ++ [final]) final)
        (wordOfEndpoints initial switchedMiddle initial) := by
    simpa [switchedMiddle] using
      derivesRepeatedFirstFinalSwitch initial rest final
  have fullPerm :
      (wordOfEndpoints initial middle final).toList.Perm
        (wordOfEndpoints initial switchedMiddle initial).toList := by
    have appendFinal := arrange.append_right [final]
    have outerPerm := List.Perm.cons initial appendFinal
    have moveInitial :=
      List.Perm.cons initial <|
        perm_cons_to_end initial (rest ++ [final, final])
    exact outerPerm.trans <| by
      simpa [switchedMiddle, List.append_assoc] using moveInitial
  exact ⟨switchedMiddle, arranged.trans switch, fullPerm⟩

private theorem derivesRepeatedFinalToOther
    (initial : Nat) (middle : List Nat) (oldFinal newFinal : Nat)
    (finalsNe : oldFinal ≠ newFinal)
    (initialOldNe : initial ≠ oldFinal)
    (initialNewNe : initial ≠ newFinal)
    (oldMultiple :
      2 ≤ (wordOfEndpoints initial middle oldFinal).toList.count oldFinal)
    (newMultiple :
      2 ≤ (wordOfEndpoints initial middle oldFinal).toList.count newFinal) :
    ∃ switchedMiddle,
      Derives basis
        (wordOfEndpoints initial middle oldFinal)
        (wordOfEndpoints initial switchedMiddle newFinal) ∧
      (wordOfEndpoints initial middle oldFinal).toList.Perm
        (wordOfEndpoints initial switchedMiddle newFinal).toList := by
  have oldPositive : 0 < middle.count oldFinal := by
    rw [count_wordOfEndpoints] at oldMultiple
    simp [endpointCopies, initialOldNe, Ne.symm initialOldNe] at oldMultiple
    omega
  have newAtLeastTwo : 2 ≤ middle.count newFinal := by
    rw [count_wordOfEndpoints] at newMultiple
    simp [endpointCopies, finalsNe, initialNewNe,
      Ne.symm finalsNe, Ne.symm initialNewNe] at newMultiple
    omega
  have newMem : newFinal ∈ middle :=
    List.count_pos_iff.mp (by omega)
  have newAfterCount :
      (middle.erase newFinal).count newFinal = middle.count newFinal - 1 := by
    rw [List.count_erase_self]
  have newMemAfter : newFinal ∈ middle.erase newFinal := by
    apply List.count_pos_iff.mp
    rw [newAfterCount]
    omega
  have oldCountAfterTwoNew :
      ((middle.erase newFinal).erase newFinal).count oldFinal =
        middle.count oldFinal := by
    rw [List.count_erase_of_ne finalsNe,
      List.count_erase_of_ne finalsNe]
  have oldMemAfter :
      oldFinal ∈ (middle.erase newFinal).erase newFinal := by
    apply List.count_pos_iff.mp
    rw [oldCountAfterTwoNew]
    exact oldPositive
  let rest :=
    ((middle.erase newFinal).erase newFinal).erase oldFinal
  have arrangeFront :
      middle.Perm (newFinal :: newFinal :: oldFinal :: rest) := by
    exact (List.perm_cons_erase newMem).trans <|
      List.Perm.cons newFinal <|
        (List.perm_cons_erase newMemAfter).trans <|
          List.Perm.cons newFinal <| by
            simpa [rest] using List.perm_cons_erase oldMemAfter
  have arrange :
      middle.Perm (rest ++ [newFinal, newFinal, oldFinal]) := by
    exact arrangeFront.trans <|
      perm_three_to_end newFinal newFinal oldFinal rest
  have arranged := derivesMiddlePermutation initial oldFinal arrange
  let switchedMiddle := rest ++ [newFinal, oldFinal, oldFinal]
  have switch :
      Derives basis
        (wordOfEndpoints initial
          (rest ++ [newFinal, newFinal, oldFinal]) oldFinal)
        (wordOfEndpoints initial switchedMiddle newFinal) := by
    have contextual :=
      Derives.prepend (wordOfCons initial rest)
        (derivesSquareFinalSwitch
          (Word.singleton newFinal) (Word.singleton oldFinal))
    simpa [switchedMiddle, wordOfEndpoints, wordOfCons, Word.append,
      Word.singleton, Word.append_assoc, List.append_assoc] using contextual
  have fullPerm :
      (wordOfEndpoints initial middle oldFinal).toList.Perm
        (wordOfEndpoints initial switchedMiddle newFinal).toList := by
    have appendFinal := arrange.append_right [oldFinal]
    have outerPerm := List.Perm.cons initial appendFinal
    have suffixPerm :
        [newFinal, newFinal, oldFinal, oldFinal].Perm
          [newFinal, oldFinal, oldFinal, newFinal] :=
      List.Perm.cons newFinal <|
        perm_cons_to_end newFinal [oldFinal, oldFinal]
    have restPerm := List.Perm.append_left rest suffixPerm
    have switchedPerm := List.Perm.cons initial restPerm
    exact outerPerm.trans <| by
      simpa [switchedMiddle, List.append_assoc] using switchedPerm
  exact ⟨switchedMiddle, arranged.trans switch, fullPerm⟩

/-! ## The simple-final separator inherited from `S4_23` -/

private def finalSeparator (tested : Nat) : Nat → Fin 4 :=
  fun value => if value = tested then 1 else 3

private theorem eval_finalSeparator
    (tested : Nat) (front : List Nat) (final : Nat) :
    SemigroupBasis.Examples.edmundsFourTwentyOne.semigroup.eval
        (finalSeparator tested)
        (wordOfPrefixFinal front final) =
      if tested ∈ front then (0 : Fin 4) else
        if final = tested then (1 : Fin 4) else (3 : Fin 4) := by
  induction front with
  | nil =>
      by_cases finalEq : final = tested
      · subst final
        simp [wordOfPrefixFinal, finalSeparator]
      · simp [wordOfPrefixFinal, finalSeparator, finalEq]
  | cons current rest induction =>
      rw [wordOfPrefixFinal_cons,
        Semigroup.eval_append, Semigroup.eval_singleton, induction]
      change
        SemigroupBasis.Examples.edmundsFourTwentyOneMul
            (finalSeparator tested current)
            (if tested ∈ rest then (0 : Fin 4) else
              if final = tested then (1 : Fin 4) else (3 : Fin 4)) =
          if tested ∈ current :: rest then (0 : Fin 4) else
            if final = tested then (1 : Fin 4) else (3 : Fin 4)
      by_cases currentEq : current = tested
      · subst current
        simp [finalSeparator,
          SemigroupBasis.Examples.edmundsFourTwentyOneMul]
      · simp [finalSeparator, currentEq, Ne.symm currentEq,
          SemigroupBasis.Examples.edmundsFourTwentyOneMul]

private theorem wordOfEndpoints_asPrefix
    (initial : Nat) (middle : List Nat) (final : Nat) :
    wordOfEndpoints initial middle final =
      wordOfPrefixFinal (initial :: middle) final := rfl

private theorem eval_finalSeparator_eq_one_iff
    (tested initial : Nat) (middle : List Nat) (final : Nat) :
    SemigroupBasis.Examples.edmundsFourTwentyOne.semigroup.eval
        (finalSeparator tested)
        (wordOfEndpoints initial middle final) = (1 : Fin 4) ↔
      final = tested ∧ tested ∉ initial :: middle := by
  rw [wordOfEndpoints_asPrefix, eval_finalSeparator]
  by_cases member : tested ∈ initial :: middle
  · simp [member]
  · by_cases finalEq : final = tested
    · simp [member, finalEq]
    · simp [member, finalEq]

private theorem simpleFinal_iff_of_valid
    (initialLeft : Nat) (middleLeft : List Nat) (finalLeft : Nat)
    (initialRight : Nat) (middleRight : List Nat) (finalRight : Nat)
    (valid :
      (Identity.mk
        (wordOfEndpoints initialLeft middleLeft finalLeft)
        (wordOfEndpoints initialRight middleRight finalRight)).SatisfiedBy
          SemigroupBasis.Examples.edmundsFourTwentyOne.semigroup) :
    ∀ tested,
      (finalLeft = tested ∧ tested ∉ initialLeft :: middleLeft) ↔
        (finalRight = tested ∧ tested ∉ initialRight :: middleRight) := by
  intro tested
  have evaluated := valid (finalSeparator tested)
  constructor
  · intro leftSimple
    have leftOne :=
      (eval_finalSeparator_eq_one_iff
        tested initialLeft middleLeft finalLeft).2 leftSimple
    have rightOne := evaluated.symm.trans leftOne
    exact (eval_finalSeparator_eq_one_iff
      tested initialRight middleRight finalRight).1 rightOne
  · intro rightSimple
    have rightOne :=
      (eval_finalSeparator_eq_one_iff
        tested initialRight middleRight finalRight).2 rightSimple
    have leftOne := evaluated.trans rightOne
    exact (eval_finalSeparator_eq_one_iff
      tested initialLeft middleLeft finalLeft).1 leftOne

private def splitMiddleFinal (current : Nat) :
    List Nat → List Nat × Nat
  | [] => ([], current)
  | next :: rest =>
      let split := splitMiddleFinal next rest
      (current :: split.1, split.2)

private theorem splitMiddleFinal_reconstruct
    (current : Nat) (rest : List Nat) :
    (splitMiddleFinal current rest).1 ++
        [(splitMiddleFinal current rest).2] =
      current :: rest := by
  induction rest generalizing current with
  | nil => rfl
  | cons next rest induction =>
      simp only [splitMiddleFinal]
      simpa using congrArg (List.cons current) (induction next)

private theorem wordOfEndpoints_splitMiddleFinal
    (initial current : Nat) (rest : List Nat) :
    wordOfEndpoints initial (splitMiddleFinal current rest).1
        (splitMiddleFinal current rest).2 =
      Word.mk initial (current :: rest) := by
  apply Word.toList_injective
  change
    initial ::
        ((splitMiddleFinal current rest).1 ++
          [(splitMiddleFinal current rest).2]) =
      initial :: current :: rest
  exact congrArg (List.cons initial)
    (splitMiddleFinal_reconstruct current rest)

private theorem repeatedInitial_count_two
    (initial : Nat) (middle : List Nat) (final : Nat)
    (repeated : initial ∈ middle ∨ final = initial) :
    2 ≤ (wordOfEndpoints initial middle final).toList.count initial := by
  rw [count_wordOfEndpoints]
  rcases repeated with middleMem | finalEq
  · have positive : 0 < middle.count initial :=
      List.count_pos_iff.mpr middleMem
    simp [endpointCopies]
    omega
  · subst final
    simp [endpointCopies]

private theorem repeatedFinal_count_two
    (initial : Nat) (middle : List Nat) (final : Nat)
    (repeated : final ∈ initial :: middle) :
    2 ≤ (wordOfEndpoints initial middle final).toList.count final := by
  simp only [toList_wordOfEndpoints, List.count_cons, List.count_append,
    List.count_singleton]
  have positive : 0 < (initial :: middle).count final :=
    List.count_pos_iff.mpr repeated
  simp only [List.count_cons] at positive
  by_cases endpoints : initial = final
  · subst final
    simp
  · simp [endpoints, Ne.symm endpoints] at positive ⊢
    omega

/-! ## Unrestricted factor-theory intersection -/

/-- Any identity valid in both factors is derivable from the exact thirteen
displayed laws. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (s4_23Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_23.table.semigroup)
    (s4_90Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_90.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have factorDerivation :=
    SemigroupBasis.Generated.S4_23.representative_basis.2
      identity s4_23Valid
  have edmundsValid :
      identity.SatisfiedBy
        SemigroupBasis.Examples.edmundsFourTwentyOne.semigroup := by
    intro valuation
    exact factorDerivation.sound
      SemigroupBasis.Examples.edmundsFourTwentyOneBasis_models valuation
  have cappedCounts :=
    SemigroupBasis.Examples.edmundsFourTwentyOneValid_capped_count_eq
      identity edmundsValid
  have parityCounts :=
    SemigroupBasis.CoRoots.S4_90.valid_parity identity s4_90Valid
  have heads :=
    SemigroupBasis.CoRoots.S4_90.valid_head_eq identity s4_90Valid
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  simp only at heads
  subst rightHead
  cases leftTail with
  | nil =>
      cases rightTail with
      | nil =>
          exact Derives.refl _
      | cons rightSecond rightRest =>
          by_cases secondHead : rightSecond = leftHead
          · subst rightSecond
            have countEq := cappedCounts leftHead
            simp [Word.toList] at countEq
          · have countEq := cappedCounts rightSecond
            simp [Word.toList, secondHead, Ne.symm secondHead] at countEq
            omega
  | cons leftSecond leftRest =>
      cases rightTail with
      | nil =>
          by_cases secondHead : leftSecond = leftHead
          · subst leftSecond
            have countEq := cappedCounts leftHead
            simp [Word.toList] at countEq
          · have countEq := cappedCounts leftSecond
            simp [Word.toList, secondHead, Ne.symm secondHead] at countEq
      | cons rightSecond rightRest =>
          let leftSplit := splitMiddleFinal leftSecond leftRest
          let rightSplit := splitMiddleFinal rightSecond rightRest
          have leftReconstruct :
              wordOfEndpoints leftHead leftSplit.1 leftSplit.2 =
                Word.mk leftHead (leftSecond :: leftRest) :=
            wordOfEndpoints_splitMiddleFinal leftHead leftSecond leftRest
          have rightReconstruct :
              wordOfEndpoints leftHead rightSplit.1 rightSplit.2 =
                Word.mk leftHead (rightSecond :: rightRest) :=
            wordOfEndpoints_splitMiddleFinal leftHead rightSecond rightRest
          have leftNormal :
              Derives basis
                (Word.mk leftHead (leftSecond :: leftRest))
                (wordOfEndpoints leftHead
                  (endpointThresholdParityReduce
                    leftHead leftSplit.2 leftSplit.1)
                  leftSplit.2) := by
            rw [← leftReconstruct]
            exact derivesNormalizeEndpoints
              leftHead leftSplit.1 leftSplit.2
          have rightNormal :
              Derives basis
                (Word.mk leftHead (rightSecond :: rightRest))
                (wordOfEndpoints leftHead
                  (endpointThresholdParityReduce
                    leftHead rightSplit.2 rightSplit.1)
                  rightSplit.2) := by
            rw [← rightReconstruct]
            exact derivesNormalizeEndpoints
              leftHead rightSplit.1 rightSplit.2
          have normalCountEq :
              ∀ tested,
                (wordOfEndpoints leftHead
                    (endpointThresholdParityReduce
                      leftHead leftSplit.2 leftSplit.1)
                    leftSplit.2).toList.count tested =
                  (wordOfEndpoints leftHead
                    (endpointThresholdParityReduce
                      leftHead rightSplit.2 rightSplit.1)
                    rightSplit.2).toList.count tested := by
            apply endpointThresholdParityReduce_whole_count_eq
            · intro tested
              rw [leftReconstruct, rightReconstruct]
              exact cappedCounts tested
            · intro tested
              rw [leftReconstruct, rightReconstruct]
              exact parityCounts tested
          have endpointEdmundsValid :
              (Identity.mk
                (wordOfEndpoints leftHead leftSplit.1 leftSplit.2)
                (wordOfEndpoints leftHead rightSplit.1 rightSplit.2)).SatisfiedBy
                  SemigroupBasis.Examples.edmundsFourTwentyOne.semigroup := by
            rw [leftReconstruct, rightReconstruct]
            exact edmundsValid
          have simpleFinalIff :=
            simpleFinal_iff_of_valid
              leftHead leftSplit.1 leftSplit.2
              leftHead rightSplit.1 rightSplit.2
              endpointEdmundsValid
          by_cases leftSimple :
              leftSplit.2 ∉ leftHead :: leftSplit.1
          · have rightSimple :=
              (simpleFinalIff leftSplit.2).mp ⟨rfl, leftSimple⟩
            have finalsEq : rightSplit.2 = leftSplit.2 := rightSimple.1
            rw [finalsEq] at rightNormal normalCountEq
            have middlePerm :=
              middlePerm_of_wholeCountEq leftHead leftSplit.2
                (endpointThresholdParityReduce
                  leftHead leftSplit.2 leftSplit.1)
                (endpointThresholdParityReduce
                  leftHead leftSplit.2 rightSplit.1)
                normalCountEq
            exact leftNormal.trans <|
              (derivesMiddlePermutation
                leftHead leftSplit.2 middlePerm).trans rightNormal.symm
          · have leftRepeated :
                leftSplit.2 ∈ leftHead :: leftSplit.1 :=
              Decidable.not_not.mp leftSimple
            have rightRepeated :
                rightSplit.2 ∈ leftHead :: rightSplit.1 := by
              apply Decidable.byContradiction
              intro rightSimple
              have leftWouldBeSimple :=
                (simpleFinalIff rightSplit.2).mpr ⟨rfl, rightSimple⟩
              exact leftWouldBeSimple.2 <| by
                simpa [leftWouldBeSimple.1] using leftRepeated
            by_cases initialRepeated :
                leftHead ∈ leftSplit.1 ∨ leftSplit.2 = leftHead
            · have leftInitialMultiple :=
                normalizedCount_at_least_two
                  leftHead leftSplit.1 leftSplit.2 leftHead
                  (repeatedInitial_count_two
                    leftHead leftSplit.1 leftSplit.2 initialRepeated)
              have rightInitialMultiple :
                  2 ≤
                    (wordOfEndpoints leftHead
                      (endpointThresholdParityReduce
                        leftHead rightSplit.2 rightSplit.1)
                      rightSplit.2).toList.count leftHead := by
                rw [← normalCountEq leftHead]
                exact leftInitialMultiple
              have leftFinalMultiple :=
                normalizedCount_at_least_two
                  leftHead leftSplit.1 leftSplit.2 leftSplit.2
                  (repeatedFinal_count_two
                    leftHead leftSplit.1 leftSplit.2 leftRepeated)
              have rightFinalMultiple :=
                normalizedCount_at_least_two
                  leftHead rightSplit.1 rightSplit.2 rightSplit.2
                  (repeatedFinal_count_two
                    leftHead rightSplit.1 rightSplit.2 rightRepeated)
              obtain ⟨leftSwitched, leftSwitch, leftPerm⟩ :=
                derivesRepeatedFinalToInitial
                  leftHead
                  (endpointThresholdParityReduce
                    leftHead leftSplit.2 leftSplit.1)
                  leftSplit.2 leftInitialMultiple leftFinalMultiple
              obtain ⟨rightSwitched, rightSwitch, rightPerm⟩ :=
                derivesRepeatedFinalToInitial
                  leftHead
                  (endpointThresholdParityReduce
                    leftHead rightSplit.2 rightSplit.1)
                  rightSplit.2 rightInitialMultiple rightFinalMultiple
              have switchedCountEq :
                  ∀ tested,
                    (wordOfEndpoints leftHead leftSwitched leftHead).toList.count
                        tested =
                      (wordOfEndpoints leftHead rightSwitched leftHead).toList.count
                        tested := by
                intro tested
                have leftPermCount :=
                  (List.perm_iff_count.mp leftPerm) tested
                have rightPermCount :=
                  (List.perm_iff_count.mp rightPerm) tested
                exact leftPermCount.symm.trans <|
                  (normalCountEq tested).trans rightPermCount
              have switchedMiddlePerm :=
                middlePerm_of_wholeCountEq
                  leftHead leftHead leftSwitched rightSwitched
                  switchedCountEq
              exact leftNormal.trans <| leftSwitch.trans <|
                (derivesMiddlePermutation
                  leftHead leftHead switchedMiddlePerm).trans <|
                rightSwitch.symm.trans rightNormal.symm
            · have leftMiddleHeadAbsent : leftHead ∉ leftSplit.1 :=
                fun member => initialRepeated (Or.inl member)
              have leftFinalHeadNe : leftSplit.2 ≠ leftHead :=
                fun equal => initialRepeated (Or.inr equal)
              have leftInitialSingleOriginal :
                  (wordOfEndpoints leftHead leftSplit.1 leftSplit.2).toList.count
                      leftHead = 1 := by
                rw [count_wordOfEndpoints]
                simp [endpointCopies,
                  List.count_eq_zero.mpr leftMiddleHeadAbsent,
                  leftFinalHeadNe, Ne.symm leftFinalHeadNe]
              have leftInitialSingle :=
                normalizedCount_eq_one
                  leftHead leftSplit.1 leftSplit.2 leftHead
                  leftInitialSingleOriginal
              by_cases finalsEq : leftSplit.2 = rightSplit.2
              · rw [← finalsEq] at rightNormal normalCountEq
                have middlePerm :=
                  middlePerm_of_wholeCountEq leftHead leftSplit.2
                    (endpointThresholdParityReduce
                      leftHead leftSplit.2 leftSplit.1)
                    (endpointThresholdParityReduce
                      leftHead leftSplit.2 rightSplit.1)
                    normalCountEq
                exact leftNormal.trans <|
                  (derivesMiddlePermutation
                    leftHead leftSplit.2 middlePerm).trans rightNormal.symm
              · have leftFinalMultiple :=
                  normalizedCount_at_least_two
                    leftHead leftSplit.1 leftSplit.2 leftSplit.2
                    (repeatedFinal_count_two
                      leftHead leftSplit.1 leftSplit.2 leftRepeated)
                have rightFinalMultiple :=
                  normalizedCount_at_least_two
                    leftHead rightSplit.1 rightSplit.2 rightSplit.2
                    (repeatedFinal_count_two
                      leftHead rightSplit.1 rightSplit.2 rightRepeated)
                have leftNewMultiple :
                    2 ≤
                      (wordOfEndpoints leftHead
                        (endpointThresholdParityReduce
                          leftHead leftSplit.2 leftSplit.1)
                        leftSplit.2).toList.count rightSplit.2 := by
                  rw [normalCountEq rightSplit.2]
                  exact rightFinalMultiple
                have initialOldNe : leftHead ≠ leftSplit.2 :=
                  Ne.symm leftFinalHeadNe
                have initialNewNe : leftHead ≠ rightSplit.2 := by
                  intro equal
                  rw [← equal] at leftNewMultiple
                  omega
                obtain ⟨switchedMiddle, switch, switchPerm⟩ :=
                  derivesRepeatedFinalToOther
                    leftHead
                    (endpointThresholdParityReduce
                      leftHead leftSplit.2 leftSplit.1)
                    leftSplit.2 rightSplit.2 finalsEq
                    initialOldNe initialNewNe
                    leftFinalMultiple leftNewMultiple
                have switchedCountEq :
                    ∀ tested,
                      (wordOfEndpoints leftHead switchedMiddle
                          rightSplit.2).toList.count tested =
                        (wordOfEndpoints leftHead
                          (endpointThresholdParityReduce
                            leftHead rightSplit.2 rightSplit.1)
                          rightSplit.2).toList.count tested := by
                  intro tested
                  have switchCount :=
                    (List.perm_iff_count.mp switchPerm) tested
                  exact switchCount.symm.trans (normalCountEq tested)
                have switchedMiddlePerm :=
                  middlePerm_of_wholeCountEq
                    leftHead rightSplit.2 switchedMiddle
                    (endpointThresholdParityReduce
                      leftHead rightSplit.2 rightSplit.1)
                    switchedCountEq
                exact leftNormal.trans <| switch.trans <|
                  (derivesMiddlePermutation
                    leftHead rightSplit.2 switchedMiddlePerm).trans
                      rightNormal.symm

/-- The exact thirteen laws form the unrestricted identity-theory
intersection of `S4_23` and `S4_90`. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S4_23.table.semigroup
      SemigroupBasis.Generated.S4_90.table.semigroup
      basis where
  leftModels := basis_s4_23_models
  rightModels := basis_s4_90_models
  complete := derivesOfFactorValid

end SemigroupBasis.CoRoots.Order6L3RootS4_23S4_90

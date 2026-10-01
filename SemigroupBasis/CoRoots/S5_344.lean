import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.Examples.FirstCappedMultiplicityFour

namespace SemigroupBasis.CoRoots.S5_344

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xxyz : Word Nat := w 0 [0, 1, 2]
def xyxz : Word Nat := w 0 [1, 0, 2]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xzyy : Word Nat := w 0 [2, 1, 1]
def xyzt : Word Nat := w 0 [1, 2, 3]
def xzyt : Word Nat := w 0 [2, 1, 3]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftEndpointDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def rightEndpointDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def squareInterleaveLaw : Identity Nat := ⟨xxyy, xyxy⟩
def squareFinalSwitchLaw : Identity Nat := ⟨xxyy, xyyx⟩
def doubledInitialMoveLaw : Identity Nat := ⟨xxyz, xyxz⟩
def closedInteriorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩
def repeatedFinalSwapLaw : Identity Nat := ⟨xyzy, xzyy⟩
def interiorSwapLaw : Identity Nat := ⟨xyzt, xzyt⟩

/-- The common exact nine-identity basis of
`S5_344`, `S5_356`, `S5_373`, and `S5_408`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftEndpointDuplicationLaw, rightEndpointDuplicationLaw,
    squareInterleaveLaw, squareFinalSwitchLaw, doubledInitialMoveLaw,
    closedInteriorSwapLaw, repeatedFinalSwapLaw, interiorSwapLaw]

private def instantiateFourWords
    (u v z q : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | 3 => q
  | n + 4 => Word.singleton (n + 4)

theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) := by
  have base : Derives basis xxx xx :=
    Derives.symm <|
      Derives.fromBasis (e := powerLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateFourWords u u u u)
  simpa [powerLaw, xx, xxx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesLeftEndpointExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have base : Derives basis xyx xxyx :=
    Derives.fromBasis (e := leftEndpointDuplicationLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateFourWords u v v v)
  simpa [leftEndpointDuplicationLaw, xyx, xxyx, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesRightEndpointExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have base : Derives basis xyx xyxx :=
    Derives.fromBasis (e := rightEndpointDuplicationLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateFourWords u v v v)
  simpa [rightEndpointDuplicationLaw, xyx, xyxx, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSquareFinalSwitch (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ v) (((u ++ v) ++ v) ++ u) := by
  have base : Derives basis xxyy xyyx :=
    Derives.fromBasis (e := squareFinalSwitchLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateFourWords u v v v)
  simpa [squareFinalSwitchLaw, xxyy, xyyx, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesDoubledInitialMove (u v z : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ z) (((u ++ v) ++ u) ++ z) := by
  have base : Derives basis xxyz xyxz :=
    Derives.fromBasis (e := doubledInitialMoveLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateFourWords u v z z)
  simpa [doubledInitialMoveLaw, xxyz, xyxz, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Arbitrary adjacent nonempty blocks commute between fixed nonempty
endpoint contexts. -/
theorem derivesInteriorSwap (a b c d : Word Nat) :
    Derives basis (((a ++ b) ++ c) ++ d) (((a ++ c) ++ b) ++ d) := by
  have base : Derives basis xyzt xzyt :=
    Derives.fromBasis (e := interiorSwapLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateFourWords a b c d)
  simpa [interiorSwapLaw, xyzt, xzyt, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- The derived switch
`x x y z z = x y z z x`. -/
theorem derivesRepeatedFirstFinalSwitch
    (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ z)
      ((((x ++ y) ++ z) ++ z) ++ x) := by
  have step₁ :=
    derivesDoubledInitialMove x (y ++ z) z
  have step₂ :=
    Derives.appendRight (derivesRightEndpointExpansion x (y ++ z)) z
  have step₃ :=
    Derives.prepend (x ++ y) <|
      Derives.symm (derivesSquareFinalSwitch z x)
  have step₄ :=
    Derives.symm <|
      derivesRightEndpointExpansion x (y ++ (z ++ z))
  exact Derives.trans
    (by simpa [Word.append_assoc] using step₁) <|
    Derives.trans
      (by simpa [Word.append_assoc] using step₂) <|
    Derives.trans
      (by simpa [Word.append_assoc] using step₃)
      (by simpa [Word.append_assoc] using step₄)

/-- A word with fixed first and final letters and an explicit middle. -/
private def wordOfEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) : Word Nat :=
  ⟨initial, middle ++ [final]⟩

@[simp]
private theorem toList_wordOfEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) :
    (wordOfEndpoints initial middle final).toList =
      initial :: middle ++ [final] := rfl

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

/-- Split a nonempty list into all but its last entry and its last entry. -/
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
  | cons next rest ih =>
      simp only [splitMiddleFinal]
      simpa using congrArg (List.cons current) (ih next)

private theorem wordOfEndpoints_splitMiddleFinal
    (initial current : Nat) (rest : List Nat) :
    wordOfEndpoints initial (splitMiddleFinal current rest).1
        (splitMiddleFinal current rest).2 =
      ⟨initial, current :: rest⟩ := by
  apply Word.toList_injective
  change
    initial ::
        ((splitMiddleFinal current rest).1 ++
          [(splitMiddleFinal current rest).2]) =
      initial :: current :: rest
  exact congrArg (List.cons initial)
    (splitMiddleFinal_reconstruct current rest)

/-- The number of middle copies retained after the two endpoint occurrences
have been accounted for. -/
private def middleLimit (initial final x : Nat) : Nat :=
  if x = initial then
    if x = final then 0 else 1
  else if x = final then 1 else 2

private def middleReduce (initial final : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := middleReduce initial final xs
      if reduced.count x < middleLimit initial final x then
        x :: reduced
      else
        reduced

private theorem count_middleReduce
    (initial final z : Nat) (middle : List Nat) :
    (middleReduce initial final middle).count z =
      min (middle.count z) (middleLimit initial final z) := by
  induction middle with
  | nil =>
      simp [middleReduce, middleLimit]
  | cons x xs ih =>
      simp only [middleReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at hcount
          by_cases hi : x = initial <;>
            by_cases hf : x = final <;>
              simp [middleLimit, hi, hf] at hcount ⊢ <;> omega
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx), ih]
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, ih]
          rw [ih] at hcount
          by_cases hi : x = initial <;>
            by_cases hf : x = final <;>
              simp [middleLimit, hi, hf] at hcount ⊢ <;> omega
        · rw [List.count_cons_of_ne (Ne.symm hzx), ih]

private theorem normal_count
    (initial : Nat) (middle : List Nat) (final z : Nat) :
    (wordOfEndpoints initial (middleReduce initial final middle)
        final).toList.count z =
      min ((wordOfEndpoints initial middle final).toList.count z) 2 := by
  simp only [toList_wordOfEndpoints,
    List.count_cons, List.count_append, List.count_append,
    count_middleReduce]
  by_cases hi : z = initial
  · subst z
    by_cases hf : initial = final
    · subst final
      simp [middleLimit]
    · simp [middleLimit, hf, Ne.symm hf]
      omega
  · by_cases hf : z = final
    · subst z
      simp [middleLimit, hi, Ne.symm hi]
      omega
    · simp [middleLimit, hi, hf, Ne.symm hi, Ne.symm hf]

private theorem derivesMiddlePermutation
    (initial final : Nat) {middle₁ middle₂ : List Nat}
    (permutation : middle₁.Perm middle₂) :
    Derives basis
      (wordOfEndpoints initial middle₁ final)
      (wordOfEndpoints initial middle₂ final) := by
  induction permutation generalizing initial with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      simpa [wordOfEndpoints_eq, Word.append_assoc] using
        Derives.prepend (Word.singleton initial) (ih x)
  | swap x y xs =>
      simpa [wordOfEndpoints_eq, Word.append_assoc] using
        derivesInteriorSwap
          (Word.singleton initial)
          (Word.singleton y) (Word.singleton x)
          (wordOfPrefixFinal xs final)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ initial) (ih₂ initial)

private theorem derivesDeleteThirdInterior
    (initial final x : Nat) (pre reduced : List Nat)
    (hcount : reduced.count x = 2) :
    Derives basis
      (wordOfEndpoints initial (pre ++ x :: reduced) final)
      (wordOfEndpoints initial (pre ++ reduced) final) := by
  let remainder := (reduced.erase x).erase x
  have sourcePerm :
      (pre ++ x :: reduced).Perm
        (x :: x :: x :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases hz : z = x
    · subst z
      simp only [List.count_cons_self]
      have firstErase : (reduced.erase x).count x = 1 := by
        rw [List.count_erase_self, hcount]
      have secondErase : ((reduced.erase x).erase x).count x = 0 := by
        rw [List.count_erase_self, firstErase]
      simp [remainder, hcount, secondErase]
    · simp [remainder, hz, Ne.symm hz]
  have targetPerm :
      (pre ++ reduced).Perm (x :: x :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases hz : z = x
    · subst z
      simp only [List.count_cons_self]
      have firstErase : (reduced.erase x).count x = 1 := by
        rw [List.count_erase_self, hcount]
      have secondErase : ((reduced.erase x).erase x).count x = 0 := by
        rw [List.count_erase_self, firstErase]
      simp [remainder, hcount, secondErase]
    · simp [remainder, hz, Ne.symm hz]
  have contract :=
    Derives.appendRight
      (Derives.prepend (Word.singleton initial)
        (derivesPowerContraction (Word.singleton x)))
      (wordOfPrefixFinal (pre ++ remainder) final)
  exact Derives.trans
    (derivesMiddlePermutation initial final sourcePerm) <|
    Derives.trans
      (by
        simpa [wordOfEndpoints_eq, wordOfPrefixFinal,
          Word.append_assoc] using contract)
      (derivesMiddlePermutation initial final targetPerm.symm)

private theorem derivesDeleteRepeatedInitial
    (initial final : Nat) (pre reduced : List Nat)
    (hcount : reduced.count initial = 1) :
    Derives basis
      (wordOfEndpoints initial (pre ++ initial :: reduced) final)
      (wordOfEndpoints initial (pre ++ reduced) final) := by
  let remainder := reduced.erase initial
  have sourcePerm :
      (pre ++ initial :: reduced).Perm
        (initial :: initial :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases hz : z = initial
    · subst z
      have eraseCount : (reduced.erase initial).count initial = 0 := by
        rw [List.count_erase_self, hcount]
      simp [remainder, hcount, eraseCount]
    · simp [remainder, hz, Ne.symm hz]
  have targetPerm :
      (pre ++ reduced).Perm (initial :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases hz : z = initial
    · subst z
      have eraseCount : (reduced.erase initial).count initial = 0 := by
        rw [List.count_erase_self, hcount]
      simp [remainder, hcount, eraseCount]
    · simp [remainder, hz, Ne.symm hz]
  have contract :=
    Derives.appendRight
      (derivesPowerContraction (Word.singleton initial))
      (wordOfPrefixFinal (pre ++ remainder) final)
  exact Derives.trans
    (derivesMiddlePermutation initial final sourcePerm) <|
    Derives.trans
      (by
        simpa [wordOfEndpoints_eq, wordOfPrefixFinal,
          Word.append_assoc] using contract)
      (derivesMiddlePermutation initial final targetPerm.symm)

private theorem derivesDeleteRepeatedFinal
    (initial final : Nat) (pre reduced : List Nat)
    (hcount : reduced.count final = 1) :
    Derives basis
      (wordOfEndpoints initial (pre ++ final :: reduced) final)
      (wordOfEndpoints initial (pre ++ reduced) final) := by
  let remainder := reduced.erase final
  have sourcePerm :
      (pre ++ final :: reduced).Perm
        ((pre ++ remainder) ++ [final, final]) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases hz : z = final
    · subst z
      have eraseCount : (reduced.erase final).count final = 0 := by
        rw [List.count_erase_self, hcount]
      simp [remainder, hcount, eraseCount]
    · simp [remainder, hz, Ne.symm hz]
  have targetPerm :
      (pre ++ reduced).Perm ((pre ++ remainder) ++ [final]) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases hz : z = final
    · subst z
      have eraseCount : (reduced.erase final).count final = 0 := by
        rw [List.count_erase_self, hcount]
      simp [remainder, hcount, eraseCount]
    · simp [remainder, hz, Ne.symm hz]
  have contract :=
    Derives.prepend (wordOfCons initial (pre ++ remainder))
      (derivesPowerContraction (Word.singleton final))
  have contractSource :
      wordOfEndpoints initial ((pre ++ remainder) ++ [final, final])
          final =
        wordOfCons initial (pre ++ remainder) ++
          ((Word.singleton final ++ Word.singleton final) ++
            Word.singleton final) := by
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

private theorem derivesDeleteBetweenEqualEndpoints
    (endpoint : Nat) (pre reduced : List Nat) :
    Derives basis
      (wordOfEndpoints endpoint (pre ++ endpoint :: reduced) endpoint)
      (wordOfEndpoints endpoint (pre ++ reduced) endpoint) := by
  let rest := pre ++ reduced
  have arrange :
      (pre ++ endpoint :: reduced).Perm (endpoint :: rest) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append, List.count_cons]
    simp [rest]
    omega
  have arranged :=
    derivesMiddlePermutation endpoint endpoint arrange
  have contractRest :
      Derives basis
        (wordOfEndpoints endpoint (endpoint :: rest) endpoint)
        (wordOfEndpoints endpoint rest endpoint) := by
    cases rest with
    | nil =>
      simpa [wordOfEndpoints, Word.append, Word.singleton,
        Word.append_assoc] using
          derivesPowerContraction (Word.singleton endpoint)
    | cons next more =>
      have contract :=
        Derives.symm <|
          derivesLeftEndpointExpansion
            (Word.singleton endpoint) (wordOfCons next more)
      simpa [wordOfEndpoints, wordOfCons, Word.append,
        Word.singleton, Word.append_assoc] using contract
  exact Derives.trans arranged contractRest

private theorem derivesNormalizeMiddleAux :
    ∀ (initial : Nat) (pre middle : List Nat) (final : Nat),
      Derives basis
        (wordOfEndpoints initial (pre ++ middle) final)
        (wordOfEndpoints initial
          (pre ++ middleReduce initial final middle) final)
  | initial, pre, [], final => by
      exact Derives.refl _
  | initial, pre, x :: xs, final => by
      have suffixNormal :=
        derivesNormalizeMiddleAux initial (pre ++ [x]) xs final
      let reduced := middleReduce initial final xs
      have firstStep :
          Derives basis
            (wordOfEndpoints initial (pre ++ x :: xs) final)
            (wordOfEndpoints initial (pre ++ x :: reduced) final) := by
        simpa [reduced, List.append_assoc] using suffixNormal
      by_cases hcount : reduced.count x < middleLimit initial final x
      · have reducedEq :
            middleReduce initial final (x :: xs) = x :: reduced := by
          simp [middleReduce, reduced, hcount]
        rw [reducedEq]
        exact firstStep
      · have countLe :
            reduced.count x ≤ middleLimit initial final x := by
          rw [show reduced = middleReduce initial final xs by rfl,
            count_middleReduce]
          exact Nat.min_le_right _ _
        have countEq :
            reduced.count x = middleLimit initial final x := by
          omega
        have reducedEq :
            middleReduce initial final (x :: xs) = reduced := by
          simp [middleReduce, reduced, hcount]
        rw [reducedEq]
        by_cases hi : x = initial
        · subst x
          by_cases hf : initial = final
          · subst final
            exact Derives.trans firstStep
              (derivesDeleteBetweenEqualEndpoints initial pre reduced)
          · have initialCount : reduced.count initial = 1 := by
              simpa [middleLimit, hf] using countEq
            exact Derives.trans firstStep
              (derivesDeleteRepeatedInitial
                initial final pre reduced initialCount)
        · by_cases hf : x = final
          · subst x
            have finalCount : reduced.count final = 1 := by
              simpa [middleLimit, hi] using countEq
            exact Derives.trans firstStep
              (derivesDeleteRepeatedFinal
                initial final pre reduced finalCount)
          · have interiorCount : reduced.count x = 2 := by
              simpa [middleLimit, hi, hf] using countEq
            exact Derives.trans firstStep
              (derivesDeleteThirdInterior
                initial final x pre reduced interiorCount)
termination_by
  _ _ middle _ => middle.length

private theorem derivesNormalEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (middleReduce initial final middle) final) := by
  simpa using derivesNormalizeMiddleAux initial [] middle final

private theorem perm_cons_to_end (x : Nat) :
    ∀ letters : List Nat, (x :: letters).Perm (letters ++ [x])
  | [] => List.Perm.refl _
  | y :: ys =>
      (List.Perm.swap y x ys).trans <|
        List.Perm.cons y (perm_cons_to_end x ys)

private theorem perm_three_to_end (a b c : Nat) (rest : List Nat) :
    (a :: b :: c :: rest).Perm (rest ++ [a, b, c]) := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_append, List.count_nil]
  omega

private theorem derivesRepeatedFinalToInitial
    (initial : Nat) (middle : List Nat) (final : Nat)
    (initialCount :
      (wordOfEndpoints initial middle final).toList.count initial = 2)
    (finalCount :
      (wordOfEndpoints initial middle final).toList.count final = 2) :
    ∃ switchedMiddle,
      Derives basis
        (wordOfEndpoints initial middle final)
        (wordOfEndpoints initial switchedMiddle initial) ∧
      (wordOfEndpoints initial middle final).toList.Perm
        (wordOfEndpoints initial switchedMiddle initial).toList := by
  by_cases endpoints : initial = final
  · subst final
    exact ⟨middle, Derives.refl _, List.Perm.refl _⟩
  · have middleInitialCount : middle.count initial = 1 := by
      simp only [toList_wordOfEndpoints, List.count_cons,
        List.count_append] at initialCount
      simp [endpoints, Ne.symm endpoints] at initialCount
      omega
    have middleFinalCount : middle.count final = 1 := by
      simp only [toList_wordOfEndpoints, List.count_cons,
        List.count_append] at finalCount
      simp [endpoints, Ne.symm endpoints] at finalCount
      omega
    have initialMem : initial ∈ middle :=
      List.count_pos_iff.mp (by omega)
    have finalCountAfterInitial :
        (middle.erase initial).count final = 1 := by
      rw [List.count_erase_of_ne (Ne.symm endpoints),
        middleFinalCount]
    have finalMemAfterInitial : final ∈ middle.erase initial :=
      List.count_pos_iff.mp (by omega)
    let rest := (middle.erase initial).erase final
    have arrangeFront :
        middle.Perm (initial :: final :: rest) := by
      exact (List.perm_cons_erase initialMem).trans <|
        List.Perm.cons initial <| by
          simpa [rest] using
            List.perm_cons_erase finalMemAfterInitial
    have arrange :
        middle.Perm (initial :: rest ++ [final]) :=
      arrangeFront.trans <|
        List.Perm.cons initial (perm_cons_to_end final rest)
    have arranged :=
      derivesMiddlePermutation initial final arrange
    let switchedMiddle := rest ++ [final, final]
    have switchRaw :
        Derives basis
          (wordOfEndpoints initial (initial :: rest ++ [final]) final)
          (wordOfEndpoints initial (rest ++ [final, final]) initial) := by
      cases rest with
      | nil =>
          simpa [wordOfEndpoints, Word.append,
            Word.singleton, Word.append_assoc] using
              derivesSquareFinalSwitch
                (Word.singleton initial) (Word.singleton final)
      | cons next more =>
          simpa [wordOfEndpoints, wordOfCons,
            Word.append, Word.singleton, Word.append_assoc,
            List.append_assoc] using
              derivesRepeatedFirstFinalSwitch
                (Word.singleton initial) (wordOfCons next more)
                (Word.singleton final)
    have switch :
        Derives basis
          (wordOfEndpoints initial (initial :: rest ++ [final]) final)
          (wordOfEndpoints initial switchedMiddle initial) := by
      simpa [switchedMiddle] using switchRaw
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
    exact ⟨switchedMiddle, Derives.trans arranged switch, fullPerm⟩

private theorem derivesRepeatedFinalToOther
    (initial : Nat) (middle : List Nat) (oldFinal newFinal : Nat)
    (finalsNe : oldFinal ≠ newFinal)
    (initialOldNe : initial ≠ oldFinal)
    (initialNewNe : initial ≠ newFinal)
    (oldCount :
      (wordOfEndpoints initial middle oldFinal).toList.count oldFinal = 2)
    (newCount :
      (wordOfEndpoints initial middle oldFinal).toList.count newFinal = 2) :
    ∃ switchedMiddle,
      Derives basis
        (wordOfEndpoints initial middle oldFinal)
        (wordOfEndpoints initial switchedMiddle newFinal) ∧
      (wordOfEndpoints initial middle oldFinal).toList.Perm
        (wordOfEndpoints initial switchedMiddle newFinal).toList := by
  have middleOldCount : middle.count oldFinal = 1 := by
    simp only [toList_wordOfEndpoints, List.count_cons,
      List.count_append] at oldCount
    simp [initialOldNe, Ne.symm initialOldNe] at oldCount
    omega
  have middleNewCount : middle.count newFinal = 2 := by
    simp only [toList_wordOfEndpoints, List.count_cons,
      List.count_append] at newCount
    simp [finalsNe, initialNewNe, Ne.symm initialNewNe] at newCount
    omega
  have newMem : newFinal ∈ middle :=
    List.count_pos_iff.mp (by omega)
  have firstNewCount :
      (middle.erase newFinal).count newFinal = 1 := by
    rw [List.count_erase_self, middleNewCount]
  have newMemAfter : newFinal ∈ middle.erase newFinal :=
    List.count_pos_iff.mp (by omega)
  have oldCountAfterNew :
      (middle.erase newFinal).count oldFinal = 1 := by
    rw [List.count_erase_of_ne finalsNe, middleOldCount]
  have oldCountAfterTwoNew :
      ((middle.erase newFinal).erase newFinal).count oldFinal = 1 := by
    rw [List.count_erase_of_ne finalsNe, oldCountAfterNew]
  have oldMemAfter :
      oldFinal ∈ (middle.erase newFinal).erase newFinal :=
    List.count_pos_iff.mp (by omega)
  let rest :=
    ((middle.erase newFinal).erase newFinal).erase oldFinal
  have arrangeFront :
      middle.Perm
        (newFinal :: newFinal :: oldFinal :: rest) := by
    exact (List.perm_cons_erase newMem).trans <|
      List.Perm.cons newFinal <|
        (List.perm_cons_erase newMemAfter).trans <|
          List.Perm.cons newFinal <| by
            simpa [rest] using List.perm_cons_erase oldMemAfter
  have arrange :
      middle.Perm (rest ++ [newFinal, newFinal, oldFinal]) :=
    arrangeFront.trans <|
      perm_three_to_end newFinal newFinal oldFinal rest
  have arranged :=
    derivesMiddlePermutation initial oldFinal arrange
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
    have restPerm :=
      List.Perm.append_left rest suffixPerm
    have switchedPerm := List.Perm.cons initial restPerm
    exact outerPerm.trans <| by
      simpa [switchedMiddle, List.append_assoc] using switchedPerm
  exact ⟨switchedMiddle, Derives.trans arranged switch, fullPerm⟩

private def finalSeparator (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 1 else 2

private theorem eval_finalSeparator
    (z : Nat) (pref : List Nat) (final : Nat) :
    finalMarkerThree.semigroup.eval (finalSeparator z)
        (wordOfPrefixFinal pref final) =
      if z ∈ pref then (0 : Fin 3)
      else if final = z then (1 : Fin 3) else (2 : Fin 3) := by
  induction pref with
  | nil =>
      simp [wordOfPrefixFinal, finalSeparator]
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append, ih]
      by_cases hx : x = z
      · subst x
        simp [finalSeparator, finalMarkerThree,
          FiniteTable.semigroup, finalMarkerThreeMul]
      · simp [finalSeparator, finalMarkerThree,
          FiniteTable.semigroup, finalMarkerThreeMul, hx, Ne.symm hx]

private theorem simpleFinal_iff_of_valid
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (valid :
      (Identity.mk
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
          finalMarkerThree.semigroup) :
    ∀ z,
      (final₁ = z ∧ z ∉ initial₁ :: middle₁) ↔
        (final₂ = z ∧ z ∉ initial₂ :: middle₂) := by
  intro z
  have evaluated := valid (finalSeparator z)
  rw [wordOfEndpoints_eq, wordOfEndpoints_eq,
    ← wordOfPrefixFinal_cons, ← wordOfPrefixFinal_cons,
    eval_finalSeparator, eval_finalSeparator] at evaluated
  constructor
  · intro simple₁
    apply Decidable.byContradiction
    intro notSimple₂
    rw [if_neg simple₁.2] at evaluated
    rw [if_pos simple₁.1] at evaluated
    by_cases present₂ : z ∈ initial₂ :: middle₂
    · rw [if_pos present₂] at evaluated
      exact (by decide : (1 : Fin 3) ≠ 0) evaluated
    · have finalNe₂ : final₂ ≠ z := by
        intro finalEq
        exact notSimple₂ ⟨finalEq, present₂⟩
      rw [if_neg present₂, if_neg finalNe₂] at evaluated
      exact (by decide : (1 : Fin 3) ≠ 2) evaluated
  · intro simple₂
    apply Decidable.byContradiction
    intro notSimple₁
    rw [if_neg simple₂.2] at evaluated
    rw [if_pos simple₂.1] at evaluated
    by_cases present₁ : z ∈ initial₁ :: middle₁
    · rw [if_pos present₁] at evaluated
      exact (by decide : (0 : Fin 3) ≠ 1) evaluated
    · have finalNe₁ : final₁ ≠ z := by
        intro finalEq
        exact notSimple₁ ⟨finalEq, present₁⟩
      rw [if_neg present₁, if_neg finalNe₁] at evaluated
      exact (by decide : (2 : Fin 3) ≠ 1) evaluated

private theorem middlePerm_of_wholeCountEq
    (initial final : Nat) (middle₁ middle₂ : List Nat)
    (counts :
      ∀ z,
        (wordOfEndpoints initial middle₁ final).toList.count z =
          (wordOfEndpoints initial middle₂ final).toList.count z) :
    middle₁.Perm middle₂ := by
  rw [List.perm_iff_count]
  intro z
  have h := counts z
  simp only [toList_wordOfEndpoints, List.count_cons,
    List.count_append] at h
  omega

private theorem normalizedFinal_count_two
    (initial : Nat) (middle : List Nat) (final : Nat)
    (repeated : final ∈ initial :: middle) :
    (wordOfEndpoints initial (middleReduce initial final middle)
        final).toList.count final = 2 := by
  have totalAtLeast :
      2 ≤ (wordOfEndpoints initial middle final).toList.count final := by
    have positive : 0 < (initial :: middle).count final :=
      List.count_pos_iff.mpr repeated
    change 2 ≤ ((initial :: middle) ++ [final]).count final
    rw [List.count_append]
    have singletonCount : [final].count final = 1 := by simp
    rw [singletonCount]
    omega
  rw [normal_count]
  exact Nat.min_eq_right totalAtLeast

private theorem normalizedInitial_count_two
    (initial : Nat) (middle : List Nat) (final : Nat)
    (repeated : initial ∈ middle ∨ final = initial) :
    (wordOfEndpoints initial (middleReduce initial final middle)
        final).toList.count initial = 2 := by
  have totalAtLeast :
      2 ≤ (wordOfEndpoints initial middle final).toList.count initial := by
    simp only [toList_wordOfEndpoints, List.count_cons,
      List.count_append]
    rcases repeated with middleMem | finalEq
    · have positive : 0 < middle.count initial :=
        List.count_pos_iff.mpr middleMem
      simp
      omega
    · subst final
      simp
  rw [normal_count]
  exact Nat.min_eq_right totalAtLeast

private theorem normalizedInitial_count_one
    (initial : Nat) (middle : List Nat) (final : Nat)
    (middleAbsent : initial ∉ middle) (finalNe : final ≠ initial) :
    (wordOfEndpoints initial (middleReduce initial final middle)
        final).toList.count initial = 1 := by
  rw [normal_count]
  simp [toList_wordOfEndpoints, List.count_eq_zero.mpr middleAbsent,
    finalNe, Ne.symm finalNe]

/-- Unrestricted completeness for every finite table whose identities factor
through the first/capped-multiplicity and final-marker semantics. -/
theorem basis_complete_of_factors
    (T : FiniteTable)
    (models : Models T.semigroup basis)
    (toFirstCapped :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.SatisfiedBy firstCappedMultiplicityFour.semigroup)
    (toFinalMarker :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.SatisfiedBy finalMarkerThree.semigroup) :
    BasisFor T.semigroup basis := by
  refine ⟨models, ?_⟩
  intro e valid
  have firstValid := toFirstCapped e valid
  have heads := firstCappedValid_head_eq e firstValid
  have cappedCounts :=
    firstCappedValid_capped_count_eq e firstValid
  have finalValid := toFinalMarker e valid
  rcases e with
    ⟨⟨lhsHead, lhsTail⟩, ⟨rhsHead, rhsTail⟩⟩
  simp only at heads
  subst rhsHead
  cases lhsTail with
  | nil =>
      cases rhsTail with
      | nil =>
          exact Derives.refl _
      | cons rhsSecond rhsRest =>
          by_cases secondHead : rhsSecond = lhsHead
          · subst rhsSecond
            have countEq := cappedCounts lhsHead
            simp [Word.toList] at countEq
          · have countEq := cappedCounts rhsSecond
            simp [Word.toList, secondHead, Ne.symm secondHead] at countEq
            omega
  | cons lhsSecond lhsRest =>
      cases rhsTail with
      | nil =>
          by_cases secondHead : lhsSecond = lhsHead
          · subst lhsSecond
            have countEq := cappedCounts lhsHead
            simp [Word.toList] at countEq
          · have countEq := cappedCounts lhsSecond
            simp [Word.toList, secondHead, Ne.symm secondHead] at countEq
      | cons rhsSecond rhsRest =>
          let lhsSplit := splitMiddleFinal lhsSecond lhsRest
          let rhsSplit := splitMiddleFinal rhsSecond rhsRest
          have lhsReconstruct :
              wordOfEndpoints lhsHead lhsSplit.1 lhsSplit.2 =
                ⟨lhsHead, lhsSecond :: lhsRest⟩ := by
            exact wordOfEndpoints_splitMiddleFinal
              lhsHead lhsSecond lhsRest
          have rhsReconstruct :
              wordOfEndpoints lhsHead rhsSplit.1 rhsSplit.2 =
                ⟨lhsHead, rhsSecond :: rhsRest⟩ := by
            exact wordOfEndpoints_splitMiddleFinal
              lhsHead rhsSecond rhsRest
          have lhsNormal :
              Derives basis
                (Word.mk lhsHead (lhsSecond :: lhsRest))
                (wordOfEndpoints lhsHead
                  (middleReduce lhsHead lhsSplit.2 lhsSplit.1)
                  lhsSplit.2) := by
            rw [← lhsReconstruct]
            exact derivesNormalEndpoints
              lhsHead lhsSplit.1 lhsSplit.2
          have rhsNormal :
              Derives basis
                (Word.mk lhsHead (rhsSecond :: rhsRest))
                (wordOfEndpoints lhsHead
                  (middleReduce lhsHead rhsSplit.2 rhsSplit.1)
                  rhsSplit.2) := by
            rw [← rhsReconstruct]
            exact derivesNormalEndpoints
              lhsHead rhsSplit.1 rhsSplit.2
          have normalCountEq :
              ∀ z,
                (wordOfEndpoints lhsHead
                    (middleReduce lhsHead lhsSplit.2 lhsSplit.1)
                    lhsSplit.2).toList.count z =
                  (wordOfEndpoints lhsHead
                    (middleReduce lhsHead rhsSplit.2 rhsSplit.1)
                    rhsSplit.2).toList.count z := by
            intro z
            rw [normal_count, normal_count,
              lhsReconstruct, rhsReconstruct]
            exact cappedCounts z
          have endpointFinalValid :
              (Identity.mk
                (wordOfEndpoints lhsHead lhsSplit.1 lhsSplit.2)
                (wordOfEndpoints lhsHead rhsSplit.1 rhsSplit.2)).SatisfiedBy
                  finalMarkerThree.semigroup := by
            rw [lhsReconstruct, rhsReconstruct]
            exact finalValid
          have simpleFinalIff :=
            simpleFinal_iff_of_valid
              lhsHead lhsSplit.1 lhsSplit.2
              lhsHead rhsSplit.1 rhsSplit.2
              endpointFinalValid
          by_cases lhsSimple :
              lhsSplit.2 ∉ lhsHead :: lhsSplit.1
          · have rightSimple :=
              (simpleFinalIff lhsSplit.2).mp ⟨rfl, lhsSimple⟩
            have finalsEq : rhsSplit.2 = lhsSplit.2 :=
              rightSimple.1
            rw [finalsEq] at rhsNormal normalCountEq
            have middlePerm :=
              middlePerm_of_wholeCountEq lhsHead lhsSplit.2
                (middleReduce lhsHead lhsSplit.2 lhsSplit.1)
                (middleReduce lhsHead lhsSplit.2 rhsSplit.1)
                normalCountEq
            exact Derives.trans lhsNormal <|
              Derives.trans
                (derivesMiddlePermutation
                  lhsHead lhsSplit.2 middlePerm)
                (Derives.symm rhsNormal)
          · have lhsRepeated :
                lhsSplit.2 ∈ lhsHead :: lhsSplit.1 := by
              exact Decidable.not_not.mp lhsSimple
            have rhsRepeated :
                rhsSplit.2 ∈ lhsHead :: rhsSplit.1 := by
              apply Decidable.byContradiction
              intro rhsSimple
              have leftSimple :=
                (simpleFinalIff rhsSplit.2).mpr ⟨rfl, rhsSimple⟩
              exact leftSimple.2 <| by
                simpa [leftSimple.1] using lhsRepeated
            by_cases firstRepeated :
                lhsHead ∈ lhsSplit.1 ∨ lhsSplit.2 = lhsHead
            · have lhsInitialCount :=
                normalizedInitial_count_two
                  lhsHead lhsSplit.1 lhsSplit.2 firstRepeated
              have rhsInitialCount :
                  (wordOfEndpoints lhsHead
                    (middleReduce lhsHead rhsSplit.2 rhsSplit.1)
                    rhsSplit.2).toList.count lhsHead = 2 := by
                rw [← normalCountEq lhsHead]
                exact lhsInitialCount
              have lhsFinalCount :=
                normalizedFinal_count_two
                  lhsHead lhsSplit.1 lhsSplit.2 lhsRepeated
              have rhsFinalCount :=
                normalizedFinal_count_two
                  lhsHead rhsSplit.1 rhsSplit.2 rhsRepeated
              obtain
                ⟨lhsSwitched, lhsSwitch, lhsPerm⟩ :=
                  derivesRepeatedFinalToInitial
                    lhsHead
                    (middleReduce lhsHead lhsSplit.2 lhsSplit.1)
                    lhsSplit.2 lhsInitialCount lhsFinalCount
              obtain
                ⟨rhsSwitched, rhsSwitch, rhsPerm⟩ :=
                  derivesRepeatedFinalToInitial
                    lhsHead
                    (middleReduce lhsHead rhsSplit.2 rhsSplit.1)
                    rhsSplit.2 rhsInitialCount rhsFinalCount
              have switchedCountEq :
                  ∀ z,
                    (wordOfEndpoints lhsHead lhsSwitched lhsHead).toList.count z =
                      (wordOfEndpoints lhsHead rhsSwitched lhsHead).toList.count z := by
                intro z
                have lhsPermCount :=
                  (List.perm_iff_count.mp lhsPerm) z
                have rhsPermCount :=
                  (List.perm_iff_count.mp rhsPerm) z
                exact lhsPermCount.symm.trans <|
                  (normalCountEq z).trans rhsPermCount
              have switchedMiddlePerm :=
                middlePerm_of_wholeCountEq
                  lhsHead lhsHead lhsSwitched rhsSwitched
                  switchedCountEq
              exact Derives.trans lhsNormal <|
                Derives.trans lhsSwitch <|
                  Derives.trans
                    (derivesMiddlePermutation
                      lhsHead lhsHead switchedMiddlePerm) <|
                    Derives.trans
                      (Derives.symm rhsSwitch)
                      (Derives.symm rhsNormal)
            · have lhsMiddleHeadAbsent : lhsHead ∉ lhsSplit.1 :=
                fun member => firstRepeated (Or.inl member)
              have lhsFinalHeadNe : lhsSplit.2 ≠ lhsHead :=
                fun equal => firstRepeated (Or.inr equal)
              have lhsInitialCount :=
                normalizedInitial_count_one
                  lhsHead lhsSplit.1 lhsSplit.2
                  lhsMiddleHeadAbsent lhsFinalHeadNe
              by_cases finalsEq : lhsSplit.2 = rhsSplit.2
              · rw [← finalsEq] at rhsNormal normalCountEq
                have middlePerm :=
                  middlePerm_of_wholeCountEq lhsHead lhsSplit.2
                    (middleReduce lhsHead lhsSplit.2 lhsSplit.1)
                    (middleReduce lhsHead lhsSplit.2 rhsSplit.1)
                    normalCountEq
                exact Derives.trans lhsNormal <|
                  Derives.trans
                    (derivesMiddlePermutation
                      lhsHead lhsSplit.2 middlePerm)
                    (Derives.symm rhsNormal)
              · have lhsFinalCount :=
                  normalizedFinal_count_two
                    lhsHead lhsSplit.1 lhsSplit.2 lhsRepeated
                have rhsFinalCount :=
                  normalizedFinal_count_two
                    lhsHead rhsSplit.1 rhsSplit.2 rhsRepeated
                have lhsNewCount :
                    (wordOfEndpoints lhsHead
                      (middleReduce lhsHead lhsSplit.2 lhsSplit.1)
                      lhsSplit.2).toList.count rhsSplit.2 = 2 := by
                  rw [normalCountEq rhsSplit.2]
                  exact rhsFinalCount
                have lhsOldNe : lhsHead ≠ lhsSplit.2 :=
                  Ne.symm lhsFinalHeadNe
                have lhsNewNe : lhsHead ≠ rhsSplit.2 := by
                  intro equal
                  have countAtHead := lhsNewCount
                  rw [← equal] at countAtHead
                  omega
                obtain
                  ⟨switchedMiddle, switch, switchPerm⟩ :=
                    derivesRepeatedFinalToOther
                      lhsHead
                      (middleReduce lhsHead lhsSplit.2 lhsSplit.1)
                      lhsSplit.2 rhsSplit.2 finalsEq
                      lhsOldNe lhsNewNe lhsFinalCount lhsNewCount
                have switchedCountEq :
                    ∀ z,
                      (wordOfEndpoints lhsHead switchedMiddle
                          rhsSplit.2).toList.count z =
                        (wordOfEndpoints lhsHead
                          (middleReduce lhsHead rhsSplit.2 rhsSplit.1)
                          rhsSplit.2).toList.count z := by
                  intro z
                  have switchCount :=
                    (List.perm_iff_count.mp switchPerm) z
                  exact switchCount.symm.trans (normalCountEq z)
                have switchedMiddlePerm :=
                  middlePerm_of_wholeCountEq
                    lhsHead rhsSplit.2 switchedMiddle
                    (middleReduce lhsHead rhsSplit.2 rhsSplit.1)
                    switchedCountEq
                exact Derives.trans lhsNormal <|
                  Derives.trans switch <|
                    Derives.trans
                      (derivesMiddlePermutation
                        lhsHead rhsSplit.2 switchedMiddlePerm)
                      (Derives.symm rhsNormal)

end SemigroupBasis.CoRoots.S5_344

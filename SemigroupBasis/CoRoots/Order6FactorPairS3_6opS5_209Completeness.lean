import SemigroupBasis.CoRoots.Order6FactorPairS2S594Normal
import SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Normal

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Normal

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev endpointWord :=
  _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints

private theorem derivesPublicMiddlePermutation
    (initial final : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives correctedBasis
      (endpointWord initial left final)
      (endpointWord initial right final) :=
  _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.derivesMiddlePermutationOfOpenSwap
    derivesOpenInteriorSwap initial final permutation

private def word (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def instantiateTwoWords
    (x y : Word Nat) : Nat -> Word Nat
  | 0 => x
  | 1 => y
  | n + 2 => Word.singleton (n + 2)

private def instantiateThreeWords
    (x y z : Word Nat) : Nat -> Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private def wordOfPrefixFinal : List Nat -> Nat -> Word Nat
  | [], final => Word.singleton final
  | head :: tail, final => Word.mk head (tail ++ [final])

@[simp]
private theorem toList_wordOfPrefixFinal
    (wordPrefix : List Nat) (final : Nat) :
    (wordOfPrefixFinal wordPrefix final).toList = wordPrefix ++ [final] := by
  cases wordPrefix <;> simp [wordOfPrefixFinal, Word.toList, Word.singleton]

@[simp]
private theorem wordOfPrefixFinal_cons
    (head : Nat) (tail : List Nat) (final : Nat) :
    wordOfPrefixFinal (head :: tail) final =
      Word.singleton head ++ wordOfPrefixFinal tail final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal, toList_wordOfPrefixFinal]
  rfl

private theorem endpointWord_eq
    (initial : Nat) (middle : List Nat) (final : Nat) :
    endpointWord initial middle final =
      Word.singleton initial ++ wordOfPrefixFinal middle final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal]
  rfl

private theorem permConsToEnd (x : Nat) :
    ∀ letters : List Nat, (x :: letters).Perm (letters ++ [x])
  | [] => List.Perm.refl _
  | y :: ys =>
      (List.Perm.swap y x ys).trans <|
        List.Perm.cons y (permConsToEnd x ys)

private theorem permTwoToEnd (x : Nat) (rest : List Nat) :
    (x :: x :: rest).Perm (rest ++ [x, x]) := by
  apply (List.Perm.cons x (permConsToEnd x rest)).trans
  simpa [List.append_assoc] using permConsToEnd x (rest ++ [x])

private theorem permSwapAround (first last : Nat) (middle : List Nat) :
    (first :: middle ++ [last]).Perm
      (last :: middle ++ [first]) := by
  have moveFirst := permConsToEnd first (middle ++ [last])
  have moveLast :=
    (permConsToEnd last middle).symm.append_right [first]
  exact moveFirst.trans <| by
    simpa [List.append_assoc] using moveLast

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-! ## Balanced consequences of the corrected basis -/

private theorem basisTripleClosedContraction :
    Derives correctedBasis
      (word 0 [0, 0, 1, 0])
      (word 0 [0, 1, 0]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [0, 0, 1, 0])
    (word 0 [0, 1, 0]))
    (by decide)

private theorem basisSquareFinalSwitch :
    Derives correctedBasis
      (word 0 [0, 1, 1])
      (word 0 [1, 1, 0]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [0, 1, 1])
    (word 0 [1, 1, 0]))
    (by decide)

private theorem basisSquareInitialSwitch :
    Derives correctedBasis
      (word 0 [0, 1, 1])
      (word 1 [0, 0, 1]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [0, 1, 1])
    (word 1 [0, 0, 1]))
    (by decide)

private theorem basisAttachmentFinal :
    Derives correctedBasis
      (word 0 [0, 1, 2, 1])
      (word 0 [1, 1, 2, 0]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [0, 1, 2, 1])
    (word 0 [1, 1, 2, 0]))
    (by decide)

private theorem basisAttachmentInitial :
    Derives correctedBasis
      (word 0 [0, 1, 2, 1])
      (word 1 [0, 0, 2, 1]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [0, 1, 2, 1])
    (word 1 [0, 0, 2, 1]))
    (by decide)

private theorem derivesTripleClosedContraction
    (x middle : Word Nat) :
    Derives correctedBasis
      ((((x ++ x) ++ x) ++ middle) ++ x)
      (((x ++ x) ++ middle) ++ x) := by
  have substituted :=
    Derives.subst basisTripleClosedContraction
      (instantiateTwoWords x middle)
  simpa [word, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesSquareFinalSwitch
    (x y : Word Nat) :
    Derives correctedBasis
      ((x ++ x) ++ (y ++ y))
      (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSquareFinalSwitch
      (instantiateTwoWords x y)
  simpa [word, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesSquareInitialSwitch
    (x y : Word Nat) :
    Derives correctedBasis
      ((x ++ x) ++ (y ++ y))
      (((y ++ x) ++ x) ++ y) := by
  have substituted :=
    Derives.subst basisSquareInitialSwitch
      (instantiateTwoWords x y)
  simpa [word, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesAttachmentFinal
    (x y z : Word Nat) :
    Derives correctedBasis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ y) ++ y) ++ z) ++ x) := by
  have substituted :=
    Derives.subst basisAttachmentFinal
      (instantiateThreeWords x y z)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesAttachmentInitial
    (x y z : Word Nat) :
    Derives correctedBasis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((y ++ x) ++ x) ++ z) ++ y) := by
  have substituted :=
    Derives.subst basisAttachmentInitial
      (instantiateThreeWords x y z)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The corrected basis is sound in the endpoint separator used below. -/
theorem correctedModels_simpleEndpoints :
    Models simpleEndpointsFour.semigroup correctedBasis := by
  intro identity member
  exact valid_simpleEndpoints_of_factors identity
    (correctedModels_s3_6_opposite identity member)
    (correctedModels_s5_209 identity member)

/-! ## Endpoint-aware cap-three normalization -/

/-- Retain at most three copies in the whole word, counting the two protected
endpoints before deciding whether to retain an interior occurrence. -/
def endpointCapThreeReduce
    (initial final : Nat) : List Nat -> List Nat
  | [] => []
  | x :: xs =>
      let reduced := endpointCapThreeReduce initial final xs
      if _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final x + reduced.count x < 3 then
        x :: reduced
      else
        reduced

theorem endpointCapThreeReduce_total_le_three
    (initial final tested : Nat) (middle : List Nat) :
    _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final tested +
        (endpointCapThreeReduce initial final middle).count tested <= 3 := by
  induction middle with
  | nil =>
      simp only [endpointCapThreeReduce, List.count_nil, Nat.add_zero]
      have endpointBound :=
        _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies_le_two
          initial final tested
      omega
  | cons x xs ih =>
      simp only [endpointCapThreeReduce]
      split <;> rename_i small
      · by_cases same : tested = x
        · subst tested
          rw [List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm same)]
          exact ih
      · exact ih

theorem endpointCapThreeReduce_total_capped
    (initial final tested : Nat) (middle : List Nat) :
    min
        (_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final tested +
          (endpointCapThreeReduce initial final middle).count tested) 3 =
      min
        (_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final tested +
          middle.count tested) 3 := by
  induction middle with
  | nil =>
      simp [endpointCapThreeReduce]
  | cons x xs ih =>
      simp only [endpointCapThreeReduce]
      split <;> rename_i small
      · by_cases same : tested = x
        · subst tested
          rw [List.count_cons_self, List.count_cons_self]
          have bound :=
            endpointCapThreeReduce_total_le_three
              initial final x xs
          omega
        · rw [List.count_cons_of_ne (Ne.symm same),
            List.count_cons_of_ne (Ne.symm same)]
          exact ih
      · by_cases same : tested = x
        · subst tested
          rw [List.count_cons_self]
          have bound :=
            endpointCapThreeReduce_total_le_three
              initial final x xs
          omega
        · rw [List.count_cons_of_ne (Ne.symm same)]
          exact ih

theorem endpointCapThreeReduce_whole_count
    (initial : Nat) (middle : List Nat) (final tested : Nat) :
    (endpointWord initial
      (endpointCapThreeReduce initial final middle) final).toList.count tested =
      min
        ((endpointWord initial middle final).toList.count tested) 3 := by
  rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints]
  have capped :=
    endpointCapThreeReduce_total_capped
      initial final tested middle
  have bound :=
    endpointCapThreeReduce_total_le_three
      initial final tested middle
  omega

theorem endpointCapThreeReduce_normal_counts_eq
    {leftInitial leftFinal rightInitial rightFinal : Nat}
    {leftMiddle rightMiddle : List Nat}
    (capped : forall tested,
      min
          ((endpointWord leftInitial leftMiddle leftFinal).toList.count
            tested) 3 =
        min
          ((endpointWord rightInitial rightMiddle rightFinal).toList.count
            tested) 3) :
    forall tested,
      (endpointWord leftInitial
          (endpointCapThreeReduce
            leftInitial leftFinal leftMiddle)
          leftFinal).toList.count tested =
        (endpointWord rightInitial
          (endpointCapThreeReduce
            rightInitial rightFinal rightMiddle)
          rightFinal).toList.count tested := by
  intro tested
  rw [endpointCapThreeReduce_whole_count,
    endpointCapThreeReduce_whole_count, capped tested]

private theorem derivesDeleteFourInterior
    (initial final selected : Nat) (pre reduced : List Nat)
    (countEq : reduced.count selected = 3) :
    Derives correctedBasis
      (endpointWord initial (pre ++ selected :: reduced) final)
      (endpointWord initial (pre ++ reduced) final) := by
  let remainder :=
    ((reduced.erase selected).erase selected).erase selected
  have firstCount : (reduced.erase selected).count selected = 2 := by
    rw [List.count_erase_self, countEq]
  have secondCount :
      ((reduced.erase selected).erase selected).count selected = 1 := by
    rw [List.count_erase_self, firstCount]
  have remainderCount : remainder.count selected = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, secondCount]
  have sourcePerm :
      (pre ++ selected :: reduced).Perm
        (selected :: selected :: selected :: selected ::
          pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = selected
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have targetPerm :
      (pre ++ reduced).Perm
        (selected :: selected :: selected :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = selected
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have contraction :=
    Derives.appendRight
      (Derives.prepend (Word.singleton initial)
        (derivesFourToThree (Word.singleton selected)))
      (wordOfPrefixFinal (pre ++ remainder) final)
  have contracted :
      Derives correctedBasis
        (endpointWord initial
          (selected :: selected :: selected :: selected ::
            pre ++ remainder) final)
        (endpointWord initial
          (selected :: selected :: selected :: pre ++ remainder) final) := by
    simpa only [List.cons_append, endpointWord_eq,
      wordOfPrefixFinal_cons, Word.append_assoc] using contraction
  exact Derives.trans
    (derivesPublicMiddlePermutation initial final sourcePerm) <|
      Derives.trans contracted <|
        derivesPublicMiddlePermutation initial final targetPerm.symm

private theorem derivesDeleteInitialExcess
    (initial final : Nat) (pre reduced : List Nat)
    (countEq : reduced.count initial = 2) :
    Derives correctedBasis
      (endpointWord initial (pre ++ initial :: reduced) final)
      (endpointWord initial (pre ++ reduced) final) := by
  let remainder := (reduced.erase initial).erase initial
  have firstCount : (reduced.erase initial).count initial = 1 := by
    rw [List.count_erase_self, countEq]
  have remainderCount : remainder.count initial = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, firstCount]
  have sourcePerm :
      (pre ++ initial :: reduced).Perm
        (initial :: initial :: initial :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = initial
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have targetPerm :
      (pre ++ reduced).Perm
        (initial :: initial :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = initial
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have contraction :=
    Derives.appendRight
      (derivesFourToThree (Word.singleton initial))
      (wordOfPrefixFinal (pre ++ remainder) final)
  have contracted :
      Derives correctedBasis
        (endpointWord initial
          (initial :: initial :: initial :: pre ++ remainder) final)
        (endpointWord initial
          (initial :: initial :: pre ++ remainder) final) := by
    simpa only [List.cons_append, endpointWord_eq,
      wordOfPrefixFinal_cons, Word.append_assoc] using contraction
  exact Derives.trans
    (derivesPublicMiddlePermutation initial final sourcePerm) <|
      Derives.trans contracted <|
        derivesPublicMiddlePermutation initial final targetPerm.symm

private theorem derivesDeleteFinalExcess
    (initial final : Nat) (pre reduced : List Nat)
    (countEq : reduced.count final = 2) :
    Derives correctedBasis
      (endpointWord initial (pre ++ final :: reduced) final)
      (endpointWord initial (pre ++ reduced) final) := by
  let remainder := (reduced.erase final).erase final
  have firstCount : (reduced.erase final).count final = 1 := by
    rw [List.count_erase_self, countEq]
  have remainderCount : remainder.count final = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, firstCount]
  have sourcePerm :
      (pre ++ final :: reduced).Perm
        ((pre ++ remainder) ++ [final, final, final]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = final
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have targetPerm :
      (pre ++ reduced).Perm
        ((pre ++ remainder) ++ [final, final]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = final
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have contraction :=
    Derives.prepend (wordOfCons initial (pre ++ remainder))
      (derivesFourToThree (Word.singleton final))
  have contracted :
      Derives correctedBasis
        (endpointWord initial
          ((pre ++ remainder) ++ [final, final, final]) final)
        (endpointWord initial
          ((pre ++ remainder) ++ [final, final]) final) := by
    have sourceShape :
        wordOfCons initial (pre ++ remainder) ++
            (((Word.singleton final ++ Word.singleton final) ++
              Word.singleton final) ++ Word.singleton final) =
          endpointWord initial
            ((pre ++ remainder) ++ [final, final, final]) final := by
      apply Word.toList_injective
      simp [endpointWord,
        _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
        wordOfCons, Word.toList, List.append_assoc]
    have targetShape :
        wordOfCons initial (pre ++ remainder) ++
            ((Word.singleton final ++ Word.singleton final) ++
              Word.singleton final) =
          endpointWord initial
            ((pre ++ remainder) ++ [final, final]) final := by
      apply Word.toList_injective
      simp [endpointWord,
        _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
        wordOfCons, Word.toList, List.append_assoc]
    rw [← sourceShape, ← targetShape]
    exact contraction
  exact Derives.trans
    (derivesPublicMiddlePermutation initial final sourcePerm) <|
      Derives.trans contracted <|
        derivesPublicMiddlePermutation initial final targetPerm.symm

private theorem derivesDeleteClosedExcess
    (endpoint : Nat) (pre reduced : List Nat)
    (countEq : reduced.count endpoint = 1) :
    Derives correctedBasis
      (endpointWord endpoint (pre ++ endpoint :: reduced) endpoint)
      (endpointWord endpoint (pre ++ reduced) endpoint) := by
  let remainder := reduced.erase endpoint
  have remainderCount : remainder.count endpoint = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, countEq]
  have sourcePerm :
      (pre ++ endpoint :: reduced).Perm
        (endpoint :: endpoint :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = endpoint
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have targetPerm :
      (pre ++ reduced).Perm
        (endpoint :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = endpoint
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have arranged :=
    derivesPublicMiddlePermutation endpoint endpoint sourcePerm
  have contraction :
      Derives correctedBasis
        (endpointWord endpoint
          (endpoint :: endpoint :: pre ++ remainder) endpoint)
        (endpointWord endpoint
          (endpoint :: pre ++ remainder) endpoint) := by
    cases restEq : pre ++ remainder with
    | nil =>
        simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
          restEq, Word.append, Word.singleton,
          Word.append_assoc] using
            derivesFourToThree (Word.singleton endpoint)
    | cons next rest =>
        have contracted :=
          derivesTripleClosedContraction
            (Word.singleton endpoint) (wordOfCons next rest)
        simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
          restEq, wordOfCons, Word.append, Word.singleton,
          Word.append_assoc, List.append_assoc] using contracted
  exact arranged.trans <|
    contraction.trans <|
      derivesPublicMiddlePermutation endpoint endpoint targetPerm.symm

private theorem derivesDeleteCapThreeExcess
    (initial final selected : Nat) (pre reduced : List Nat)
    (totalEq :
      _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final selected +
          reduced.count selected = 3) :
    Derives correctedBasis
      (endpointWord initial (pre ++ selected :: reduced) final)
      (endpointWord initial (pre ++ reduced) final) := by
  by_cases atInitial : selected = initial
  · subst selected
    by_cases closed : initial = final
    · subst final
      have countEq : reduced.count initial = 1 := by
        simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies] at totalEq
        omega
      exact derivesDeleteClosedExcess initial pre reduced countEq
    · have countEq : reduced.count initial = 2 := by
        simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies, closed, Ne.symm closed] at totalEq
        omega
      exact derivesDeleteInitialExcess initial final pre reduced countEq
  · by_cases atFinal : selected = final
    · subst selected
      have countEq : reduced.count final = 2 := by
        simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies, atInitial,
          Ne.symm atInitial] at totalEq
        omega
      exact derivesDeleteFinalExcess initial final pre reduced countEq
    · have countEq : reduced.count selected = 3 := by
        simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies, atInitial, atFinal,
          Ne.symm atInitial, Ne.symm atFinal] at totalEq
        omega
      exact derivesDeleteFourInterior
        initial final selected pre reduced countEq

private theorem derivesNormalizeCapThreeAux :
    forall (initial : Nat) (pre middle : List Nat) (final : Nat),
      Derives correctedBasis
        (endpointWord initial (pre ++ middle) final)
        (endpointWord initial
          (pre ++ endpointCapThreeReduce initial final middle) final)
  | initial, pre, [], final => by
      exact Derives.refl _
  | initial, pre, selected :: tail, final => by
      have tailNormal :=
        derivesNormalizeCapThreeAux
          initial (pre ++ [selected]) tail final
      let reduced := endpointCapThreeReduce initial final tail
      have firstStep :
          Derives correctedBasis
            (endpointWord initial (pre ++ selected :: tail) final)
            (endpointWord initial (pre ++ selected :: reduced) final) := by
        simpa [reduced, List.append_assoc] using tailNormal
      by_cases small :
          _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final selected +
              reduced.count selected < 3
      · have reduceEq :
            endpointCapThreeReduce initial final (selected :: tail) =
              selected :: reduced := by
          simp [endpointCapThreeReduce, reduced, small]
        rw [reduceEq]
        exact firstStep
      · have totalLe :
            _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final selected +
                reduced.count selected <= 3 := by
          simpa [reduced] using
            endpointCapThreeReduce_total_le_three
              initial final selected tail
        have totalEq :
            _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final selected +
                reduced.count selected = 3 := by
          omega
        have reduceEq :
            endpointCapThreeReduce initial final (selected :: tail) =
              reduced := by
          simp [endpointCapThreeReduce, reduced, small]
        rw [reduceEq]
        exact firstStep.trans <|
          derivesDeleteCapThreeExcess
            initial final selected pre reduced totalEq
termination_by
  _ _ middle _ => middle.length

/-- Normalize all multiplicities to their values capped at three while
preserving both endpoint positions. -/
theorem derivesNormalizeCapThree
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives correctedBasis
      (endpointWord initial middle final)
      (endpointWord initial
        (endpointCapThreeReduce initial final middle) final) := by
  simpa using derivesNormalizeCapThreeAux initial [] middle final

/-! ## Balanced endpoint alignment -/

private theorem repeatedInitial_count_two
    (initial : Nat) (middle : List Nat) (final : Nat)
    (repeated : initial ∈ middle ∨ final = initial) :
    2 <= (endpointWord initial middle final).toList.count initial := by
  rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints]
  rcases repeated with member | same
  · have positive : 0 < middle.count initial :=
      List.count_pos_iff.mpr member
    simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies]
    omega
  · subst final
    simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies]

private theorem repeatedFinal_count_two
    (initial : Nat) (middle : List Nat) (final : Nat)
    (repeated : final ∈ initial :: middle) :
    2 <= (endpointWord initial middle final).toList.count final := by
  simp only [endpointWord,
    _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints,
    List.count_cons, List.count_append, List.count_singleton]
  have positive : 0 < (initial :: middle).count final :=
    List.count_pos_iff.mpr repeated
  simp only [List.count_cons] at positive
  by_cases endpoints : initial = final
  · subst final
    simp
  · simp [endpoints, Ne.symm endpoints] at positive ⊢
    omega

private theorem fullPerm_of_middle_arrangement
    (sourceInitial sourceFinal targetInitial targetFinal : Nat)
    (sourceMiddle targetMiddle arrangedSource arrangedTarget : List Nat)
    (sourceArrangement : sourceMiddle.Perm arrangedSource)
    (targetArrangement : targetMiddle.Perm arrangedTarget)
    (arranged :
      (endpointWord sourceInitial arrangedSource sourceFinal).toList.Perm
        (endpointWord targetInitial arrangedTarget targetFinal).toList) :
    (endpointWord sourceInitial sourceMiddle sourceFinal).toList.Perm
      (endpointWord targetInitial targetMiddle targetFinal).toList := by
  have sourceOuter :
      (endpointWord sourceInitial sourceMiddle sourceFinal).toList.Perm
        (endpointWord sourceInitial arrangedSource sourceFinal).toList := by
    simpa only [endpointWord,
      _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints] using
        List.Perm.cons sourceInitial
          (sourceArrangement.append_right [sourceFinal])
  have targetOuter :
      (endpointWord targetInitial targetMiddle targetFinal).toList.Perm
        (endpointWord targetInitial arrangedTarget targetFinal).toList := by
    simpa only [endpointWord,
      _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints] using
        List.Perm.cons targetInitial
          (targetArrangement.append_right [targetFinal])
  exact sourceOuter.trans <| arranged.trans targetOuter.symm

private theorem derivesInitialSwitchPreservingFinal
    (old new : Nat) (middle : List Nat) (final : Nat)
    (different : old ≠ new)
    (finalOldNe : final ≠ old)
    (oldRepeated : old ∈ middle ∨ final = old)
    (newMultiple :
      2 <= (endpointWord old middle final).toList.count new) :
    ∃ switchedMiddle,
      Derives correctedBasis
        (endpointWord old middle final)
        (endpointWord new switchedMiddle final) ∧
      (endpointWord old middle final).toList.Perm
        (endpointWord new switchedMiddle final).toList := by
  have oldMem : old ∈ middle := by
    rcases oldRepeated with member | same
    · exact member
    · exact False.elim (finalOldNe same)
  by_cases finalNew : final = new
  · subst final
    have newPositive : 0 < middle.count new := by
      rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints] at newMultiple
      simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies, different,
        Ne.symm different] at newMultiple
      omega
    have newMemAfterOld : new ∈ middle.erase old := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_of_ne (Ne.symm different)]
      exact newPositive
    let rest := (middle.erase old).erase new
    have arrangement :
        middle.Perm (old :: new :: rest) :=
      (List.perm_cons_erase oldMem).trans <|
        List.Perm.cons old <| by
          simpa [rest] using List.perm_cons_erase newMemAfterOld
    cases restEq : rest with
    | nil =>
        let switchedMiddle := [old, old]
        have arranged :=
          derivesPublicMiddlePermutation old new arrangement
        have switched :
            Derives correctedBasis
              (endpointWord old [old, new] new)
              (endpointWord new switchedMiddle new) := by
          simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
            switchedMiddle, Word.append, Word.singleton,
            Word.append_assoc] using
              derivesSquareInitialSwitch
                (Word.singleton old) (Word.singleton new)
        have sourceArrangement :
            middle.Perm [old, new] := by
          simpa [restEq] using arrangement
        have targetArrangement :
            switchedMiddle.Perm [old, old] := List.Perm.refl _
        have endpointPermutation :
            (endpointWord old [old, new] new).toList.Perm
              (endpointWord new [old, old] new).toList := by
          have literalPermutation :
              [old, old, new, new].Perm [new, old, old, new] :=
            (permConsToEnd new [old, old]).symm.append_right [new]
          simpa only [endpointWord,
            _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints] using
              literalPermutation
        have switchedNil :
            Derives correctedBasis
              (endpointWord old (old :: new :: rest) new)
              (endpointWord new switchedMiddle new) := by
          simpa [restEq] using switched
        exact ⟨switchedMiddle, arranged.trans switchedNil,
          fullPerm_of_middle_arrangement
            old new new new middle switchedMiddle
            [old, new] [old, old]
            sourceArrangement targetArrangement endpointPermutation⟩
    | cons next tail =>
        let switchedMiddle := old :: old :: next :: tail
        have arranged :=
          derivesPublicMiddlePermutation old new arrangement
        have switched :
            Derives correctedBasis
              (endpointWord old (old :: new :: next :: tail) new)
              (endpointWord new switchedMiddle new) := by
          simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
            switchedMiddle, wordOfCons, Word.append,
            Word.singleton, Word.append_assoc] using
              derivesAttachmentInitial
                (Word.singleton old) (Word.singleton new)
                (wordOfCons next tail)
        have sourceArrangement :
            middle.Perm (old :: new :: next :: tail) := by
          simpa [restEq] using arrangement
        have targetArrangement :
            switchedMiddle.Perm (old :: old :: next :: tail) :=
          List.Perm.refl _
        have endpointPermutation :
            (endpointWord old
              (old :: new :: next :: tail) new).toList.Perm
              (endpointWord new
                (old :: old :: next :: tail) new).toList := by
          have literalPermutation :=
            (permConsToEnd new [old, old]).symm.append_right
              (next :: tail ++ [new])
          simpa only [endpointWord,
            _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints] using
              literalPermutation
        have arrangedCons :
            Derives correctedBasis
              (endpointWord old middle new)
              (endpointWord old (old :: new :: next :: tail) new) := by
          simpa [restEq] using arranged
        exact ⟨switchedMiddle, arrangedCons.trans switched,
          fullPerm_of_middle_arrangement
            old new new new middle switchedMiddle
            (old :: new :: next :: tail)
            (old :: old :: next :: tail)
            sourceArrangement targetArrangement endpointPermutation⟩
  · have finalNewNe : final ≠ new := finalNew
    have newAtLeastTwo : 2 <= middle.count new := by
      rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints] at newMultiple
      simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies, different, finalNewNe,
        Ne.symm different, Ne.symm finalNewNe] at newMultiple
      exact newMultiple
    have newMemAfterOld : new ∈ middle.erase old := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_of_ne (Ne.symm different)]
      omega
    have newMemAfterOldNew :
        new ∈ (middle.erase old).erase new := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_self,
        List.count_erase_of_ne (Ne.symm different)]
      omega
    let rest := ((middle.erase old).erase new).erase new
    have arrangement :
        middle.Perm (old :: new :: new :: rest) :=
      (List.perm_cons_erase oldMem).trans <|
        List.Perm.cons old <|
          (List.perm_cons_erase newMemAfterOld).trans <|
            List.Perm.cons new <| by
              simpa [rest] using
                List.perm_cons_erase newMemAfterOldNew
    let switchedMiddle := old :: old :: new :: rest
    have arranged :=
      derivesPublicMiddlePermutation old final arrangement
    have switchedRaw :=
      Derives.appendRight
        (derivesSquareInitialSwitch
          (Word.singleton old) (Word.singleton new))
        (wordOfPrefixFinal rest final)
    have switched :
        Derives correctedBasis
          (endpointWord old (old :: new :: new :: rest) final)
          (endpointWord new switchedMiddle final) := by
      simpa only [switchedMiddle, endpointWord_eq,
        wordOfPrefixFinal_cons, Word.append_assoc] using switchedRaw
    have targetArrangement :
        switchedMiddle.Perm (old :: old :: new :: rest) :=
      List.Perm.refl _
    have endpointPermutation :
        (endpointWord old
          (old :: new :: new :: rest) final).toList.Perm
          (endpointWord new
            (old :: old :: new :: rest) final).toList := by
      have literalPermutation :=
        (permConsToEnd new [old, old]).symm.append_right
          (new :: rest ++ [final])
      simpa only [endpointWord,
        _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints] using
          literalPermutation
    exact ⟨switchedMiddle, arranged.trans switched,
      fullPerm_of_middle_arrangement
        old final new final middle switchedMiddle
        (old :: new :: new :: rest)
        (old :: old :: new :: rest)
        arrangement targetArrangement endpointPermutation⟩

private theorem derivesClosedSwitch
    (old new : Nat) (middle : List Nat)
    (different : old ≠ new)
    (newMultiple :
      2 <= (endpointWord old middle old).toList.count new) :
    ∃ switchedMiddle,
      Derives correctedBasis
        (endpointWord old middle old)
        (endpointWord new switchedMiddle new) ∧
      (endpointWord old middle old).toList.Perm
        (endpointWord new switchedMiddle new).toList := by
  have newAtLeastTwo : 2 <= middle.count new := by
    rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints] at newMultiple
    simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies, different,
      Ne.symm different] at newMultiple
    exact newMultiple
  have newMem : new ∈ middle :=
    List.count_pos_iff.mp (by omega)
  have newMemAfter : new ∈ middle.erase new := by
    apply List.count_pos_iff.mp
    rw [List.count_erase_self]
    omega
  let rest := (middle.erase new).erase new
  have arrangement : middle.Perm (new :: new :: rest) :=
    (List.perm_cons_erase newMem).trans <|
      List.Perm.cons new <| by
        simpa [rest] using List.perm_cons_erase newMemAfter
  cases restEq : rest with
  | nil =>
      let switchedMiddle := [old, old]
      have arranged :=
        derivesPublicMiddlePermutation old old arrangement
      have openFinal :
          Derives correctedBasis
            (endpointWord old [new, new] old)
            (endpointWord old [old, new] new) := by
        simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
          Word.append, Word.singleton, Word.append_assoc] using
            Derives.symm
              (derivesSquareFinalSwitch
                (Word.singleton old) (Word.singleton new))
      have switchInitial :
          Derives correctedBasis
            (endpointWord old [old, new] new)
            (endpointWord new switchedMiddle new) := by
        simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
          switchedMiddle, Word.append, Word.singleton,
          Word.append_assoc] using
            derivesSquareInitialSwitch
              (Word.singleton old) (Word.singleton new)
      have sourceArrangement : middle.Perm [new, new] := by
        simpa [restEq] using arrangement
      have targetArrangement :
          switchedMiddle.Perm [old, old] := List.Perm.refl _
      have endpointPermutation :
          (endpointWord old [new, new] old).toList.Perm
            (endpointWord new [old, old] new).toList := by
        have swapFront :
            [old, new, new, old].Perm [new, old, new, old] :=
          List.Perm.swap new old [new, old]
        have swapBack :
            [new, old, new, old].Perm [new, old, old, new] :=
          List.Perm.cons new <|
            List.Perm.cons old <|
              List.Perm.swap old new []
        simpa only [endpointWord,
          _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints] using
            swapFront.trans swapBack
      have arrangedNil :
          Derives correctedBasis
            (endpointWord old middle old)
            (endpointWord old [new, new] old) := by
        simpa [restEq] using arranged
      exact ⟨switchedMiddle,
        arrangedNil.trans <| openFinal.trans switchInitial,
        fullPerm_of_middle_arrangement
          old old new new middle switchedMiddle
          [new, new] [old, old]
          sourceArrangement targetArrangement endpointPermutation⟩
  | cons next tail =>
      let switchedMiddle := old :: old :: next :: tail
      have arranged :=
        derivesPublicMiddlePermutation old old arrangement
      have openFinal :
          Derives correctedBasis
            (endpointWord old (new :: new :: next :: tail) old)
            (endpointWord old (old :: new :: next :: tail) new) := by
        simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
          wordOfCons, Word.append, Word.singleton,
          Word.append_assoc] using
            Derives.symm
              (derivesAttachmentFinal
                (Word.singleton old) (Word.singleton new)
                (wordOfCons next tail))
      have switchInitial :
          Derives correctedBasis
            (endpointWord old (old :: new :: next :: tail) new)
            (endpointWord new switchedMiddle new) := by
        simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
          switchedMiddle, wordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using
            derivesAttachmentInitial
              (Word.singleton old) (Word.singleton new)
              (wordOfCons next tail)
      have sourceArrangement :
          middle.Perm (new :: new :: next :: tail) := by
        simpa [restEq] using arrangement
      have targetArrangement :
          switchedMiddle.Perm (old :: old :: next :: tail) :=
        List.Perm.refl _
      have endpointPermutation :
          (endpointWord old
            (new :: new :: next :: tail) old).toList.Perm
            (endpointWord new
              (old :: old :: next :: tail) new).toList := by
        have swapFront :
            (old :: new :: new :: next :: tail ++ [old]).Perm
              (new :: old :: new :: next :: tail ++ [old]) :=
          List.Perm.swap new old (new :: next :: tail ++ [old])
        have swapAround :
            (new :: old :: new :: next :: tail ++ [old]).Perm
              (new :: old :: old :: next :: tail ++ [new]) :=
          List.Perm.cons new <|
            List.Perm.cons old <|
              permSwapAround new old (next :: tail)
        simpa only [endpointWord,
          _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints] using
            swapFront.trans swapAround
      have arrangedCons :
          Derives correctedBasis
            (endpointWord old middle old)
            (endpointWord old (new :: new :: next :: tail) old) := by
        simpa [restEq] using arranged
      exact ⟨switchedMiddle, arrangedCons.trans <|
        openFinal.trans switchInitial,
        fullPerm_of_middle_arrangement
          old old new new middle switchedMiddle
          (new :: new :: next :: tail)
          (old :: old :: next :: tail)
          sourceArrangement targetArrangement endpointPermutation⟩

private theorem derivesOpenFinalFromClosed
    (initial newFinal : Nat) (middle : List Nat)
    (different : initial ≠ newFinal)
    (newMultiple :
      2 <= (endpointWord initial middle initial).toList.count newFinal) :
    ∃ switchedMiddle,
      Derives correctedBasis
        (endpointWord initial middle initial)
        (endpointWord initial switchedMiddle newFinal) ∧
      (endpointWord initial middle initial).toList.Perm
        (endpointWord initial switchedMiddle newFinal).toList := by
  have newAtLeastTwo : 2 <= middle.count newFinal := by
    rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints] at newMultiple
    simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies, different,
      Ne.symm different] at newMultiple
    exact newMultiple
  have firstMem : newFinal ∈ middle :=
    List.count_pos_iff.mp (by omega)
  have secondMem : newFinal ∈ middle.erase newFinal := by
    apply List.count_pos_iff.mp
    rw [List.count_erase_self]
    omega
  let rest := (middle.erase newFinal).erase newFinal
  have arrangement : middle.Perm (newFinal :: newFinal :: rest) :=
    (List.perm_cons_erase firstMem).trans <|
      List.Perm.cons newFinal <| by
        simpa [rest] using List.perm_cons_erase secondMem
  cases restEq : rest with
  | nil =>
      let switchedMiddle := [initial, newFinal]
      have arranged :=
        derivesPublicMiddlePermutation initial initial arrangement
      have switched :
          Derives correctedBasis
            (endpointWord initial [newFinal, newFinal] initial)
            (endpointWord initial switchedMiddle newFinal) := by
        simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
          switchedMiddle, Word.append, Word.singleton,
          Word.append_assoc] using
            Derives.symm
              (derivesSquareFinalSwitch
                (Word.singleton initial)
                (Word.singleton newFinal))
      have sourceArrangement :
          middle.Perm [newFinal, newFinal] := by
        simpa [restEq] using arrangement
      have targetArrangement :
          switchedMiddle.Perm [initial, newFinal] :=
        List.Perm.refl _
      have endpointPermutation :
          (endpointWord initial
            [newFinal, newFinal] initial).toList.Perm
            (endpointWord initial
              [initial, newFinal] newFinal).toList := by
        have literalPermutation :=
          List.Perm.cons initial <|
            (permConsToEnd initial [newFinal, newFinal]).symm
        simpa only [endpointWord,
          _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints] using
            literalPermutation
      have arrangedNil :
          Derives correctedBasis
            (endpointWord initial middle initial)
            (endpointWord initial [newFinal, newFinal] initial) := by
        simpa [restEq] using arranged
      exact ⟨switchedMiddle,
        arrangedNil.trans switched,
        fullPerm_of_middle_arrangement
          initial initial initial newFinal middle switchedMiddle
          [newFinal, newFinal] [initial, newFinal]
          sourceArrangement targetArrangement endpointPermutation⟩
  | cons next tail =>
      let switchedMiddle := initial :: newFinal :: next :: tail
      have arranged :=
        derivesPublicMiddlePermutation initial initial arrangement
      have switched :
          Derives correctedBasis
            (endpointWord initial
              (newFinal :: newFinal :: next :: tail) initial)
            (endpointWord initial switchedMiddle newFinal) := by
        simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
          switchedMiddle, wordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using
            Derives.symm
              (derivesAttachmentFinal
                (Word.singleton initial)
                (Word.singleton newFinal)
                (wordOfCons next tail))
      have sourceArrangement :
          middle.Perm (newFinal :: newFinal :: next :: tail) := by
        simpa [restEq] using arrangement
      have targetArrangement :
          switchedMiddle.Perm
            (initial :: newFinal :: next :: tail) :=
        List.Perm.refl _
      have endpointPermutation :
          (endpointWord initial
            (newFinal :: newFinal :: next :: tail) initial).toList.Perm
            (endpointWord initial
              (initial :: newFinal :: next :: tail) newFinal).toList := by
        have literalPermutation :=
          List.Perm.cons initial <|
            permSwapAround newFinal initial
              (newFinal :: next :: tail)
        simpa only [endpointWord,
          _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints] using
            literalPermutation
      have arrangedCons :
          Derives correctedBasis
            (endpointWord initial middle initial)
            (endpointWord initial
              (newFinal :: newFinal :: next :: tail) initial) := by
        simpa [restEq] using arranged
      exact ⟨switchedMiddle, arrangedCons.trans switched,
        fullPerm_of_middle_arrangement
          initial initial initial newFinal middle switchedMiddle
          (newFinal :: newFinal :: next :: tail)
          (initial :: newFinal :: next :: tail)
          sourceArrangement targetArrangement endpointPermutation⟩

private theorem derivesFinalSwitchPreservingInitial
    (initial oldFinal newFinal : Nat) (middle : List Nat)
    (finalsNe : oldFinal ≠ newFinal)
    (initialOldNe : initial ≠ oldFinal)
    (oldRepeated : oldFinal ∈ initial :: middle)
    (newMultiple :
      2 <= (endpointWord initial middle oldFinal).toList.count newFinal) :
    ∃ switchedMiddle,
      Derives correctedBasis
        (endpointWord initial middle oldFinal)
        (endpointWord initial switchedMiddle newFinal) ∧
      (endpointWord initial middle oldFinal).toList.Perm
        (endpointWord initial switchedMiddle newFinal).toList := by
  have oldMem : oldFinal ∈ middle := by
    rcases List.mem_cons.mp oldRepeated with atInitial | member
    · exact False.elim (initialOldNe atInitial.symm)
    · exact member
  by_cases initialNew : initial = newFinal
  · subst newFinal
    have newPositive : 0 < middle.count initial := by
      rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints] at newMultiple
      simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies, initialOldNe,
        Ne.symm initialOldNe] at newMultiple
      omega
    have newMem : initial ∈ middle :=
      List.count_pos_iff.mp newPositive
    have oldMemAfterNew : oldFinal ∈ middle.erase initial := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_of_ne (Ne.symm initialOldNe)]
      exact List.count_pos_iff.mpr oldMem
    let rest := (middle.erase initial).erase oldFinal
    have arrangement :
        middle.Perm (initial :: rest ++ [oldFinal]) := by
      have front : middle.Perm (initial :: oldFinal :: rest) :=
        (List.perm_cons_erase newMem).trans <|
          List.Perm.cons initial <| by
            simpa [rest] using List.perm_cons_erase oldMemAfterNew
      exact front.trans <|
        List.Perm.cons initial (permConsToEnd oldFinal rest)
    cases restEq : rest with
    | nil =>
        let switchedMiddle := [oldFinal, oldFinal]
        have arranged :=
          derivesPublicMiddlePermutation initial oldFinal arrangement
        have switched :
            Derives correctedBasis
              (endpointWord initial [initial, oldFinal] oldFinal)
              (endpointWord initial switchedMiddle initial) := by
          simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
            switchedMiddle, Word.append, Word.singleton,
            Word.append_assoc] using
              derivesSquareFinalSwitch
                (Word.singleton initial) (Word.singleton oldFinal)
        have sourceArrangement :
            middle.Perm [initial, oldFinal] := by
          simpa [restEq] using arrangement
        have targetArrangement :
            switchedMiddle.Perm [oldFinal, oldFinal] :=
          List.Perm.refl _
        have endpointPermutation :
            (endpointWord initial
              [initial, oldFinal] oldFinal).toList.Perm
              (endpointWord initial
                [oldFinal, oldFinal] initial).toList := by
          have literalPermutation :=
            List.Perm.cons initial <|
              permConsToEnd initial [oldFinal, oldFinal]
          simpa only [endpointWord,
            _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints] using
              literalPermutation
        have arrangedNil :
            Derives correctedBasis
              (endpointWord initial middle oldFinal)
              (endpointWord initial [initial, oldFinal] oldFinal) := by
          simpa [restEq] using arranged
        exact ⟨switchedMiddle,
          arrangedNil.trans switched,
          fullPerm_of_middle_arrangement
            initial oldFinal initial initial middle switchedMiddle
            [initial, oldFinal] [oldFinal, oldFinal]
            sourceArrangement targetArrangement endpointPermutation⟩
    | cons next tail =>
        let switchedMiddle := oldFinal :: oldFinal :: next :: tail
        have arranged :=
          derivesPublicMiddlePermutation initial oldFinal arrangement
        have attachmentPermutation :
            (initial :: next :: tail ++ [oldFinal]).Perm
              (initial :: oldFinal :: next :: tail) :=
          List.Perm.cons initial <|
            (permConsToEnd oldFinal (next :: tail)).symm
        have attachmentArranged :=
          derivesPublicMiddlePermutation
            initial oldFinal attachmentPermutation
        have attachmentSwitch :
            Derives correctedBasis
              (endpointWord initial
                (initial :: oldFinal :: next :: tail) oldFinal)
              (endpointWord initial switchedMiddle initial) := by
          simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
            switchedMiddle, wordOfCons, Word.append,
            Word.singleton, Word.append_assoc,
            List.append_assoc] using
              derivesAttachmentFinal
                (Word.singleton initial) (Word.singleton oldFinal)
                (wordOfCons next tail)
        have switched :
            Derives correctedBasis
              (endpointWord initial
                (initial :: next :: tail ++ [oldFinal]) oldFinal)
              (endpointWord initial switchedMiddle initial) :=
          attachmentArranged.trans attachmentSwitch
        have sourceArrangement :
            middle.Perm
              (initial :: next :: tail ++ [oldFinal]) := by
          simpa [restEq] using arrangement
        have targetArrangement :
            switchedMiddle.Perm
              (oldFinal :: oldFinal :: next :: tail) :=
          List.Perm.refl _
        have endpointPermutation :
            (endpointWord initial
              (initial :: next :: tail ++ [oldFinal])
              oldFinal).toList.Perm
              (endpointWord initial
                (oldFinal :: oldFinal :: next :: tail)
                initial).toList := by
          have suffixPermutation :
              (initial :: next :: tail ++ [oldFinal, oldFinal]).Perm
                (oldFinal :: oldFinal :: next :: tail ++ [initial]) := by
            have moveInitial :=
              permConsToEnd initial
                ((next :: tail) ++ [oldFinal, oldFinal])
            have moveOldFinals :=
              (permTwoToEnd oldFinal (next :: tail)).symm.append_right
                [initial]
            exact moveInitial.trans <| by
              simpa [List.append_assoc] using moveOldFinals
          have literalPermutation :=
            List.Perm.cons initial suffixPermutation
          simpa only [endpointWord,
            _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints,
            List.cons_append, List.append_assoc] using literalPermutation
        have arrangedCons :
            Derives correctedBasis
              (endpointWord initial middle oldFinal)
              (endpointWord initial
                (initial :: next :: tail ++ [oldFinal]) oldFinal) := by
          simpa [restEq] using arranged
        exact ⟨switchedMiddle, arrangedCons.trans switched,
          fullPerm_of_middle_arrangement
            initial oldFinal initial initial middle switchedMiddle
            (initial :: next :: tail ++ [oldFinal])
            (oldFinal :: oldFinal :: next :: tail)
            sourceArrangement targetArrangement endpointPermutation⟩
  · have initialNewNe : initial ≠ newFinal := initialNew
    have newAtLeastTwo : 2 <= middle.count newFinal := by
      rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints] at newMultiple
      simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies, finalsNe, initialNewNe,
        Ne.symm finalsNe, Ne.symm initialNewNe] at newMultiple
      exact newMultiple
    have firstNew : newFinal ∈ middle :=
      List.count_pos_iff.mp (by omega)
    have secondNew : newFinal ∈ middle.erase newFinal := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_self]
      omega
    have oldAfterTwoNew :
        oldFinal ∈ (middle.erase newFinal).erase newFinal := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_of_ne finalsNe,
        List.count_erase_of_ne finalsNe]
      exact List.count_pos_iff.mpr oldMem
    let rest :=
      ((middle.erase newFinal).erase newFinal).erase oldFinal
    have frontArrangement :
        middle.Perm (newFinal :: newFinal :: oldFinal :: rest) :=
      (List.perm_cons_erase firstNew).trans <|
        List.Perm.cons newFinal <|
          (List.perm_cons_erase secondNew).trans <|
            List.Perm.cons newFinal <| by
              simpa [rest] using List.perm_cons_erase oldAfterTwoNew
    have arrangement :
        middle.Perm (rest ++ [newFinal, newFinal, oldFinal]) := by
      have rotatePrefix :
          (newFinal :: newFinal :: oldFinal :: rest).Perm
            (rest ++ [newFinal, newFinal, oldFinal]) := by
        exact
          (List.perm_append_comm :
            ([newFinal, newFinal, oldFinal] ++ rest).Perm
              (rest ++ [newFinal, newFinal, oldFinal]))
      exact frontArrangement.trans rotatePrefix
    let switchedMiddle :=
      rest ++ [newFinal, oldFinal, oldFinal]
    have arranged :=
      derivesPublicMiddlePermutation initial oldFinal arrangement
    have switchedRaw :=
      Derives.prepend (wordOfCons initial rest)
        (derivesSquareFinalSwitch
          (Word.singleton newFinal) (Word.singleton oldFinal))
    have switched :
        Derives correctedBasis
          (endpointWord initial
            (rest ++ [newFinal, newFinal, oldFinal]) oldFinal)
          (endpointWord initial switchedMiddle newFinal) := by
      simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
        switchedMiddle, wordOfCons, Word.append,
        Word.singleton, Word.append_assoc,
        List.append_assoc] using switchedRaw
    have targetArrangement :
        switchedMiddle.Perm
          (rest ++ [newFinal, oldFinal, oldFinal]) :=
      List.Perm.refl _
    have endpointPermutation :
        (endpointWord initial
          (rest ++ [newFinal, newFinal, oldFinal])
          oldFinal).toList.Perm
          (endpointWord initial
            (rest ++ [newFinal, oldFinal, oldFinal])
            newFinal).toList := by
      have suffixPermutation :
          [newFinal, newFinal, oldFinal, oldFinal].Perm
            [newFinal, oldFinal, oldFinal, newFinal] :=
        List.Perm.cons newFinal <|
          permConsToEnd newFinal [oldFinal, oldFinal]
      have literalPermutation :=
        List.Perm.cons initial <|
          List.Perm.append_left rest suffixPermutation
      simpa only [endpointWord,
        _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints,
        List.cons_append, List.append_assoc] using literalPermutation
    exact ⟨switchedMiddle, arranged.trans switched,
      fullPerm_of_middle_arrangement
        initial oldFinal initial newFinal middle switchedMiddle
        (rest ++ [newFinal, newFinal, oldFinal])
        (rest ++ [newFinal, oldFinal, oldFinal])
        arrangement targetArrangement endpointPermutation⟩

/-! ## Endpoint semantics and terminal completeness -/

private def initialSeparator (tested : Nat) : Nat -> Fin 4 :=
  fun value => if value = tested then 2 else 3

private def finalSeparator (tested : Nat) : Nat -> Fin 4 :=
  fun value => if value = tested then 1 else 3

private theorem simpleInitial_iff_of_valid
    (leftInitial : Nat) (leftMiddle : List Nat) (leftFinal : Nat)
    (rightInitial : Nat) (rightMiddle : List Nat) (rightFinal : Nat)
    (valid :
      (Identity.mk
        (endpointWord leftInitial leftMiddle leftFinal)
        (endpointWord rightInitial rightMiddle rightFinal)).SatisfiedBy
          simpleEndpointsFour.semigroup) :
    forall tested,
      (leftInitial = tested ∧ tested ∉ leftMiddle ∧
          leftFinal ≠ tested) ↔
        (rightInitial = tested ∧ tested ∉ rightMiddle ∧
          rightFinal ≠ tested) := by
  intro tested
  have evaluated := valid (initialSeparator tested)
  constructor
  · intro leftSimple
    have leftTwo :
        simpleEndpointsFour.semigroup.eval
            (initialSeparator tested)
            (endpointWord leftInitial leftMiddle leftFinal) = (2 : Fin 4) := by
      simpa [initialSeparator] using
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          tested leftInitial leftMiddle leftFinal).2 leftSimple
    have rightTwo := evaluated.symm.trans leftTwo
    exact
      (simpleEndpointsEval_initialSeparator_eq_two_iff
        tested rightInitial rightMiddle rightFinal).1 <| by
          simpa [initialSeparator] using rightTwo
  · intro rightSimple
    have rightTwo :
        simpleEndpointsFour.semigroup.eval
            (initialSeparator tested)
            (endpointWord rightInitial rightMiddle rightFinal) = (2 : Fin 4) := by
      simpa [initialSeparator] using
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          tested rightInitial rightMiddle rightFinal).2 rightSimple
    have leftTwo := evaluated.trans rightTwo
    exact
      (simpleEndpointsEval_initialSeparator_eq_two_iff
        tested leftInitial leftMiddle leftFinal).1 <| by
          simpa [initialSeparator] using leftTwo

private theorem simpleFinal_iff_of_valid
    (leftInitial : Nat) (leftMiddle : List Nat) (leftFinal : Nat)
    (rightInitial : Nat) (rightMiddle : List Nat) (rightFinal : Nat)
    (valid :
      (Identity.mk
        (endpointWord leftInitial leftMiddle leftFinal)
        (endpointWord rightInitial rightMiddle rightFinal)).SatisfiedBy
          simpleEndpointsFour.semigroup) :
    forall tested,
      (leftFinal = tested ∧ tested ∉ leftInitial :: leftMiddle) ↔
        (rightFinal = tested ∧ tested ∉ rightInitial :: rightMiddle) := by
  intro tested
  have evaluated := valid (finalSeparator tested)
  constructor
  · intro leftSimple
    have leftOne :
        simpleEndpointsFour.semigroup.eval
            (finalSeparator tested)
            (endpointWord leftInitial leftMiddle leftFinal) = (1 : Fin 4) := by
      simpa [finalSeparator] using
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          tested leftInitial leftMiddle leftFinal).2 leftSimple
    have rightOne := evaluated.symm.trans leftOne
    exact
      (simpleEndpointsEval_finalSeparator_eq_one_iff
        tested rightInitial rightMiddle rightFinal).1 <| by
          simpa [finalSeparator] using rightOne
  · intro rightSimple
    have rightOne :
        simpleEndpointsFour.semigroup.eval
            (finalSeparator tested)
            (endpointWord rightInitial rightMiddle rightFinal) = (1 : Fin 4) := by
      simpa [finalSeparator] using
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          tested rightInitial rightMiddle rightFinal).2 rightSimple
    have leftOne := evaluated.trans rightOne
    exact
      (simpleEndpointsEval_finalSeparator_eq_one_iff
        tested leftInitial leftMiddle leftFinal).1 <| by
          simpa [finalSeparator] using leftOne

private theorem middlePerm_of_wholeCounts
    (initial final : Nat) (left right : List Nat)
    (counts : forall tested,
      (endpointWord initial left final).toList.count tested =
        (endpointWord initial right final).toList.count tested) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro tested
  have countEq := counts tested
  rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints,
    _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints] at countEq
  omega

private theorem derivesSameEndpointsOfCounts
    (initial final : Nat) (left right : List Nat)
    (counts : forall tested,
      (endpointWord initial left final).toList.count tested =
        (endpointWord initial right final).toList.count tested) :
    Derives correctedBasis
      (endpointWord initial left final)
      (endpointWord initial right final) :=
  derivesPublicMiddlePermutation initial final <|
    middlePerm_of_wholeCounts initial final left right counts

private theorem counts_after_permutation
    {source target reference : Word Nat}
    (permutation : source.toList.Perm target.toList)
    (counts : forall tested,
      source.toList.count tested = reference.toList.count tested) :
    forall tested,
      target.toList.count tested = reference.toList.count tested := by
  intro tested
  have switched :=
    (List.perm_iff_count.mp permutation) tested
  exact switched.symm.trans (counts tested)

private theorem derivesSameInitial
    (initial : Nat)
    (leftMiddle : List Nat) (leftFinal : Nat)
    (rightMiddle : List Nat) (rightFinal : Nat)
    (simpleValid :
      (Identity.mk
        (endpointWord initial leftMiddle leftFinal)
        (endpointWord initial rightMiddle rightFinal)).SatisfiedBy
          simpleEndpointsFour.semigroup)
    (counts : forall tested,
      (endpointWord initial leftMiddle leftFinal).toList.count tested =
        (endpointWord initial rightMiddle rightFinal).toList.count tested) :
    Derives correctedBasis
      (endpointWord initial leftMiddle leftFinal)
      (endpointWord initial rightMiddle rightFinal) := by
  by_cases finals : leftFinal = rightFinal
  · subst rightFinal
    exact derivesSameEndpointsOfCounts
      initial leftFinal leftMiddle rightMiddle counts
  · have finalSimple :=
      simpleFinal_iff_of_valid
        initial leftMiddle leftFinal
        initial rightMiddle rightFinal simpleValid
    have leftRepeated : leftFinal ∈ initial :: leftMiddle := by
      apply Decidable.byContradiction
      intro absent
      have rightSimple :=
        (finalSimple leftFinal).mp ⟨rfl, absent⟩
      exact finals rightSimple.1.symm
    have rightRepeated : rightFinal ∈ initial :: rightMiddle := by
      apply Decidable.byContradiction
      intro absent
      have leftSimple :=
        (finalSimple rightFinal).mpr ⟨rfl, absent⟩
      exact finals leftSimple.1
    have rightMultiple :=
      repeatedFinal_count_two
        initial rightMiddle rightFinal rightRepeated
    have leftNewMultiple :
        2 <=
          (endpointWord initial leftMiddle leftFinal).toList.count
            rightFinal := by
      rw [counts rightFinal]
      exact rightMultiple
    by_cases closed : initial = leftFinal
    · subst leftFinal
      obtain ⟨switchedMiddle, switch, permutation⟩ :=
        derivesOpenFinalFromClosed
          initial rightFinal leftMiddle
          finals
          leftNewMultiple
      have switchedCounts :=
        counts_after_permutation permutation counts
      exact switch.trans <|
        derivesSameEndpointsOfCounts
          initial rightFinal switchedMiddle rightMiddle switchedCounts
    · obtain ⟨switchedMiddle, switch, permutation⟩ :=
        derivesFinalSwitchPreservingInitial
          initial leftFinal rightFinal leftMiddle
          finals closed leftRepeated leftNewMultiple
      have switchedCounts :=
        counts_after_permutation permutation counts
      exact switch.trans <|
        derivesSameEndpointsOfCounts
          initial rightFinal switchedMiddle rightMiddle switchedCounts

private theorem derivesNormalizedOfSimpleAndCounts
    (leftInitial : Nat) (leftMiddle : List Nat) (leftFinal : Nat)
    (rightInitial : Nat) (rightMiddle : List Nat) (rightFinal : Nat)
    (simpleValid :
      (Identity.mk
        (endpointWord leftInitial leftMiddle leftFinal)
        (endpointWord rightInitial rightMiddle rightFinal)).SatisfiedBy
          simpleEndpointsFour.semigroup)
    (counts : forall tested,
      (endpointWord leftInitial leftMiddle leftFinal).toList.count tested =
        (endpointWord rightInitial rightMiddle rightFinal).toList.count tested) :
    Derives correctedBasis
      (endpointWord leftInitial leftMiddle leftFinal)
      (endpointWord rightInitial rightMiddle rightFinal) := by
  by_cases initials : leftInitial = rightInitial
  · subst rightInitial
    exact derivesSameInitial
      leftInitial leftMiddle leftFinal rightMiddle rightFinal
      simpleValid counts
  · have initialSimple :=
      simpleInitial_iff_of_valid
        leftInitial leftMiddle leftFinal
        rightInitial rightMiddle rightFinal simpleValid
    have leftRepeated :
        leftInitial ∈ leftMiddle ∨ leftFinal = leftInitial := by
      apply Decidable.byContradiction
      intro absent
      have middleAbsent : leftInitial ∉ leftMiddle :=
        fun member => absent (Or.inl member)
      have finalNe : leftFinal ≠ leftInitial :=
        fun equal => absent (Or.inr equal)
      have rightSimple :=
        (initialSimple leftInitial).mp
          ⟨rfl, middleAbsent, finalNe⟩
      exact initials rightSimple.1.symm
    have rightRepeated :
        rightInitial ∈ rightMiddle ∨ rightFinal = rightInitial := by
      apply Decidable.byContradiction
      intro absent
      have middleAbsent : rightInitial ∉ rightMiddle :=
        fun member => absent (Or.inl member)
      have finalNe : rightFinal ≠ rightInitial :=
        fun equal => absent (Or.inr equal)
      have leftSimple :=
        (initialSimple rightInitial).mpr
          ⟨rfl, middleAbsent, finalNe⟩
      exact initials leftSimple.1
    have rightMultiple :=
      repeatedInitial_count_two
        rightInitial rightMiddle rightFinal rightRepeated
    have leftNewMultiple :
        2 <=
          (endpointWord leftInitial leftMiddle leftFinal).toList.count
            rightInitial := by
      rw [counts rightInitial]
      exact rightMultiple
    by_cases closed : leftFinal = leftInitial
    · subst leftFinal
      obtain ⟨switchedMiddle, switch, permutation⟩ :=
        derivesClosedSwitch
          leftInitial rightInitial leftMiddle initials leftNewMultiple
      have switchedCounts :=
        counts_after_permutation permutation counts
      have residualSimple :
          (Identity.mk
            (endpointWord rightInitial switchedMiddle rightInitial)
            (endpointWord rightInitial rightMiddle rightFinal)).SatisfiedBy
              simpleEndpointsFour.semigroup := by
        intro valuation
        exact
          (switch.sound correctedModels_simpleEndpoints valuation).symm.trans
            (simpleValid valuation)
      exact switch.trans <|
        derivesSameInitial
          rightInitial switchedMiddle rightInitial
          rightMiddle rightFinal residualSimple switchedCounts
    · obtain ⟨switchedMiddle, switch, permutation⟩ :=
        derivesInitialSwitchPreservingFinal
          leftInitial rightInitial leftMiddle leftFinal
          initials closed leftRepeated leftNewMultiple
      have switchedCounts :=
        counts_after_permutation permutation counts
      have residualSimple :
          (Identity.mk
            (endpointWord rightInitial switchedMiddle leftFinal)
            (endpointWord rightInitial rightMiddle rightFinal)).SatisfiedBy
              simpleEndpointsFour.semigroup := by
        intro valuation
        exact
          (switch.sound correctedModels_simpleEndpoints valuation).symm.trans
            (simpleValid valuation)
      exact switch.trans <|
        derivesSameInitial
          rightInitial switchedMiddle leftFinal
          rightMiddle rightFinal residualSimple switchedCounts

private def splitMiddleFinal (current : Nat) :
    List Nat -> List Nat × Nat
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

private theorem endpointWord_splitMiddleFinal
    (initial current : Nat) (rest : List Nat) :
    endpointWord initial (splitMiddleFinal current rest).1
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

/-- The cap-three and endpoint invariants form a complete arbitrary-support
normal form for the repaired thirteen-law system. -/
theorem endpointCapThreeCompleteness :
    EndpointCapThreeCompleteness := by
  intro identity simpleValid cappedCounts
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  cases leftTail with
  | nil =>
      cases rightTail with
      | nil =>
          have heads : leftHead = rightHead := by
            apply Decidable.byContradiction
            intro different
            have capped := cappedCounts leftHead
            simp [Word.toList, different, Ne.symm different] at capped
          subst rightHead
          exact Derives.refl _
      | cons rightSecond rightRest =>
          have evaluated := simpleValid (fun _ => (1 : Fin 4))
          have leftOne :=
            (simpleEndpointsSingletonSeparator
              (Word.mk leftHead [])).2 rfl
          have rightOne := evaluated.symm.trans leftOne
          have impossible :=
            (simpleEndpointsSingletonSeparator
              (Word.mk rightHead
                (rightSecond :: rightRest))).1 rightOne
          simp at impossible
  | cons leftSecond leftRest =>
      cases rightTail with
      | nil =>
          have evaluated := simpleValid (fun _ => (1 : Fin 4))
          have rightOne :=
            (simpleEndpointsSingletonSeparator
              (Word.mk rightHead [])).2 rfl
          have leftOne := evaluated.trans rightOne
          have impossible :=
            (simpleEndpointsSingletonSeparator
              (Word.mk leftHead
                (leftSecond :: leftRest))).1 leftOne
          simp at impossible
      | cons rightSecond rightRest =>
          let leftSplit := splitMiddleFinal leftSecond leftRest
          let rightSplit := splitMiddleFinal rightSecond rightRest
          have leftReconstruct :
              endpointWord leftHead leftSplit.1 leftSplit.2 =
                Word.mk leftHead (leftSecond :: leftRest) :=
            endpointWord_splitMiddleFinal
              leftHead leftSecond leftRest
          have rightReconstruct :
              endpointWord rightHead rightSplit.1 rightSplit.2 =
                Word.mk rightHead (rightSecond :: rightRest) :=
            endpointWord_splitMiddleFinal
              rightHead rightSecond rightRest
          have leftNormal :=
            derivesNormalizeCapThree
              leftHead leftSplit.1 leftSplit.2
          have rightNormal :=
            derivesNormalizeCapThree
              rightHead rightSplit.1 rightSplit.2
          have normalCounts :=
            endpointCapThreeReduce_normal_counts_eq
              (leftInitial := leftHead)
              (leftFinal := leftSplit.2)
              (rightInitial := rightHead)
              (rightFinal := rightSplit.2)
              (leftMiddle := leftSplit.1)
              (rightMiddle := rightSplit.1)
              (by
                intro tested
                rw [leftReconstruct, rightReconstruct]
                exact cappedCounts tested)
          have endpointSimple :
              (Identity.mk
                (endpointWord leftHead leftSplit.1 leftSplit.2)
                (endpointWord rightHead rightSplit.1
                  rightSplit.2)).SatisfiedBy
                    simpleEndpointsFour.semigroup := by
            rw [leftReconstruct, rightReconstruct]
            exact simpleValid
          have normalizedSimple :
              (Identity.mk
                (endpointWord leftHead
                  (endpointCapThreeReduce
                    leftHead leftSplit.2 leftSplit.1)
                  leftSplit.2)
                (endpointWord rightHead
                  (endpointCapThreeReduce
                    rightHead rightSplit.2 rightSplit.1)
                  rightSplit.2)).SatisfiedBy
                    simpleEndpointsFour.semigroup := by
            intro valuation
            exact
              (leftNormal.sound
                correctedModels_simpleEndpoints valuation).symm.trans <|
                (endpointSimple valuation).trans <|
                  rightNormal.sound
                    correctedModels_simpleEndpoints valuation
          have bridge :=
            derivesNormalizedOfSimpleAndCounts
              leftHead
              (endpointCapThreeReduce
                leftHead leftSplit.2 leftSplit.1)
              leftSplit.2
              rightHead
              (endpointCapThreeReduce
                rightHead rightSplit.2 rightSplit.1)
              rightSplit.2 normalizedSimple normalCounts
          rw [← leftReconstruct, ← rightReconstruct]
          exact leftNormal.trans <| bridge.trans rightNormal.symm

/-- Unconditional arbitrary-support reduction for the repaired basis. -/
theorem correctedReducedCompleteness :
    ReducedCompleteness :=
  reducedCompleteness_of_endpointCapThree endpointCapThreeCompleteness

/-- Every identity valid in both recorded factors follows from the repaired
thirteen-law basis. -/
theorem correctedJointCompleteness
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_6.table.semigroup.opposite)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S5_209.table.semigroup) :
    Derives correctedBasis identity.lhs identity.rhs :=
  correctedJointCompleteness_of_reduced
    correctedReducedCompleteness identity s3Valid s5Valid

/-- Terminal intersection-basis endpoint for the repaired candidate. -/
def correctedIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      SemigroupBasis.Generated.S5_209.table.semigroup
      correctedBasis :=
  correctedIntersectionBasis_of_reduced correctedReducedCompleteness

end SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Normal

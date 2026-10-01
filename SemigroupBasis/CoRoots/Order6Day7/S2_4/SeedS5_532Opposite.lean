import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank102
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.Generated.S5_529Transfers

/-!
# An unrestricted `S2_4 × S5_532ᵒᵖ` family seed

The independently complete `S5_529 → S5_532` power-embedding transfer
certifies that the actual opposite right factor fixes the final letter and
every multiplicity capped at three. The actual left-zero factor fixes the
initial letter. Exactly three authenticated displayed laws suffice: the
four-to-three power contraction, the closed-endpoint contraction, and the
square-free open-interior transposition.

The normalizer protects both endpoints, reduces whole-word multiplicities to
their cap-three signatures, and then permutes the remaining interior. No
finite check or conditional shell is treated as unrestricted completeness.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank102.Seed

open SemigroupBasis
open SemigroupBasis.Examples

universe u v

private def instantiateFour
    (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | marker + 4 => Word.singleton (marker + 4)

private def endpointWord
    (initial : Nat) (middle : List Nat) (final : Nat) : Word Nat :=
  ⟨initial, middle ++ [final]⟩

@[simp]
private theorem toList_endpointWord
    (initial : Nat) (middle : List Nat) (final : Nat) :
    (endpointWord initial middle final).toList =
      initial :: middle ++ [final] := rfl

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

private theorem endpointWord_eq
    (initial : Nat) (middle : List Nat) (final : Nat) :
    endpointWord initial middle final =
      Word.singleton initial ++ wordOfPrefixFinal middle final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal, toList_endpointWord]
  rfl

private def endpointCopies (initial final tested : Nat) : Nat :=
  [initial, final].count tested

private theorem endpointCopies_le_two
    (initial final tested : Nat) :
    endpointCopies initial final tested ≤ 2 := by
  simpa [endpointCopies] using
    (List.count_le_length (a := tested) (l := [initial, final]))

private theorem count_endpointWord
    (initial : Nat) (middle : List Nat) (final tested : Nat) :
    (endpointWord initial middle final).toList.count tested =
      endpointCopies initial final tested + middle.count tested := by
  simp only [toList_endpointWord, endpointCopies, List.count_cons,
    List.count_append, List.count_nil]
  omega

/-- The frozen `xxx = xxxx` contracts any fourth nonempty block. -/
theorem derivesFourToThree (block : Word Nat) :
    Derives basis
      (((block ++ block) ++ block) ++ block)
      ((block ++ block) ++ block) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 0]) (Word.mk 0 [0, 0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive.symm
      (instantiateFour block block block block)
  simpa [law00, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The frozen `xxxyx = xxyx` contracts a repeated closed endpoint. -/
theorem derivesTripleClosedContraction
    (endpoint middle : Word Nat) :
    Derives basis
      ((((endpoint ++ endpoint) ++ endpoint) ++ middle) ++ endpoint)
      (((endpoint ++ endpoint) ++ middle) ++ endpoint) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 0, 1, 0]) (Word.mk 0 [0, 1, 0]) :=
    Derives.fromBasis (e := law01) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateFour endpoint middle middle middle)
  simpa [law01, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The frozen square-free law swaps arbitrary protected interior blocks. -/
theorem derivesOpenInteriorSwap
    (initial first second final : Word Nat) :
    Derives basis
      (((initial ++ first) ++ second) ++ final)
      (((initial ++ second) ++ first) ++ final) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2, 3]) (Word.mk 0 [2, 1, 3]) :=
    Derives.fromBasis (e := law07) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateFour initial first second final)
  simpa [law07, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Adjacent open swaps replay every arbitrary-support interior permutation. -/
theorem derivesMiddlePermutation
    (initial final : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives basis
      (endpointWord initial left final)
      (endpointWord initial right final) := by
  induction permutation generalizing initial with
  | nil =>
      exact Derives.refl _
  | cons letter _ induction =>
      simpa [endpointWord_eq, Word.append_assoc] using
        Derives.prepend (Word.singleton initial) (induction letter)
  | swap first second rest =>
      simpa [endpointWord_eq, Word.append_assoc] using
        derivesOpenInteriorSwap
          (Word.singleton initial)
          (Word.singleton second)
          (Word.singleton first)
          (wordOfPrefixFinal rest final)
  | trans _ _ first second =>
      exact (first initial).trans (second initial)

/-- Reduce middle occurrences while counting the two protected endpoints. -/
def endpointCapThreeReduce
    (initial final : Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      let reduced := endpointCapThreeReduce initial final rest
      if endpointCopies initial final letter + reduced.count letter < 3 then
        letter :: reduced
      else
        reduced

theorem endpointCapThreeReduce_total_le_three
    (initial final tested : Nat) (middle : List Nat) :
    endpointCopies initial final tested +
        (endpointCapThreeReduce initial final middle).count tested ≤ 3 := by
  induction middle with
  | nil =>
      simp only [endpointCapThreeReduce, List.count_nil, Nat.add_zero]
      have bound := endpointCopies_le_two initial final tested
      omega
  | cons letter rest induction =>
      simp only [endpointCapThreeReduce]
      split <;> rename_i small
      · by_cases same : tested = letter
        · subst tested
          rw [List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm same)]
          exact induction
      · exact induction

theorem endpointCapThreeReduce_total_capped
    (initial final tested : Nat) (middle : List Nat) :
    min
        (endpointCopies initial final tested +
          (endpointCapThreeReduce initial final middle).count tested) 3 =
      min
        (endpointCopies initial final tested + middle.count tested) 3 := by
  induction middle with
  | nil =>
      simp [endpointCapThreeReduce]
  | cons letter rest induction =>
      simp only [endpointCapThreeReduce]
      split <;> rename_i small
      · by_cases same : tested = letter
        · subst tested
          rw [List.count_cons_self, List.count_cons_self]
          have bound :=
            endpointCapThreeReduce_total_le_three
              initial final letter rest
          omega
        · rw [List.count_cons_of_ne (Ne.symm same),
            List.count_cons_of_ne (Ne.symm same)]
          exact induction
      · by_cases same : tested = letter
        · subst tested
          rw [List.count_cons_self]
          have bound :=
            endpointCapThreeReduce_total_le_three
              initial final letter rest
          omega
        · rw [List.count_cons_of_ne (Ne.symm same)]
          exact induction

theorem endpointCapThreeReduce_whole_count
    (initial : Nat) (middle : List Nat) (final tested : Nat) :
    (endpointWord initial
      (endpointCapThreeReduce initial final middle) final).toList.count tested =
      min ((endpointWord initial middle final).toList.count tested) 3 := by
  rw [count_endpointWord, count_endpointWord]
  have capped :=
    endpointCapThreeReduce_total_capped initial final tested middle
  have bound :=
    endpointCapThreeReduce_total_le_three initial final tested middle
  omega

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private theorem derivesDeleteFourInterior
    (initial final selected : Nat) (front reduced : List Nat)
    (countEq : reduced.count selected = 3) :
    Derives basis
      (endpointWord initial (front ++ selected :: reduced) final)
      (endpointWord initial (front ++ reduced) final) := by
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
      (front ++ selected :: reduced).Perm
        (selected :: selected :: selected :: selected ::
          front ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = selected
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have targetPerm :
      (front ++ reduced).Perm
        (selected :: selected :: selected :: front ++ remainder) := by
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
      (wordOfPrefixFinal (front ++ remainder) final)
  have contracted :
      Derives basis
        (endpointWord initial
          (selected :: selected :: selected :: selected ::
            front ++ remainder) final)
        (endpointWord initial
          (selected :: selected :: selected :: front ++ remainder) final) := by
    simpa only [List.cons_append, endpointWord_eq,
      wordOfPrefixFinal_cons, Word.append_assoc] using contraction
  exact (derivesMiddlePermutation initial final sourcePerm).trans <|
    contracted.trans <|
      derivesMiddlePermutation initial final targetPerm.symm

private theorem derivesDeleteInitialExcess
    (initial final : Nat) (front reduced : List Nat)
    (countEq : reduced.count initial = 2) :
    Derives basis
      (endpointWord initial (front ++ initial :: reduced) final)
      (endpointWord initial (front ++ reduced) final) := by
  let remainder := (reduced.erase initial).erase initial
  have firstCount : (reduced.erase initial).count initial = 1 := by
    rw [List.count_erase_self, countEq]
  have remainderCount : remainder.count initial = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, firstCount]
  have sourcePerm :
      (front ++ initial :: reduced).Perm
        (initial :: initial :: initial :: front ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = initial
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have targetPerm :
      (front ++ reduced).Perm
        (initial :: initial :: front ++ remainder) := by
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
      (wordOfPrefixFinal (front ++ remainder) final)
  have contracted :
      Derives basis
        (endpointWord initial
          (initial :: initial :: initial :: front ++ remainder) final)
        (endpointWord initial
          (initial :: initial :: front ++ remainder) final) := by
    simpa only [List.cons_append, endpointWord_eq,
      wordOfPrefixFinal_cons, Word.append_assoc] using contraction
  exact (derivesMiddlePermutation initial final sourcePerm).trans <|
    contracted.trans <|
      derivesMiddlePermutation initial final targetPerm.symm

private theorem derivesDeleteFinalExcess
    (initial final : Nat) (front reduced : List Nat)
    (countEq : reduced.count final = 2) :
    Derives basis
      (endpointWord initial (front ++ final :: reduced) final)
      (endpointWord initial (front ++ reduced) final) := by
  let remainder := (reduced.erase final).erase final
  have firstCount : (reduced.erase final).count final = 1 := by
    rw [List.count_erase_self, countEq]
  have remainderCount : remainder.count final = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, firstCount]
  have sourcePerm :
      (front ++ final :: reduced).Perm
        ((front ++ remainder) ++ [final, final, final]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = final
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have targetPerm :
      (front ++ reduced).Perm
        ((front ++ remainder) ++ [final, final]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = final
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have contraction :=
    Derives.prepend (wordOfCons initial (front ++ remainder))
      (derivesFourToThree (Word.singleton final))
  have contracted :
      Derives basis
        (endpointWord initial
          ((front ++ remainder) ++ [final, final, final]) final)
        (endpointWord initial
          ((front ++ remainder) ++ [final, final]) final) := by
    have sourceShape :
        wordOfCons initial (front ++ remainder) ++
            (((Word.singleton final ++ Word.singleton final) ++
              Word.singleton final) ++ Word.singleton final) =
          endpointWord initial
            ((front ++ remainder) ++ [final, final, final]) final := by
      apply Word.toList_injective
      simp [endpointWord, wordOfCons, Word.toList, List.append_assoc]
    have targetShape :
        wordOfCons initial (front ++ remainder) ++
            ((Word.singleton final ++ Word.singleton final) ++
              Word.singleton final) =
          endpointWord initial
            ((front ++ remainder) ++ [final, final]) final := by
      apply Word.toList_injective
      simp [endpointWord, wordOfCons, Word.toList, List.append_assoc]
    rw [← sourceShape, ← targetShape]
    exact contraction
  exact (derivesMiddlePermutation initial final sourcePerm).trans <|
    contracted.trans <|
      derivesMiddlePermutation initial final targetPerm.symm

private theorem derivesDeleteClosedExcess
    (endpoint : Nat) (front reduced : List Nat)
    (countEq : reduced.count endpoint = 1) :
    Derives basis
      (endpointWord endpoint (front ++ endpoint :: reduced) endpoint)
      (endpointWord endpoint (front ++ reduced) endpoint) := by
  let remainder := reduced.erase endpoint
  have remainderCount : remainder.count endpoint = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, countEq]
  have sourcePerm :
      (front ++ endpoint :: reduced).Perm
        (endpoint :: endpoint :: front ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = endpoint
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have targetPerm :
      (front ++ reduced).Perm
        (endpoint :: front ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = endpoint
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have arranged :=
    derivesMiddlePermutation endpoint endpoint sourcePerm
  have contraction :
      Derives basis
        (endpointWord endpoint
          (endpoint :: endpoint :: front ++ remainder) endpoint)
        (endpointWord endpoint
          (endpoint :: front ++ remainder) endpoint) := by
    cases restEq : front ++ remainder with
    | nil =>
        simpa [endpointWord, restEq, Word.append,
          Word.singleton, Word.append_assoc] using
            derivesFourToThree (Word.singleton endpoint)
    | cons next rest =>
        have contracted :=
          derivesTripleClosedContraction
            (Word.singleton endpoint) (wordOfCons next rest)
        simpa [endpointWord, restEq, wordOfCons, Word.append,
          Word.singleton, Word.append_assoc, List.append_assoc] using
            contracted
  exact arranged.trans <|
    contraction.trans <|
      derivesMiddlePermutation endpoint endpoint targetPerm.symm

private theorem derivesDeleteCapThreeExcess
    (initial final selected : Nat) (front reduced : List Nat)
    (totalEq :
      endpointCopies initial final selected + reduced.count selected = 3) :
    Derives basis
      (endpointWord initial (front ++ selected :: reduced) final)
      (endpointWord initial (front ++ reduced) final) := by
  by_cases atInitial : selected = initial
  · subst selected
    by_cases closed : initial = final
    · subst final
      have countEq : reduced.count initial = 1 := by
        simp [endpointCopies] at totalEq
        omega
      exact derivesDeleteClosedExcess initial front reduced countEq
    · have countEq : reduced.count initial = 2 := by
        simp [endpointCopies, Ne.symm closed] at totalEq
        omega
      exact derivesDeleteInitialExcess initial final front reduced countEq
  · by_cases atFinal : selected = final
    · subst selected
      have countEq : reduced.count final = 2 := by
        simp [endpointCopies, Ne.symm atInitial] at totalEq
        omega
      exact derivesDeleteFinalExcess initial final front reduced countEq
    · have countEq : reduced.count selected = 3 := by
        simp [endpointCopies, Ne.symm atInitial, Ne.symm atFinal] at totalEq
        omega
      exact derivesDeleteFourInterior
        initial final selected front reduced countEq

private theorem derivesNormalizeCapThreeAux :
    ∀ (initial : Nat) (front middle : List Nat) (final : Nat),
      Derives basis
        (endpointWord initial (front ++ middle) final)
        (endpointWord initial
          (front ++ endpointCapThreeReduce initial final middle) final)
  | initial, front, [], final => by
      exact Derives.refl _
  | initial, front, selected :: tail, final => by
      have tailNormal :=
        derivesNormalizeCapThreeAux
          initial (front ++ [selected]) tail final
      let reduced := endpointCapThreeReduce initial final tail
      have firstStep :
          Derives basis
            (endpointWord initial (front ++ selected :: tail) final)
            (endpointWord initial (front ++ selected :: reduced) final) := by
        simpa [reduced, List.append_assoc] using tailNormal
      by_cases small :
          endpointCopies initial final selected + reduced.count selected < 3
      · have reduceEq :
            endpointCapThreeReduce initial final (selected :: tail) =
              selected :: reduced := by
          simp [endpointCapThreeReduce, reduced, small]
        rw [reduceEq]
        exact firstStep
      · have totalLe :
            endpointCopies initial final selected +
                reduced.count selected ≤ 3 := by
          simpa [reduced] using
            endpointCapThreeReduce_total_le_three
              initial final selected tail
        have totalEq :
            endpointCopies initial final selected +
                reduced.count selected = 3 := by
          omega
        have reduceEq :
            endpointCapThreeReduce initial final (selected :: tail) =
              reduced := by
          simp [endpointCapThreeReduce, reduced, small]
        rw [reduceEq]
        exact firstStep.trans <|
          derivesDeleteCapThreeExcess
            initial final selected front reduced totalEq
termination_by
  _ _ middle _ => middle.length

/-- Derive protected-endpoint whole-word cap-three normalization. -/
theorem derivesNormalizeCapThree
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (endpointWord initial middle final)
      (endpointWord initial
        (endpointCapThreeReduce initial final middle) final) := by
  simpa using derivesNormalizeCapThreeAux initial [] middle final

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

private theorem reverse_endpointWord
    (initial : Nat) (middle : List Nat) (final : Nat) :
    (endpointWord initial middle final).reverse =
      Word.mk final (middle.reverse ++ [initial]) := by
  apply Word.toList_injective
  rw [Word.toList_reverse, toList_endpointWord]
  simp [Word.toList, List.reverse_append]

/-- The independently complete target-opposite basis transfers actual right
validity back to the independently certified `S5_529` opposite factor. -/
theorem rightValid_sourceOpposite
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.CoRoots.S5_529.table.semigroup.opposite := by
  change identity.SatisfiedBy
    SemigroupBasis.Generated.S5_529Transfers.S5_532.targetSemigroup.opposite
    at valid
  have lower :=
    SemigroupBasis.Generated.S5_529Transfers.S5_532.opposite_basis.2
      identity valid
  exact fun valuation =>
    Derives.sound
      SemigroupBasis.CoRoots.S5_529.opposite_basis.1
      lower valuation

/-- Reverse actual opposite validity into the independently complete source. -/
theorem rightValid_sourceReversed
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.reversed.SatisfiedBy
      SemigroupBasis.CoRoots.S5_529.table.semigroup :=
  (Identity.satisfiedBy_opposite_iff_reversed identity
    SemigroupBasis.CoRoots.S5_529.table.semigroup).mp
      (rightValid_sourceOpposite identity valid)

/-- Actual right-factor validity fixes the terminal variable. -/
theorem rightValid_reverseHead
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.lhs.reverse.head = identity.rhs.reverse.head :=
  SemigroupBasis.CoRoots.S5_529.valid_head
    identity.reversed (rightValid_sourceReversed identity valid)

private theorem cappedExponent_eq_min (count : Nat) :
    headSortedCappedThreeExponent count = min count 3 := by
  unfold headSortedCappedThreeExponent
  split <;> rename_i bound <;> omega

/-- Actual right-factor validity fixes unrestricted whole-word multiplicities
capped at three. -/
theorem rightValid_cappedCount
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup)
    (tested : Nat) :
    min (identity.lhs.toList.count tested) 3 =
      min (identity.rhs.toList.count tested) 3 := by
  have exponents :=
    SemigroupBasis.CoRoots.S5_529.valid_exponent
      identity.reversed (rightValid_sourceReversed identity valid) tested
  simpa [Identity.reversed, Word.toList_reverse,
    List.count_reverse, cappedExponent_eq_min] using exponents

/-- The actual left-zero factor fixes the initial variable. -/
theorem leftValid_head
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  change identity.SatisfiedBy leftZeroTwo.semigroup at valid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 :=
    fun letter => if letter = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

/-- Once both endpoints agree, cap-three equality makes the two normalized
interiors permutations. -/
theorem derivesSameEndpointsOfCappedCounts
    (initial final : Nat) (left right : List Nat)
    (capped : ∀ tested,
      min ((endpointWord initial left final).toList.count tested) 3 =
        min ((endpointWord initial right final).toList.count tested) 3) :
    Derives basis
      (endpointWord initial left final)
      (endpointWord initial right final) := by
  let normalizedLeft := endpointCapThreeReduce initial final left
  let normalizedRight := endpointCapThreeReduce initial final right
  have equalCounts : ∀ tested,
      (endpointWord initial normalizedLeft final).toList.count tested =
        (endpointWord initial normalizedRight final).toList.count tested := by
    intro tested
    change
      (endpointWord initial
          (endpointCapThreeReduce initial final left) final).toList.count
          tested =
        (endpointWord initial
          (endpointCapThreeReduce initial final right) final).toList.count
          tested
    rw [endpointCapThreeReduce_whole_count,
      endpointCapThreeReduce_whole_count, capped tested]
  have middlePerm : normalizedLeft.Perm normalizedRight := by
    rw [List.perm_iff_count]
    intro tested
    have equal := equalCounts tested
    rw [count_endpointWord, count_endpointWord] at equal
    omega
  exact (derivesNormalizeCapThree initial left final).trans <|
    (derivesMiddlePermutation initial final middlePerm).trans <|
      (derivesNormalizeCapThree initial right final).symm

/-- Independent unrestricted completeness over arbitrary natural-number
supports, using the actual initial/final/cap-three factor invariants. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have heads := leftValid_head identity leftValid
  have finals := rightValid_reverseHead identity rightValid
  have capped := rightValid_cappedCount identity rightValid
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  change leftHead = rightHead at heads
  subst rightHead
  cases leftTail with
  | nil =>
      cases rightTail with
      | nil =>
          exact Derives.refl _
      | cons rightSecond rightRest =>
          by_cases same : rightSecond = leftHead
          · subst rightSecond
            have count := capped leftHead
            simp [Word.toList] at count
            omega
          · have count := capped rightSecond
            simp [Word.toList, Ne.symm same] at count
            omega
  | cons leftSecond leftRest =>
      cases rightTail with
      | nil =>
          by_cases same : leftSecond = leftHead
          · subst leftSecond
            have count := capped leftHead
            simp [Word.toList] at count
            omega
          · have count := capped leftSecond
            simp [Word.toList, Ne.symm same] at count
      | cons rightSecond rightRest =>
          let leftSplit := splitMiddleFinal leftSecond leftRest
          let rightSplit := splitMiddleFinal rightSecond rightRest
          have leftReconstruct :
              endpointWord leftHead leftSplit.1 leftSplit.2 =
                Word.mk leftHead (leftSecond :: leftRest) :=
            endpointWord_splitMiddleFinal leftHead leftSecond leftRest
          have rightReconstruct :
              endpointWord leftHead rightSplit.1 rightSplit.2 =
                Word.mk leftHead (rightSecond :: rightRest) :=
            endpointWord_splitMiddleFinal leftHead rightSecond rightRest
          have equalFinals : leftSplit.2 = rightSplit.2 := by
            have aligned := finals
            rw [← leftReconstruct, ← rightReconstruct,
              reverse_endpointWord, reverse_endpointWord] at aligned
            exact aligned
          have bridge :
              Derives basis
                (endpointWord leftHead leftSplit.1 leftSplit.2)
                (endpointWord leftHead rightSplit.1 rightSplit.2) := by
            rw [← equalFinals]
            apply derivesSameEndpointsOfCappedCounts
            intro tested
            rw [leftReconstruct, equalFinals, rightReconstruct]
            exact capped tested
          rw [← leftReconstruct, ← rightReconstruct]
          exact bridge

/-- Construct the reviewed pair structure only after unrestricted proof. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Certified reusable protected-endpoint cap-three rank-102 seed. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_9736_representative_basis :
    BasisFor S6_9736.table.semigroup basis :=
  S6_9736.representative_basis_of_normalizer normalizer

theorem s6_9736_opposite_basis :
    BasisFor S6_9736.table.semigroup.opposite (reversedBasis basis) :=
  S6_9736.opposite_basis_of_normalizer normalizer

/-- Further transport keeps every displayed-law derivation and both
independently established target-factor theory implications explicit. -/
noncomputable def transportedNormalizer
    {A : Type u} {B : Type v}
    {targetLeft : Semigroup A} {targetRight : Semigroup B}
    {targetBasis : List (Identity Nat)}
    (lawDerivations :
      ∀ law : Identity Nat,
        law ∈ basis → Derives targetBasis law.lhs law.rhs)
    (leftTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetLeft →
          identity.SatisfiedBy leftTable.semigroup)
    (rightTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetRight →
          identity.SatisfiedBy rightTable.semigroup) :
    IntersectionNormalizer targetLeft targetRight targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer lawDerivations leftTheory rightTheory

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank102.Seed

import SemigroupBasis.CoRoots.Order6LeeLiProposition8ASyntax

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeLiProposition8A

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons :=
  S5_107.listWordOfCons

private def instantiateFourWords
    (x h y t : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => h
  | 2 => y
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

private theorem basisTripleGatherGeneral :
    Derives basis htxxx xhxtx :=
  Derives.fromBasis (e := tripleGatherGeneralLaw) (by simp [basis])

private theorem basisTripleGatherFinalGapEmpty :
    Derives basis hxxx xhxx :=
  Derives.fromBasis (e := tripleGatherFinalGapEmptyLaw) (by simp [basis])

private theorem basisTripleGatherInitialGapEmpty :
    Derives basis txxx xxtx :=
  Derives.fromBasis (e := tripleGatherInitialGapEmptyLaw) (by simp [basis])

private theorem basisPower :
    Derives basis xxx xxxx :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

private theorem derivesGatherTripleGeneral
    (x h t : Word Nat) :
    Derives basis ((((x ++ h) ++ x) ++ t) ++ x)
      ((((h ++ t) ++ x) ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisTripleGatherGeneral
      (instantiateFourWords x h x t)
  simpa [htxxx, xhxtx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

private theorem derivesGatherTripleFinalGapEmpty
    (x h : Word Nat) :
    Derives basis (((x ++ h) ++ x) ++ x)
      (((h ++ x) ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisTripleGatherFinalGapEmpty
      (instantiateFourWords x h x x)
  simpa [hxxx, xhxx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

private theorem derivesGatherTripleInitialGapEmpty
    (x t : Word Nat) :
    Derives basis (((x ++ x) ++ t) ++ x)
      (((t ++ x) ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisTripleGatherInitialGapEmpty
      (instantiateFourWords x x x t)
  simpa [txxx, xxtx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

private theorem derivesContractFourToThree (x : Word Nat) :
    Derives basis (((x ++ x) ++ x) ++ x) ((x ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisPower (instantiateFourWords x x x x)
  simpa [xxx, xxxx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

/-! ## Gathering three displayed occurrences -/

/-- Gather three displayed occurrences of `letter` at the position of the
last one.  The four branches are precisely laws 1--3, with reflexivity when
both intervening gaps are empty. -/
theorem listDerivesGatherThreeToLast
    (letter : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
        [letter] ++ after)
      (before ++ firstGap ++ secondGap ++ [letter, letter, letter] ++
        after) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            (S5_107.ListDerives.refl (basis := basis)
              (before ++ [letter, letter, letter] ++ after))
      | cons secondHead secondTail =>
          let secondWord :=
            listWordOfCons secondHead secondTail
          have gathered := S5_107.ListDerives.ofWord
            (derivesGatherTripleInitialGapEmpty
              (Word.singleton letter) secondWord)
          simpa [secondWord, listWordOfCons, Word.singleton,
            Word.append, Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after gathered
  | cons firstHead firstTail =>
      let firstWord :=
        listWordOfCons firstHead firstTail
      cases secondGap with
      | nil =>
          have gathered := S5_107.ListDerives.ofWord
            (derivesGatherTripleFinalGapEmpty
              (Word.singleton letter) firstWord)
          simpa [firstWord, listWordOfCons, Word.singleton,
            Word.append, Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after gathered
      | cons secondHead secondTail =>
          let secondWord :=
            listWordOfCons secondHead secondTail
          have gathered := S5_107.ListDerives.ofWord
            (derivesGatherTripleGeneral
              (Word.singleton letter) firstWord secondWord)
          simpa [firstWord, secondWord, listWordOfCons,
            Word.singleton, Word.append, Word.append_assoc,
            List.append_assoc] using
              S5_107.ListDerives.context before after gathered

/-- A gathered cube and one later occurrence can be gathered into a fourth
power.  For a nonempty middle this is law 1 followed by law 2; the empty
middle is reflexive. -/
theorem listDerivesGatherCubeWithLast
    (letter : Nat) (before middle after : List Nat) :
    ListDerives
      (before ++ [letter, letter, letter] ++ middle ++ [letter] ++ after)
      (before ++ middle ++ [letter, letter, letter, letter] ++ after) := by
  cases middle with
  | nil =>
      simpa [List.append_assoc] using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++ [letter, letter, letter, letter] ++ after))
  | cons middleHead middleTail =>
      let middleWord :=
        listWordOfCons middleHead middleTail
      have first :=
        derivesGatherTripleGeneral
          (Word.singleton letter) (Word.singleton letter) middleWord
      have second :=
        Derives.appendRight
          (derivesGatherTripleFinalGapEmpty
            (Word.singleton letter) middleWord)
          (Word.singleton letter)
      have gathered := S5_107.ListDerives.ofWord (first.trans second)
      simpa [middleWord, listWordOfCons, Word.singleton,
        Word.append, Word.append_assoc, List.append_assoc] using
          S5_107.ListDerives.context before after gathered

/-- Gather four arbitrarily separated displayed occurrences at the position
of the last one. -/
theorem listDerivesGatherFourToLast
    (letter : Nat)
    (before firstGap secondGap thirdGap after : List Nat) :
    ListDerives
      (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
        [letter] ++ thirdGap ++ [letter] ++ after)
      (before ++ firstGap ++ secondGap ++ thirdGap ++
        [letter, letter, letter, letter] ++ after) := by
  have gatherFirstThree :=
    listDerivesGatherThreeToLast letter before firstGap secondGap
      (thirdGap ++ [letter] ++ after)
  have gatherWithLast :=
    listDerivesGatherCubeWithLast letter
      (before ++ firstGap ++ secondGap) thirdGap after
  have firstStep :
      ListDerives
        (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
          [letter] ++ thirdGap ++ [letter] ++ after)
        (before ++ firstGap ++ secondGap ++ [letter, letter, letter] ++
          thirdGap ++ [letter] ++ after) := by
    simpa [List.append_assoc] using gatherFirstThree
  have secondStep :
      ListDerives
        (before ++ firstGap ++ secondGap ++ [letter, letter, letter] ++
          thirdGap ++ [letter] ++ after)
        (before ++ firstGap ++ secondGap ++ thirdGap ++
          [letter, letter, letter, letter] ++ after) := by
    simpa [List.append_assoc] using gatherWithLast
  exact firstStep.trans secondStep

/-- Contract a displayed fourth power to a cube in arbitrary context. -/
theorem listDerivesContractFourToThree
    (letter : Nat) (before after : List Nat) :
    ListDerives
      (before ++ [letter, letter, letter, letter] ++ after)
      (before ++ [letter, letter, letter] ++ after) := by
  have contracted := S5_107.ListDerives.ofWord
    (derivesContractFourToThree (Word.singleton letter))
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      S5_107.ListDerives.context before after contracted

/-- Cap four arbitrarily separated displayed occurrences to three, without
any hypothesis on the gaps or surrounding context. -/
theorem listDerivesCapFourthOccurrence
    (letter : Nat)
    (before firstGap secondGap thirdGap after : List Nat) :
    ListDerives
      (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
        [letter] ++ thirdGap ++ [letter] ++ after)
      (before ++ firstGap ++ secondGap ++ thirdGap ++
        [letter, letter, letter] ++ after) := by
  have gathered :=
    listDerivesGatherFourToLast letter before firstGap secondGap
      thirdGap after
  have contracted :=
    listDerivesContractFourToThree letter
      (before ++ firstGap ++ secondGap ++ thirdGap) after
  exact gathered.trans <| by
    simpa [List.append_assoc] using contracted

/-! ## Unrestricted cap-three reduction -/

private theorem existsTwoOccurrenceSplit
    (letter : Nat) :
    ∀ {letters : List Nat},
      2 ≤ letters.count letter →
        ∃ before middle after,
          letters = before ++ letter :: middle ++ letter :: after
  | [], count => by
      simp at count
  | first :: rest, count => by
      by_cases equality : first = letter
      · subst first
        have restPositive : 0 < rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        have restMember : letter ∈ rest :=
          List.count_pos_iff.mp restPositive
        obtain ⟨middle, after, split⟩ :=
          List.mem_iff_append.mp restMember
        exact ⟨[], middle, after,
          by simp [split, List.append_assoc]⟩
      · have restCount : 2 ≤ rest.count letter := by
          simpa [equality] using count
        obtain ⟨before, middle, after, split⟩ :=
          existsTwoOccurrenceSplit letter restCount
        exact ⟨first :: before, middle, after,
          by simp [split, List.append_assoc]⟩

private theorem existsThreeOccurrenceSplit
    (letter : Nat) :
    ∀ {letters : List Nat},
      3 ≤ letters.count letter →
        ∃ before firstGap secondGap after,
          letters = before ++ letter :: firstGap ++ letter ::
            secondGap ++ letter :: after
  | [], count => by
      simp at count
  | first :: rest, count => by
      by_cases equality : first = letter
      · subst first
        have restCount : 2 ≤ rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        obtain ⟨firstGap, secondGap, after, split⟩ :=
          existsTwoOccurrenceSplit letter restCount
        exact ⟨[], firstGap, secondGap, after,
          by simp [split, List.append_assoc]⟩
      · have restCount : 3 ≤ rest.count letter := by
          simpa [equality] using count
        obtain ⟨before, firstGap, secondGap, after, split⟩ :=
          existsThreeOccurrenceSplit letter restCount
        exact ⟨first :: before, firstGap, secondGap, after,
          by simp [split, List.append_assoc]⟩

private theorem existsCapThreeReductionFrom :
    ∀ (remaining kept : List Nat),
      (∀ tested, kept.count tested ≤ 3) →
        ∃ reduced : List Nat,
          (∀ tested, reduced.count tested ≤ 3) ∧
          (∀ tested,
            reduced.count tested =
              min ((kept ++ remaining).count tested) 3) ∧
          ListDerives (kept ++ remaining) reduced
  | [], kept, keptBound => by
      refine ⟨kept, keptBound, ?_, ?_⟩
      · intro tested
        simpa using (Nat.min_eq_left (keptBound tested)).symm
      · simpa using
          (S5_107.ListDerives.refl (basis := basis) kept)
  | letter :: rest, kept, keptBound => by
      by_cases room : kept.count letter < 3
      · have nextBound :
            ∀ tested, (kept ++ [letter]).count tested ≤ 3 := by
          intro tested
          rw [List.count_append]
          by_cases equality : letter = tested
          · subst letter
            simp only [List.count_cons_self, List.count_nil]
            omega
          · have singletonZero : [letter].count tested = 0 := by
              simp [equality]
            rw [singletonZero, Nat.add_zero]
            exact keptBound tested
        obtain ⟨reduced, reducedBound, counts, derivation⟩ :=
          existsCapThreeReductionFrom rest (kept ++ [letter]) nextBound
        refine ⟨reduced, reducedBound, ?_, ?_⟩
        · simpa [List.append_assoc] using counts
        · simpa [List.append_assoc] using derivation
      · have full : kept.count letter = 3 := by
          have bound := keptBound letter
          omega
        obtain ⟨before, firstGap, secondGap, after, split⟩ :=
          existsThreeOccurrenceSplit letter (letters := kept) (by omega)
        let nextKept :=
          before ++ firstGap ++ secondGap ++ after ++
            [letter, letter, letter]
        have nextBound :
            ∀ tested, nextKept.count tested ≤ 3 := by
          intro tested
          by_cases equality : tested = letter
          · subst tested
            have splitCount := congrArg (List.count letter) split
            simp only [List.count_append, List.count_cons_self] at splitCount
            simp only [nextKept, List.count_append,
              List.count_cons_self, List.count_nil]
            omega
          · have countEq :
                nextKept.count tested = kept.count tested := by
              rw [split]
              simp [nextKept, List.count_append, equality,
                Ne.symm equality]
            rw [countEq]
            exact keptBound tested
        have cappedCounts :
            ∀ tested,
              min ((nextKept ++ rest).count tested) 3 =
                min ((kept ++ letter :: rest).count tested) 3 := by
          intro tested
          by_cases equality : tested = letter
          · subst tested
            have nextLarge :
                3 ≤ (nextKept ++ rest).count letter := by
              rw [List.count_append]
              have splitCount := congrArg (List.count letter) split
              simp only [List.count_append,
                List.count_cons_self] at splitCount
              have nextCount : nextKept.count letter = 3 := by
                simp only [nextKept, List.count_append,
                  List.count_cons_self, List.count_nil]
                omega
              omega
            have sourceLarge :
                3 ≤ (kept ++ letter :: rest).count letter := by
              rw [List.count_append, List.count_cons_self]
              omega
            rw [Nat.min_eq_right nextLarge,
              Nat.min_eq_right sourceLarge]
          · have countEq :
                (nextKept ++ rest).count tested =
                  (kept ++ letter :: rest).count tested := by
              rw [split]
              simp [nextKept, List.count_append, equality,
                Ne.symm equality]
            rw [countEq]
        obtain ⟨reduced, reducedBound, counts, recurse⟩ :=
          existsCapThreeReductionFrom rest nextKept nextBound
        have capCurrent :
            ListDerives (kept ++ letter :: rest)
              (nextKept ++ rest) := by
          rw [split]
          simpa [nextKept, List.append_assoc] using
            listDerivesCapFourthOccurrence letter before firstGap
              secondGap after rest
        refine ⟨reduced, reducedBound, ?_, capCurrent.trans recurse⟩
        intro tested
        exact (counts tested).trans (cappedCounts tested)

/-- Every finite list derives to a list in which every multiplicity is at
most three, with the exact pointwise capped multiplicities.  No validity,
nonemptiness, alphabet, or length hypothesis is required. -/
theorem existsCapThreeReduction (letters : List Nat) :
    ∃ reduced : List Nat,
      (∀ tested, reduced.count tested ≤ 3) ∧
      (∀ tested,
        reduced.count tested = min (letters.count tested) 3) ∧
      S5_107.ListDerives basis letters reduced := by
  simpa using existsCapThreeReductionFrom letters [] (by simp)

end SemigroupBasis.CoRoots.Order6LeeLiProposition8A

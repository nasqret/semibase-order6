import SemigroupBasis.Examples.CommutativeParityThresholdFive
import SemigroupBasis.Examples.CommutativePeriodTwoFromThree
import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo
import SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850
import SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_2850
import SemigroupBasis.Generated.S3_8
import SemigroupBasis.Generated.S5_222

namespace SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_2850

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev rootBasis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.basis
private abbrev rootSemigroup : Semigroup (Fin 6) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup

/-! ## Root derivations -/

private theorem periodTwoFromThreeAxiomsDerive
    (identity : Identity Nat)
    (member : identity ∈ commutativePeriodTwoFromThreeBasis) :
    Derives rootBasis identity.lhs identity.rhs := by
  simp only [commutativePeriodTwoFromThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact
      Derives.fromBasis
        (basis :=
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.basis)
        (e := SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.law0)
        (List.Mem.head _)
  · exact
      Derives.fromBasis
        (basis :=
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.basis)
        (e := SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.law1)
        (List.Mem.tail _ (List.Mem.head _))

private theorem derivesPeriodTwoFromThree {left right : Word Nat}
    (derivation :
      Derives commutativePeriodTwoFromThreeBasis left right) :
    Derives rootBasis left right :=
  derivation.transport periodTwoFromThreeAxiomsDerive

private theorem derivesCommutativity (left right : Word Nat) :
    Derives rootBasis (left ++ right) (right ++ left) :=
  derivesPeriodTwoFromThree
    (periodTwoFromThreeDerivesCommutativity left right)

private theorem derivesPermutation (left right : Word Nat)
    (permutation : left.toList.Perm right.toList) :
    Derives rootBasis left right :=
  derivesPeriodTwoFromThree
    (periodTwoFromThreeDerivesPermutation left right permutation)

private def instantiateTwoWords
    (left right : Word Nat) : Nat → Word Nat
  | 0 => left
  | 1 => right
  | n + 2 => Word.singleton (n + 2)

/-- The contextual root law replays `xx = xxxx` while a nonempty marker is
retained. -/
private theorem derivesContextFourExpansion
    (marker word : Word Nat) :
    Derives rootBasis
      (marker ++ (word ++ word))
      (marker ++ (((word ++ word) ++ word) ++ word)) := by
  have base :
      Derives rootBasis
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.law2.lhs
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.law2.rhs :=
    Derives.fromBasis
      (basis :=
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.basis)
      (e := SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.law2)
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have substituted :=
    Derives.subst base (instantiateTwoWords word marker)
  have enter := derivesCommutativity marker (word ++ word)
  have exit :=
    derivesCommutativity (((word ++ word) ++ word) ++ word) marker
  exact Derives.trans enter <|
    Derives.trans
      (by
        simpa [SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.law2,
          instantiateTwoWords, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
            substituted)
      (by simpa [Word.append_assoc] using exit)

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay the period-two-from-two normalizer behind one fixed nonempty
marker. The marker supplies the residual variable in `xxy = xxxxy`. -/
private theorem liftPeriodTwoFromTwo
    {left right : Word Nat}
    (derivation : Derives commutativePeriodTwoFromTwoBasis left right)
    (marker : Word Nat) (substitution : Nat → Word Nat) :
    Derives rootBasis
      (marker ++ left.bind substitution)
      (marker ++ right.bind substitution) := by
  induction derivation generalizing marker substitution with
  | fromBasis member =>
      simp only [commutativePeriodTwoFromTwoBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [periodTwoFromTwoPowerLaw, periodTwoFromTwoXX,
          periodTwoFromTwoXXXX, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using
          derivesContextFourExpansion marker (substitution 0)
      · have commute :=
          derivesCommutativity (substitution 0) (substitution 1)
        simpa [periodTwoFromTwoCommutativityLaw,
          periodTwoFromTwoXY, periodTwoFromTwoYX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend marker commute
  | refl =>
      exact Derives.refl _
  | symm _ inductionHypothesis =>
      exact Derives.symm (inductionHypothesis marker substitution)
  | trans _ _ first second =>
      exact Derives.trans
        (first marker substitution) (second marker substitution)
  | prepend stem _ inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        inductionHypothesis
          (marker ++ stem.bind substitution) substitution
  | appendRight _ suffix inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis marker substitution)
          (suffix.bind substitution)
  | subst _ first inductionHypothesis =>
      simpa [bind_bind] using
        inductionHypothesis marker
          (fun letter => (first letter).bind substitution)

/-! ## Canonical lists -/

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def wordOfList (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => wordOfCons head tail

private theorem wordOfList_toList
    (fallback : Nat) {letters : List Nat} (nonempty : letters ≠ []) :
    (wordOfList fallback letters).toList = letters := by
  cases letters with
  | nil => contradiction
  | cons head tail => rfl

private def sortLetters (letters : List Nat) : List Nat :=
  letters.mergeSort (fun left right : Nat => decide (left ≤ right))

private theorem sortLetters_perm (letters : List Nat) :
    (sortLetters letters).Perm letters := by
  exact List.mergeSort_perm _ _

private theorem sortLetters_pairwise (letters : List Nat) :
    (sortLetters letters).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right first second
    exact decide_eq_true
      (Nat.le_trans
        (of_decide_eq_true first)
        (of_decide_eq_true second))
  have total :
      ∀ left right : Nat,
        (decide (left ≤ right) || decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with first | second
    · simp [first]
    · simp [second]
  have sorted := List.pairwise_mergeSort transitive total letters
  simpa [sortLetters] using
    (sorted.imp fun relation => of_decide_eq_true relation)

private theorem sortLetters_eq_of_perm
    {left right : List Nat} (permutation : left.Perm right) :
    sortLetters left = sortLetters right := by
  have sortedPermutation :
      (sortLetters left).Perm (sortLetters right) :=
    (sortLetters_perm left).trans <|
      permutation.trans (sortLetters_perm right).symm
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    (sortLetters_pairwise left) (sortLetters_pairwise right)
    sortedPermutation

private theorem any_ne_eq_true_iff (fixed : Nat) :
    ∀ letters : List Nat,
      (letters.any fun letter => decide (letter ≠ fixed)) = true ↔
        ∃ letter, letter ∈ letters ∧ letter ≠ fixed
  | [] => by simp
  | head :: tail => by
      simp only [List.any_cons, Bool.or_eq_true, decide_eq_true_eq,
        List.mem_cons]
      rw [any_ne_eq_true_iff fixed tail]
      constructor
      · rintro (different | ⟨letter, member, different⟩)
        · exact ⟨head, Or.inl rfl, different⟩
        · exact ⟨letter, Or.inr member, different⟩
      · rintro ⟨letter, (rfl | member), different⟩
        · exact Or.inl different
        · exact Or.inr ⟨letter, member, different⟩

private def hasOther (word : Word Nat) : Bool :=
  word.tail.any fun letter => decide (letter ≠ word.head)

private theorem hasOther_eq_true_iff (word : Word Nat) :
    hasOther word = true ↔
      ∃ letter, letter ∈ word.toList ∧ letter ≠ word.head := by
  rw [hasOther, any_ne_eq_true_iff]
  constructor
  · rintro ⟨letter, member, different⟩
    exact ⟨letter, List.Mem.tail word.head member, different⟩
  · rintro ⟨letter, member, different⟩
    simp only [Word.toList, List.mem_cons] at member
    rcases member with rfl | member
    · exact False.elim (different rfl)
    · exact ⟨letter, member, different⟩

private def normalList (word : Word Nat) : List Nat :=
  if hasOther word = true then
    sortLetters (periodTwoFromTwoReduce word.toList)
  else
    sortLetters (periodTwoFromThreeReduce word.toList)

private def normal (word : Word Nat) : Word Nat :=
  wordOfList word.head (normalList word)

private theorem periodTwoFromTwoReduce_word_ne_nil (word : Word Nat) :
    periodTwoFromTwoReduce word.toList ≠ [] := by
  intro empty
  have count := count_periodTwoFromTwoReduce word.head word.toList
  rw [empty, List.count_nil] at count
  have positive :
      0 < periodTwoFromTwoExponent
        (word.toList.count word.head) :=
    periodTwoFromTwoExponent_pos <|
      List.count_pos_iff.mpr (by simp [Word.toList])
  omega

private theorem periodTwoFromThreeReduce_word_ne_nil
    (word : Word Nat) :
    periodTwoFromThreeReduce word.toList ≠ [] := by
  intro empty
  have count := count_periodTwoFromThreeReduce word.head word.toList
  rw [empty, List.count_nil] at count
  have positive :
      0 < periodTwoFromThreeExponent
        (word.toList.count word.head) :=
    periodTwoFromThreeExponent_pos <|
      List.count_pos_iff.mpr (by simp [Word.toList])
  omega

private theorem sortLetters_ne_nil
    {letters : List Nat} (nonempty : letters ≠ []) :
    sortLetters letters ≠ [] := by
  cases letters with
  | nil => contradiction
  | cons head tail =>
      intro sortedEmpty
      have permutation := sortLetters_perm (head :: tail)
      rw [sortedEmpty] at permutation
      exact List.not_perm_cons_nil permutation.symm

private theorem normalList_ne_nil (word : Word Nat) :
    normalList word ≠ [] := by
  cases flag : hasOther word with
  | false =>
      simpa [normalList, flag] using
        sortLetters_ne_nil
          (periodTwoFromThreeReduce_word_ne_nil word)
  | true =>
      simpa [normalList, flag] using
        sortLetters_ne_nil
          (periodTwoFromTwoReduce_word_ne_nil word)

private theorem normal_toList (word : Word Nat) :
    (normal word).toList = normalList word := by
  exact wordOfList_toList word.head (normalList_ne_nil word)

private theorem derivesPermutationToList
    (source : Word Nat) (fallback : Nat) (target : List Nat)
    (permutation : source.toList.Perm target) :
    Derives rootBasis source (wordOfList fallback target) := by
  cases target with
  | nil =>
      cases source with
      | mk head tail =>
          have impossible :
              (head :: tail).Perm ([] : List Nat) := by
            simpa [Word.toList] using permutation
          exact False.elim (List.not_perm_cons_nil impossible)
  | cons head tail =>
      apply derivesPermutation
      simpa [wordOfList, wordOfCons, Word.toList] using permutation

private theorem derivesUnarySorted (word : Word Nat) :
    Derives rootBasis word
      (wordOfList word.head
        (sortLetters (periodTwoFromThreeReduce word.toList))) := by
  have reducedNonempty := periodTwoFromThreeReduce_word_ne_nil word
  have oldNormal := periodTwoFromThreeDerivesNormal word
  cases reduced : periodTwoFromThreeReduce word.toList with
  | nil => exact False.elim (reducedNonempty reduced)
  | cons head tail =>
      rw [reduced] at oldNormal
      have first :
          Derives rootBasis word
            (wordOfList word.head
              (periodTwoFromThreeReduce word.toList)) := by
        rw [reduced]
        simpa [wordOfList, wordOfCons] using
          derivesPeriodTwoFromThree oldNormal
      have permutation :
          (wordOfList word.head
              (periodTwoFromThreeReduce word.toList)).toList.Perm
            (sortLetters
              (periodTwoFromThreeReduce word.toList)) := by
        rw [wordOfList_toList word.head reducedNonempty]
        exact (sortLetters_perm _).symm
      exact first.trans <|
        derivesPermutationToList _ word.head _ (by
          simpa [reduced] using permutation)

/-! ## Supported period-two reduction -/

private def frontedWord (marker : Nat) (word : Word Nat) : Word Nat :=
  wordOfCons marker (word.toList.erase marker)

private def markerReduce (marker : Nat) (word : Word Nat) : Word Nat :=
  wordOfCons marker
    (periodTwoFromTwoReduce (word.toList.erase marker))

private def doubleMarkerReduce
    (first second : Nat) (word : Word Nat) : Word Nat :=
  markerReduce second (markerReduce first word)

private theorem word_perm_frontedWord
    (marker : Nat) (word : Word Nat)
    (present : marker ∈ word.toList) :
    word.toList.Perm (frontedWord marker word).toList := by
  simpa [frontedWord, wordOfCons, Word.toList] using
    List.perm_cons_erase present

private theorem periodTwoFromTwoReduce_cons_ne_nil
    (head : Nat) (tail : List Nat) :
    periodTwoFromTwoReduce (head :: tail) ≠ [] := by
  intro empty
  have count := count_periodTwoFromTwoReduce head (head :: tail)
  rw [empty, List.count_nil, List.count_cons_self] at count
  have positive :
      0 < periodTwoFromTwoExponent (tail.count head + 1) :=
    periodTwoFromTwoExponent_pos (by omega)
  omega

private theorem derivesMarkerReduce
    (marker : Nat) (word : Word Nat)
    (present : marker ∈ word.toList)
    (other : ∃ letter, letter ∈ word.toList ∧ letter ≠ marker) :
    Derives rootBasis word (markerReduce marker word) := by
  obtain ⟨letter, letterMember, different⟩ := other
  have eraseMember : letter ∈ word.toList.erase marker :=
    (List.mem_erase_of_ne different).mpr letterMember
  have arrange :=
    derivesPermutation word (frontedWord marker word)
      (word_perm_frontedWord marker word present)
  cases erased : word.toList.erase marker with
  | nil =>
      rw [erased] at eraseMember
      simp at eraseMember
  | cons restHead restTail =>
      let rest : Word Nat := wordOfCons restHead restTail
      have oldNormal := periodTwoFromTwoDerivesNormal rest
      cases reduced : periodTwoFromTwoReduce rest.toList with
      | nil =>
          exact False.elim <|
            periodTwoFromTwoReduce_cons_ne_nil restHead restTail <| by
              simpa [rest, wordOfCons, Word.toList] using reduced
      | cons normalHead normalTail =>
          rw [reduced] at oldNormal
          change
            Derives commutativePeriodTwoFromTwoBasis
              rest (wordOfCons normalHead normalTail) at oldNormal
          have lifted :=
            liftPeriodTwoFromTwo oldNormal
              (Word.singleton marker) Word.singleton
          rw [bind_singleton, bind_singleton] at lifted
          change
            Derives rootBasis
              (wordOfCons marker (restHead :: restTail))
              (wordOfCons marker (normalHead :: normalTail)) at lifted
          have reduced' :
              periodTwoFromTwoReduce (restHead :: restTail) =
                normalHead :: normalTail := by
            simpa [rest, wordOfCons, Word.toList] using reduced
          exact Derives.trans arrange <| by
            change
              Derives rootBasis
                (wordOfCons marker (word.toList.erase marker))
                (wordOfCons marker
                  (periodTwoFromTwoReduce
                    (word.toList.erase marker)))
            rw [erased, reduced']
            exact lifted

private theorem count_markerReduce
    (tested marker : Nat) (word : Word Nat)
    (_present : marker ∈ word.toList) :
    (markerReduce marker word).toList.count tested =
      if tested = marker then
        1 + periodTwoFromTwoExponent
          (word.toList.count tested - 1)
      else
        periodTwoFromTwoExponent (word.toList.count tested) := by
  by_cases same : tested = marker
  · subst tested
    rw [show (markerReduce marker word).toList =
        marker :: periodTwoFromTwoReduce
          (word.toList.erase marker) by rfl]
    rw [List.count_cons_self, count_periodTwoFromTwoReduce,
      List.count_erase_self]
    simp [Nat.add_comm]
  · rw [show (markerReduce marker word).toList =
        marker :: periodTwoFromTwoReduce
          (word.toList.erase marker) by rfl]
    rw [List.count_cons_of_ne (Ne.symm same),
      count_periodTwoFromTwoReduce, List.count_erase_of_ne same]
    simp [same]

private theorem markerReduce_mem_of_ne
    (first second : Nat) (word : Word Nat)
    (firstMember : first ∈ word.toList)
    (secondMember : second ∈ word.toList)
    (different : second ≠ first) :
    second ∈ (markerReduce first word).toList := by
  rw [← List.count_pos_iff,
    count_markerReduce second first word firstMember]
  simp only [if_neg different]
  exact periodTwoFromTwoExponent_pos
    (List.count_pos_iff.mpr secondMember)

private theorem periodTwoFromTwoExponent_le_three (n : Nat) :
    periodTwoFromTwoExponent n ≤ 3 := by
  unfold periodTwoFromTwoExponent
  split <;> omega

private theorem periodTwoFromTwoExponent_eq_self_of_le_three
    (n : Nat) (bound : n ≤ 3) :
    periodTwoFromTwoExponent n = n := by
  unfold periodTwoFromTwoExponent
  split <;> omega

private theorem periodTwoFromTwoExponent_idempotent (n : Nat) :
    periodTwoFromTwoExponent (periodTwoFromTwoExponent n) =
      periodTwoFromTwoExponent n :=
  periodTwoFromTwoExponent_eq_self_of_le_three _
    (periodTwoFromTwoExponent_le_three n)

private theorem periodTwoFromTwoExponent_firstMarker
    {n : Nat} (positive : 0 < n) :
    periodTwoFromTwoExponent
        (1 + periodTwoFromTwoExponent (n - 1)) =
      periodTwoFromTwoExponent n := by
  have stateBound := periodTwoFromTwoExponent_le_three (n - 1)
  have successor := periodTwoFromTwoExponent_succ (n - 1)
  have predecessorSuccessor : n - 1 + 1 = n := by omega
  rw [predecessorSuccessor] at successor
  by_cases below : periodTwoFromTwoExponent (n - 1) < 3
  · rw [if_pos below] at successor
    have fixed :=
      periodTwoFromTwoExponent_eq_self_of_le_three
        (1 + periodTwoFromTwoExponent (n - 1)) (by omega)
    rw [fixed]
    omega
  · rw [if_neg below] at successor
    have stateEq : periodTwoFromTwoExponent (n - 1) = 3 := by
      omega
    calc
      periodTwoFromTwoExponent
          (1 + periodTwoFromTwoExponent (n - 1)) =
          periodTwoFromTwoExponent 4 := by rw [stateEq]
      _ = 2 := rfl
      _ = periodTwoFromTwoExponent n := by omega

private theorem periodTwoFromTwoExponent_secondMarker
    {n : Nat} (positive : 0 < n) :
    1 + periodTwoFromTwoExponent
        (periodTwoFromTwoExponent n - 1) =
      periodTwoFromTwoExponent n := by
  have statePositive := periodTwoFromTwoExponent_pos positive
  have stateBound := periodTwoFromTwoExponent_le_three n
  have fixed :=
    periodTwoFromTwoExponent_eq_self_of_le_three
      (periodTwoFromTwoExponent n - 1) (by omega)
  rw [fixed]
  omega

private theorem count_doubleMarkerReduce
    (tested first second : Nat) (word : Word Nat)
    (firstMember : first ∈ word.toList)
    (secondMember : second ∈ word.toList)
    (different : first ≠ second) :
    (doubleMarkerReduce first second word).toList.count tested =
      periodTwoFromTwoExponent (word.toList.count tested) := by
  let firstWord := markerReduce first word
  have secondInFirst : second ∈ firstWord.toList :=
    markerReduce_mem_of_ne first second word
      firstMember secondMember (Ne.symm different)
  by_cases testedSecond : tested = second
  · subst tested
    rw [doubleMarkerReduce,
      count_markerReduce second second firstWord secondInFirst,
      if_pos rfl,
      count_markerReduce second first word firstMember,
      if_neg (Ne.symm different)]
    exact periodTwoFromTwoExponent_secondMarker
      (List.count_pos_iff.mpr secondMember)
  · rw [doubleMarkerReduce,
      count_markerReduce tested second firstWord secondInFirst,
      if_neg testedSecond]
    by_cases testedFirst : tested = first
    · subst tested
      rw [count_markerReduce first first word firstMember, if_pos rfl]
      exact periodTwoFromTwoExponent_firstMarker
        (List.count_pos_iff.mpr firstMember)
    · rw [count_markerReduce tested first word firstMember,
        if_neg testedFirst]
      exact periodTwoFromTwoExponent_idempotent _

private theorem derivesDoubleMarkerReduce
    (first second : Nat) (word : Word Nat)
    (firstMember : first ∈ word.toList)
    (secondMember : second ∈ word.toList)
    (different : first ≠ second) :
    Derives rootBasis word
      (doubleMarkerReduce first second word) := by
  have firstDerivation :=
    derivesMarkerReduce first word firstMember
      ⟨second, secondMember, Ne.symm different⟩
  have secondInFirst :
      second ∈ (markerReduce first word).toList :=
    markerReduce_mem_of_ne first second word
      firstMember secondMember (Ne.symm different)
  have firstInFirst : first ∈ (markerReduce first word).toList := by
    simp [markerReduce, wordOfCons, Word.toList]
  have secondDerivation :=
    derivesMarkerReduce second (markerReduce first word)
      secondInFirst ⟨first, firstInFirst, different⟩
  exact Derives.trans firstDerivation secondDerivation

private theorem derivesSupportedSorted
    (word : Word Nat)
    (multiple :
      ∃ second, second ∈ word.toList ∧ second ≠ word.head) :
    Derives rootBasis word
      (wordOfList word.head
        (sortLetters (periodTwoFromTwoReduce word.toList))) := by
  obtain ⟨second, secondMember, secondNe⟩ := multiple
  let first := word.head
  have firstMember : first ∈ word.toList := by
    simp [first, Word.toList]
  have different : first ≠ second := Ne.symm secondNe
  have reduced :=
    derivesDoubleMarkerReduce first second word
      firstMember secondMember different
  have reducedPermutation :
      (doubleMarkerReduce first second word).toList.Perm
        (periodTwoFromTwoReduce word.toList) := by
    rw [List.perm_iff_count]
    intro tested
    rw [count_doubleMarkerReduce tested first second word
        firstMember secondMember different,
      count_periodTwoFromTwoReduce]
  have sortedPermutation :
      (doubleMarkerReduce first second word).toList.Perm
        (sortLetters (periodTwoFromTwoReduce word.toList)) :=
    reducedPermutation.trans (sortLetters_perm _).symm
  exact reduced.trans <|
    derivesPermutationToList _ word.head _ sortedPermutation

private theorem normalizes (word : Word Nat) :
    Derives rootBasis word (normal word) := by
  cases flag : hasOther word with
  | false =>
      simpa [normal, normalList, flag] using derivesUnarySorted word
  | true =>
      have multiple := (hasOther_eq_true_iff word).mp flag
      simpa [normal, normalList, flag] using
        derivesSupportedSorted word multiple

/-! ## Factor separation -/

private theorem s3_8_table_eq_canonical_catalogue :
    SemigroupBasis.Generated.S3_8.table =
      SemigroupBasis.Generated.Catalogue.S3_8.table := by
  unfold SemigroupBasis.Generated.S3_8.table
    SemigroupBasis.Generated.Catalogue.S3_8.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext left right
  decide +revert

private theorem catalogueS3_8_table_eq_commutativeExponentThree :
    SemigroupBasis.Generated.Catalogue.S3_8.table =
      commutativeExponentThree := by
  calc
    SemigroupBasis.Generated.Catalogue.S3_8.table =
        SemigroupBasis.Generated.S3_8.table :=
      s3_8_table_eq_canonical_catalogue.symm
    _ = commutativeExponentThree :=
      SemigroupBasis.Generated.S3_8.table_eq_catalogue_model

private theorem catalogueS5_222_table_eq_commutativeParityThresholdFive :
    SemigroupBasis.Generated.Catalogue.S5_222.table =
      commutativeParityThresholdFive := by
  calc
    SemigroupBasis.Generated.Catalogue.S5_222.table =
        SemigroupBasis.Generated.S5_222.table :=
      SemigroupBasis.Generated.S5_222.table_eq_canonical_catalogue.symm
    _ = commutativeParityThresholdFive := rfl

private theorem satisfiedBy_of_table_eq
    {source target : FiniteTable} (tableEq : source = target)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy source.semigroup) :
    identity.SatisfiedBy target.semigroup := by
  cases tableEq
  exact valid

private theorem support_of_capped_count_eq
    {left right : List Nat}
    (capped : ∀ letter,
      min (left.count letter) 2 = min (right.count letter) 2) :
    ∀ letter, letter ∈ left ↔ letter ∈ right := by
  intro letter
  constructor
  · intro member
    have positive : 0 < left.count letter :=
      List.count_pos_iff.mpr member
    have rightPositive : 0 < right.count letter := by
      have equal := capped letter
      omega
    exact List.count_pos_iff.mp rightPositive
  · intro member
    have positive : 0 < right.count letter :=
      List.count_pos_iff.mpr member
    have leftPositive : 0 < left.count letter := by
      have equal := capped letter
      omega
    exact List.count_pos_iff.mp leftPositive

private theorem hasOther_true_of_two
    (word : Word Nat) {first second : Nat}
    (firstMember : first ∈ word.toList)
    (secondMember : second ∈ word.toList)
    (different : first ≠ second) :
    hasOther word = true := by
  apply (hasOther_eq_true_iff word).mpr
  by_cases secondHead : second = word.head
  · refine ⟨first, firstMember, ?_⟩
    intro firstHead
    exact different (firstHead.trans secondHead.symm)
  · exact ⟨second, secondMember, secondHead⟩

private theorem all_letters_eq_head_of_hasOther_false
    (word : Word Nat) (flag : hasOther word = false) :
    ∀ letter, letter ∈ word.toList → letter = word.head := by
  intro letter member
  apply Decidable.byContradiction
  intro different
  have trueFlag :=
    (hasOther_eq_true_iff word).mpr ⟨letter, member, different⟩
  rw [flag] at trueFlag
  contradiction

private theorem count_eq_length_of_all_eq
    (letter : Nat) (letters : List Nat)
    (allEqual : ∀ tested, tested ∈ letters → tested = letter) :
    letters.count letter = letters.length := by
  induction letters with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headEq : head = letter := allEqual head (by simp)
      subst head
      rw [List.count_cons_self, List.length_cons]
      congr 1
      exact inductionHypothesis <| by
        intro tested member
        exact allEqual tested (by simp [member])

private theorem periodTwoFromTwoExponent_eq_of_capped_parity
    {left right : Nat}
    (capped : min left 2 = min right 2)
    (parity : left % 2 = right % 2) :
    periodTwoFromTwoExponent left =
      periodTwoFromTwoExponent right := by
  unfold periodTwoFromTwoExponent
  by_cases leftShort : left < 2
  · have rightShort : right < 2 := by omega
    simp [leftShort, rightShort]
    omega
  · have rightShort : ¬right < 2 := by omega
    simp [leftShort, rightShort, parity]

private theorem periodTwoFromThreeExponent_eq_of_capped_parity
    {left right : Nat}
    (capped : min left 3 = min right 3)
    (parity : left % 2 = right % 2) :
    periodTwoFromThreeExponent left =
      periodTwoFromThreeExponent right := by
  unfold periodTwoFromThreeExponent
  by_cases leftShort : left < 3
  · have rightShort : right < 3 := by omega
    simp [leftShort, rightShort]
    omega
  · have rightShort : ¬right < 3 := by omega
    simp [leftShort, rightShort]
    omega

private theorem separates
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_222.table.semigroup) :
    normal identity.lhs = normal identity.rhs := by
  have leftValid' :
      identity.SatisfiedBy commutativeExponentThree.semigroup :=
    satisfiedBy_of_table_eq
      catalogueS3_8_table_eq_commutativeExponentThree identity leftValid
  have rightValid' :
      identity.SatisfiedBy commutativeParityThresholdFive.semigroup :=
    satisfiedBy_of_table_eq
      catalogueS5_222_table_eq_commutativeParityThresholdFive identity
        rightValid
  have capped := exponentValid_capped_count_eq identity leftValid'
  have support := support_of_capped_count_eq capped
  have parity := parityThresholdValid_parity identity rightValid'
  have cappedLength :=
    parityThresholdValid_capped_length identity rightValid'
  cases leftFlag : hasOther identity.lhs with
  | true =>
      obtain ⟨second, secondLeft, secondNe⟩ :=
        (hasOther_eq_true_iff identity.lhs).mp leftFlag
      have firstLeft : identity.lhs.head ∈ identity.lhs.toList := by
        simp [Word.toList]
      have firstRight : identity.lhs.head ∈ identity.rhs.toList :=
        (support identity.lhs.head).mp firstLeft
      have secondRight : second ∈ identity.rhs.toList :=
        (support second).mp secondLeft
      have rightFlag : hasOther identity.rhs = true :=
        hasOther_true_of_two identity.rhs
          firstRight secondRight (Ne.symm secondNe)
      have exponentEq :
          ∀ tested,
            periodTwoFromTwoExponent
                (identity.lhs.toList.count tested) =
              periodTwoFromTwoExponent
                (identity.rhs.toList.count tested) := by
        intro tested
        exact periodTwoFromTwoExponent_eq_of_capped_parity
          (capped tested) (parity tested)
      have reducedPermutation :
          (periodTwoFromTwoReduce identity.lhs.toList).Perm
            (periodTwoFromTwoReduce identity.rhs.toList) :=
        periodTwoFromTwoReduce_perm_of_exponent_eq exponentEq
      have sortedEq := sortLetters_eq_of_perm reducedPermutation
      apply Word.toList_injective
      rw [normal_toList, normal_toList]
      simpa [normalList, leftFlag, rightFlag] using sortedEq
  | false =>
      have leftAll :=
        all_letters_eq_head_of_hasOther_false identity.lhs leftFlag
      have rightFlag : hasOther identity.rhs = false := by
        cases candidate : hasOther identity.rhs with
        | false => rfl
        | true =>
            obtain ⟨second, secondRight, secondNe⟩ :=
              (hasOther_eq_true_iff identity.rhs).mp candidate
            have firstRight :
                identity.rhs.head ∈ identity.rhs.toList := by
              simp [Word.toList]
            have firstLeft :
                identity.rhs.head ∈ identity.lhs.toList :=
              (support identity.rhs.head).mpr firstRight
            have secondLeft : second ∈ identity.lhs.toList :=
              (support second).mpr secondRight
            have contradiction :=
              hasOther_true_of_two identity.lhs
                firstLeft secondLeft (Ne.symm secondNe)
            rw [leftFlag] at contradiction
            contradiction
      let letter := identity.lhs.head
      have rightAll :
          ∀ tested, tested ∈ identity.rhs.toList →
            tested = letter := by
        intro tested member
        exact leftAll tested ((support tested).mpr member)
      have lengthParity :
          identity.lhs.toList.length % 2 =
            identity.rhs.toList.length % 2 := by
        have coordinateParity := parity letter
        rw [count_eq_length_of_all_eq letter
              identity.lhs.toList leftAll,
          count_eq_length_of_all_eq letter
              identity.rhs.toList rightAll] at coordinateParity
        exact coordinateParity
      have lengthExponent :
          periodTwoFromThreeExponent identity.lhs.toList.length =
            periodTwoFromThreeExponent identity.rhs.toList.length :=
        periodTwoFromThreeExponent_eq_of_capped_parity
          cappedLength lengthParity
      have exponentEq :
          ∀ tested,
            periodTwoFromThreeExponent
                (identity.lhs.toList.count tested) =
              periodTwoFromThreeExponent
                (identity.rhs.toList.count tested) := by
        intro tested
        by_cases testedLetter : tested = letter
        · subst tested
          rw [count_eq_length_of_all_eq letter
                identity.lhs.toList leftAll,
            count_eq_length_of_all_eq letter
                identity.rhs.toList rightAll]
          exact lengthExponent
        · have leftAbsent : tested ∉ identity.lhs.toList := by
            intro member
            exact testedLetter (leftAll tested member)
          have rightAbsent : tested ∉ identity.rhs.toList := by
            intro member
            exact testedLetter (rightAll tested member)
          rw [List.count_eq_zero.mpr leftAbsent,
            List.count_eq_zero.mpr rightAbsent]
      have reducedPermutation :
          (periodTwoFromThreeReduce identity.lhs.toList).Perm
            (periodTwoFromThreeReduce identity.rhs.toList) :=
        periodTwoFromThreeReduce_perm_of_exponent_eq exponentEq
      have sortedEq := sortLetters_eq_of_perm reducedPermutation
      apply Word.toList_injective
      rw [normal_toList, normal_toList]
      simpa [normalList, leftFlag, rightFlag] using sortedEq

/-- Exact unconditional basis endpoint for the mixed generic-CAS root
`S6_2850`. -/
theorem basisFor :
    BasisFor rootSemigroup rootBasis :=
  SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_2850.subdirectPair.basisFor_of_normalForm
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.models
      normalizes separates

end SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_2850

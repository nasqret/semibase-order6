import SemigroupBasis.CoRoots.Order6LeeZhangCondition4Normalization

/-!
# Lee--Zhang Condition 4: canonical words

The first letter is always retained.  When it is globally simple, the second
letter is also retained and the rest of the word is sorted and capped.  When
the first letter repeats, its next occurrence is gathered beside it and the
entire residual tail is sorted and capped.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangCondition4

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private def listWord (head : Nat) (tail : List Nat) : Word Nat :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail

/-- Gather the first occurrence of `marker` in `suffix` beside the leading
copy.  `pre` contains no marker, so list erasure removes exactly the
gathered occurrence. -/
private theorem listDerivesExposeRepeatedMarker :
    ∀ (marker : Nat) (pre suffix : List Nat),
      marker ∉ pre →
      marker ∈ suffix →
      ListDerives
        (marker :: (pre ++ suffix))
        ([marker, marker] ++ pre ++ suffix.erase marker)
  | marker, pre, [], _, present => by
      simp at present
  | marker, pre, candidate :: rest, preFree, present => by
      by_cases equal : candidate = marker
      · subst candidate
        cases pre with
        | nil =>
            have eraseShape : (marker :: rest).erase marker = rest := by
              simp
            rw [List.nil_append, eraseShape]
            exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
        | cons preHead preTail =>
            let markerWord := Word.singleton marker
            let preWord := listWord preHead preTail
            have gathered :=
              SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
                (derivesRepeatedFirstMove
                  markerWord preWord).symm
            simpa [markerWord, preWord, listWord,
              SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.toList_append,
              List.append_assoc] using gathered.append rest
      · have presentInRest : marker ∈ rest := by
          have expanded : marker = candidate ∨ marker ∈ rest := by
            simpa using present
          rcases expanded with hit | inRest
          · exact absurd hit.symm equal
          · exact inRest
        have extendedFree : marker ∉ pre ++ [candidate] := by
          simp [preFree, Ne.symm equal]
        have recurse :=
          listDerivesExposeRepeatedMarker marker
            (pre ++ [candidate]) rest extendedFree presentInRest
        simpa [equal, List.append_assoc] using recurse
termination_by
  _ _ suffix _ _ => suffix.length

/-- The deterministic corrected Condition-4 canonical list. -/
def canonicalList : List Nat → List Nat
  | [] => []
  | [head] => [head]
  | head :: second :: tail =>
      if head ∈ second :: tail then
        [head, head] ++
          residualNormal head ((second :: tail).erase head)
      else
        [head, second] ++ simpleResidualNormal second tail

theorem canonicalList_nonempty :
    ∀ (head : Nat) (tail : List Nat),
      canonicalList (head :: tail) ≠ [] := by
  intro head tail
  cases tail with
  | nil => simp [canonicalList]
  | cons second rest =>
      by_cases repeated : head = second ∨ head ∈ rest
      · simp [canonicalList, repeated]
      · simp [canonicalList, repeated]

/-- The second letter is semantically protected exactly when the first letter
is globally simple. -/
def simpleSecond (word : Word Nat) : Option Nat :=
  if word.toList.count word.head = 1 then word.tail.head? else none

structure SameSignature (left right : Word Nat) : Prop where
  headEq : left.head = right.head
  cappedCounts :
    ∀ letter,
      min (left.toList.count letter) 2 =
        min (right.toList.count letter) 2
  simpleSecondEq : simpleSecond left = simpleSecond right

/-- The corrected signature uniquely determines the canonical list. -/
theorem canonicalList_eq_of_signature
    {left right : Word Nat} (same : SameSignature left right) :
    canonicalList left.toList = canonicalList right.toList := by
  cases left with
  | mk head leftTail =>
      cases right with
      | mk rightHead rightTail =>
          have headEq : head = rightHead := same.headEq
          subst rightHead
          cases leftTail with
          | nil =>
              cases rightTail with
              | nil => rfl
              | cons rightSecond rightRest =>
                  exfalso
                  by_cases secondEq : rightSecond = head
                  · subst rightSecond
                    have capped := same.cappedCounts head
                    simp [Word.toList] at capped
                  · have capped := same.cappedCounts rightSecond
                    simp [Word.toList, secondEq,
                      Ne.symm secondEq] at capped
                    omega
          | cons leftSecond leftRest =>
              cases rightTail with
              | nil =>
                  exfalso
                  by_cases secondEq : leftSecond = head
                  · subst leftSecond
                    have capped := same.cappedCounts head
                    simp [Word.toList] at capped
                  · have capped := same.cappedCounts leftSecond
                    simp [Word.toList, secondEq,
                      Ne.symm secondEq] at capped
              | cons rightSecond rightRest =>
                  have repeatedIff :
                      head ∈ leftSecond :: leftRest ↔
                        head ∈ rightSecond :: rightRest := by
                    have capped := same.cappedCounts head
                    simp only [Word.toList,
                      List.count_cons_self] at capped
                    constructor
                    · intro repeated
                      have positive :
                          0 < (leftSecond :: leftRest).count head :=
                        List.count_pos_iff.mpr repeated
                      apply List.count_pos_iff.mp
                      omega
                    · intro repeated
                      have positive :
                          0 < (rightSecond :: rightRest).count head :=
                        List.count_pos_iff.mpr repeated
                      apply List.count_pos_iff.mp
                      omega
                  by_cases repeatedLeft :
                      head ∈ leftSecond :: leftRest
                  · have repeatedRight :=
                      repeatedIff.mp repeatedLeft
                    have residualEq :=
                      residualNormal_eq_of_cappedCounts
                        head
                        ((leftSecond :: leftRest).erase head)
                        ((rightSecond :: rightRest).erase head)
                        (by
                          intro letter
                          by_cases letterEq : letter = head
                          · subst letter
                            simp [residualLimit]
                          · have capped := same.cappedCounts letter
                            simp only [Word.toList,
                              List.count_cons_of_ne
                                (Ne.symm letterEq)] at capped
                            simpa [residualLimit, letterEq,
                              List.count_erase_of_ne letterEq] using
                                capped)
                    simpa [canonicalList, Word.toList, repeatedLeft,
                      repeatedRight] using
                        congrArg (fun tail => [head, head] ++ tail)
                          residualEq
                  · have repeatedRight :
                        head ∉ rightSecond :: rightRest :=
                      fun repeated =>
                        repeatedLeft (repeatedIff.mpr repeated)
                    have leftHeadCount :
                        (head :: leftSecond :: leftRest).count head = 1 := by
                      simp [List.count_eq_zero.mpr repeatedLeft]
                    have rightHeadCount :
                        (head :: rightSecond :: rightRest).count head = 1 := by
                      simp [List.count_eq_zero.mpr repeatedRight]
                    have secondEq : leftSecond = rightSecond := by
                      have protectedFact := same.simpleSecondEq
                      simp [simpleSecond, Word.toList, leftHeadCount,
                        rightHeadCount] at protectedFact
                      exact protectedFact
                    subst rightSecond
                    have headNeSecond : head ≠ leftSecond := by
                      intro equal
                      subst leftSecond
                      exact repeatedLeft (by simp)
                    have leftHeadAbsent : head ∉ leftRest := by
                      intro member
                      exact repeatedLeft (by simp [member])
                    have rightHeadAbsent : head ∉ rightRest := by
                      intro member
                      exact repeatedRight (by simp [member])
                    have residualEq :=
                      simpleResidualNormal_eq_of_cappedCounts
                        leftSecond leftRest rightRest (by
                          intro letter
                          by_cases isHead : letter = head
                          · subst letter
                            simp [simpleResidualLimit, headNeSecond,
                              List.count_eq_zero.mpr leftHeadAbsent,
                              List.count_eq_zero.mpr rightHeadAbsent]
                          · by_cases isSecond : letter = leftSecond
                            · subst letter
                              have capped := same.cappedCounts leftSecond
                              simp [Word.toList, headNeSecond,
                                Ne.symm headNeSecond] at capped
                              simp [simpleResidualLimit]
                              omega
                            · have capped := same.cappedCounts letter
                              simpa [Word.toList, isHead, isSecond,
                                Ne.symm isHead, Ne.symm isSecond,
                                simpleResidualLimit] using capped)
                    simpa [canonicalList, Word.toList, repeatedLeft,
                      repeatedRight] using
                        congrArg
                          (fun tail => [head, leftSecond] ++ tail)
                          residualEq

/-- Every list derives to its deterministic Condition-4 representative. -/
theorem listDerivesCanonical :
    ∀ letters : List Nat,
      ListDerives letters (canonicalList letters)
  | [] =>
      SemigroupBasis.CoRoots.S5_107.ListDerives.empty
  | [head] =>
      SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | head :: second :: tail => by
      by_cases repeated : head ∈ second :: tail
      · have expose :=
          listDerivesExposeRepeatedMarker
            head [] (second :: tail) (by simp) repeated
        have normalize :=
          listDerivesResidualNormal
            head ((second :: tail).erase head)
        simpa [canonicalList, repeated, List.append_assoc] using
          expose.trans normalize
      · simpa [canonicalList, repeated, List.append_assoc] using
          listDerivesSimpleResidualNormal head second tail
termination_by
  letters => letters.length

/-- A convenient word-valued wrapper around `canonicalList`. -/
def canonicalWord (word : Word Nat) : Word Nat :=
  match canonicalList word.toList with
  | [] => Word.singleton word.head
  | head :: tail => listWord head tail

theorem canonicalWord_toList (word : Word Nat) :
    (canonicalWord word).toList = canonicalList word.toList := by
  cases word with
  | mk head tail =>
      have nonempty := canonicalList_nonempty head tail
      cases equation : canonicalList (head :: tail) with
      | nil =>
          exact (nonempty equation).elim
      | cons canonicalHead canonicalTail =>
          simp [canonicalWord, Word.toList, equation, listWord,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons]

theorem derivesCanonicalWord (word : Word Nat) :
    Derives basis word (canonicalWord word) := by
  cases word with
  | mk head tail =>
      have normalized := listDerivesCanonical (head :: tail)
      have shape : canonicalList (head :: tail) =
          canonicalList (Word.toList (⟨head, tail⟩ : Word Nat)) := rfl
      rw [shape, ← canonicalWord_toList] at normalized
      exact
        SemigroupBasis.CoRoots.S5_107.ListDerives.toWord normalized

/-- Equality of canonical lists is sufficient for derivability. -/
theorem derivesOfCanonicalListEq
    (left right : Word Nat)
    (sameCanonical :
      canonicalList left.toList = canonicalList right.toList) :
    Derives basis left right := by
  have leftStep := derivesCanonicalWord left
  have rightStep := derivesCanonicalWord right
  have middle : canonicalWord left = canonicalWord right := by
    apply Word.toList_injective
    rw [canonicalWord_toList, canonicalWord_toList, sameCanonical]
  rw [middle] at leftStep
  exact leftStep.trans rightStep.symm

end SemigroupBasis.CoRoots.Order6LeeZhangCondition4

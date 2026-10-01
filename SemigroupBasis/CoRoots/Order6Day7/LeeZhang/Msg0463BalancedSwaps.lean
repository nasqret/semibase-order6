import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463BalancedCore

/-! Balanced-core square transport and externally witnessed adjacent swaps.
The published M18 induction shapes now use only the thirteen explicitly
included count-preserving core rules. No power contraction or square-bank
deduplication appears in this module. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.BalancedCore

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop := S5_107.ListDerives basis

private def instantiateTwoWords
    (x y : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | n + 2 => Word.singleton (n + 2)

/-- The square of any nonempty word commutes with every nonempty word.
This is the direct nonempty-substitution instance of `xxy = yxx`. -/
theorem derivesSquareBlockAcross (block payload : Word Nat) :
    Derives basis
      ((block ++ block) ++ payload)
      (payload ++ (block ++ block)) := by
  have substituted :=
    derivesPrefixRotationSubstitution
      (instantiateTwoWords block payload)
  change
    Derives basis
      ((block ++ block) ++ payload)
      ((payload ++ block) ++ block) at substituted
  simpa [Word.append_assoc] using substituted

/-- A square block crosses an arbitrary list. Empty blocks and empty
payloads are discharged by reflexivity; all nonempty cases use
`derivesSquareBlockAcross`, so no empty substitution image is introduced. -/
theorem listDerivesBlockSquareAcross
    (block payload : List Nat) :
    ListDerives
      (block ++ block ++ payload)
      (payload ++ block ++ block) := by
  cases block with
  | nil =>
      simpa using
        S5_107.ListDerives.refl (basis := basis) payload
  | cons blockHead blockTail =>
      cases payload with
      | nil =>
          simpa using
            S5_107.ListDerives.refl (basis := basis)
              ((blockHead :: blockTail) ++
                (blockHead :: blockTail))
      | cons payloadHead payloadTail =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSquareBlockAcross
                  (S5_107.listWordOfCons blockHead blockTail)
                  (S5_107.listWordOfCons payloadHead payloadTail)

/-- A single-letter pair crosses an arbitrary list, including the empty
list. -/
theorem listDerivesPairAcross (letter : Nat) (payload : List Nat) :
    ListDerives
      ([letter, letter] ++ payload)
      (payload ++ [letter, letter]) := by
  simpa [List.append_assoc] using
    listDerivesBlockSquareAcross [letter] payload

/-- Relocate an adjacent pair through arbitrary left and right contexts. -/
theorem listDerivesPairAcrossContext
    (prefixWords : List Nat) (letter : Nat)
    (payload suffix : List Nat) :
    ListDerives
      (prefixWords ++ [letter, letter] ++ payload ++ suffix)
      (prefixWords ++ payload ++ [letter, letter] ++ suffix) := by
  simpa [List.append_assoc] using
    S5_107.ListDerives.context
      (basis := basis) prefixWords suffix
      (listDerivesPairAcross letter payload)

/-- Render each label as one adjacent square. This is the movable pair bank
that remains after a future extraction pass separates parity residues from
even pairs. -/
def renderSquareBank (labels : List Nat) : List Nat :=
  labels.flatMap fun letter => [letter, letter]

/-- Extracted square banks commute with arbitrary separator skeletons. -/
theorem listDerivesSquareBankAcross :
    ∀ (labels payload : List Nat),
      ListDerives
        (renderSquareBank labels ++ payload)
        (payload ++ renderSquareBank labels)
  | [], payload => by
      simpa [renderSquareBank] using
        S5_107.ListDerives.refl (basis := basis) payload
  | letter :: labels, payload => by
      have restFirst :=
        S5_107.ListDerives.prepend
          (basis := basis) [letter, letter]
          (listDerivesSquareBankAcross labels payload)
      have headSecond :=
        listDerivesPairAcrossContext [] letter payload
          (renderSquareBank labels)
      exact S5_107.ListDerives.trans
        (by simpa [renderSquareBank, List.append_assoc] using restFirst)
        (by simpa [renderSquareBank, List.append_assoc] using headSecond)

/-- Relocate an extracted square bank through arbitrary left and right
contexts. The payload may contain any globally simple separators. -/
theorem listDerivesSquareBankAcrossContext
    (prefixWords labels payload suffix : List Nat) :
    ListDerives
      (prefixWords ++ renderSquareBank labels ++ payload ++ suffix)
      (prefixWords ++ payload ++ renderSquareBank labels ++ suffix) := by
  simpa [List.append_assoc] using
    S5_107.ListDerives.context
      (basis := basis) prefixWords suffix
      (listDerivesSquareBankAcross labels payload)

/-- Every permutation of square-bank labels is derivable. -/
theorem listDerivesSquareBankPermutation
    {source target : List Nat}
    (permutation : source.Perm target) :
    ListDerives
      (renderSquareBank source)
      (renderSquareBank target) := by
  induction permutation with
  | nil =>
      exact S5_107.ListDerives.empty
  | cons letter _ induction =>
      simpa [renderSquareBank] using
        S5_107.ListDerives.prepend
          (basis := basis) [letter, letter] induction
  | swap left right rest =>
      have swapped :=
        listDerivesPairAcross left [right, right]
      simpa [renderSquareBank, List.append_assoc] using
        (S5_107.ListDerives.append
          (basis := basis) swapped
          (renderSquareBank rest)).symm
  | trans _ _ first second =>
      exact S5_107.ListDerives.trans first second

private def instantiateFourWords
    (x y z w : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | 3 => w
  | n + 4 => Word.singleton (n + 4)

/-! ## Adjacent swaps with witnesses outside the displayed interval -/

/-- Swap two adjacent letters when both have later witnesses and both
intervening fillers are nonempty. -/
theorem derivesSwapWithFutureWitnesses
    (left right middle beforeRight : Word Nat) :
    Derives basis
      (((((left ++ right) ++ middle) ++ left) ++ beforeRight) ++ right)
      (((((right ++ left) ++ middle) ++ left) ++ beforeRight) ++ right) := by
  have substituted :=
    derivesWyPrefixTransportSubstitution
      (instantiateFourWords left right middle beforeRight)
  change
    Derives basis
      (((((left ++ right) ++ middle) ++ left) ++ beforeRight) ++ right)
      (((((right ++ left) ++ middle) ++ left) ++ beforeRight) ++ right)
    at substituted
  exact substituted

/-- Future-witness swap with no filler between the two left witnesses. -/
theorem derivesSwapWithFutureWitnessesNoMiddle
    (left right beforeRight : Word Nat) :
    Derives basis
      ((((left ++ right) ++ left) ++ beforeRight) ++ right)
      ((((right ++ left) ++ left) ++ beforeRight) ++ right) := by
  have substituted :=
    derivesWyRotationSubstitution
      (instantiateFourWords left right right beforeRight)
  change
    Derives basis
      ((((left ++ right) ++ left) ++ beforeRight) ++ right)
      ((((right ++ left) ++ left) ++ beforeRight) ++ right)
    at substituted
  exact substituted

/-- Future-witness swap with no filler before the later right witness. -/
theorem derivesSwapWithFutureWitnessesNoBeforeRight
    (left right middle : Word Nat) :
    Derives basis
      ((((left ++ right) ++ middle) ++ left) ++ right)
      ((((right ++ left) ++ middle) ++ left) ++ right) := by
  have substituted :=
    derivesTerminalYTransportSubstitution
      (instantiateFourWords left right middle middle)
  change
    Derives basis
      ((((left ++ right) ++ middle) ++ left) ++ right)
      ((((right ++ left) ++ middle) ++ left) ++ right)
    at substituted
  exact substituted

/-- Future-witness swap with both fillers empty. -/
theorem derivesSwapWithFutureWitnessesShort
    (left right : Word Nat) :
    Derives basis
      (((left ++ right) ++ left) ++ right)
      (((right ++ left) ++ left) ++ right) := by
  have substituted :=
    derivesAlternatingPairSubstitution
      (instantiateFourWords left right right right)
  change
    Derives basis
      (((left ++ right) ++ left) ++ right)
      (((right ++ left) ++ left) ++ right)
    at substituted
  exact substituted

/-- Swap adjacent `left,right` when `right` has a past witness and `left`
has a future witness. The orientation is the reverse of
`x y x z w z = x y z x w z`. -/
theorem derivesSwapWithPastRightFutureLeft
    (left right afterPast beforeFuture : Word Nat) :
    Derives basis
      (((((right ++ afterPast) ++ left) ++ right) ++ beforeFuture) ++ left)
      (((((right ++ afterPast) ++ right) ++ left) ++ beforeFuture) ++ left) := by
  have substituted :=
    derivesLongZwzTransportSubstitution
      (instantiateFourWords right afterPast left beforeFuture)
  change
    Derives basis
      (((((right ++ afterPast) ++ right) ++ left) ++ beforeFuture) ++ left)
      (((((right ++ afterPast) ++ left) ++ right) ++ beforeFuture) ++ left)
    at substituted
  exact substituted.symm

/-- Past/future swap with no filler after the past witness. -/
theorem derivesSwapWithPastRightFutureLeftNoAfterPast
    (left right beforeFuture : Word Nat) :
    Derives basis
      ((((right ++ left) ++ right) ++ beforeFuture) ++ left)
      ((((right ++ right) ++ left) ++ beforeFuture) ++ left) := by
  have substituted :=
    derivesZwzPrefixSubstitution
      (instantiateFourWords right right left beforeFuture)
  change
    Derives basis
      ((((right ++ right) ++ left) ++ beforeFuture) ++ left)
      ((((right ++ left) ++ right) ++ beforeFuture) ++ left)
    at substituted
  exact substituted.symm

/-- Past/future swap with no filler before the future witness. -/
theorem derivesSwapWithPastRightFutureLeftNoBeforeFuture
    (left right afterPast : Word Nat) :
    Derives basis
      ((((right ++ afterPast) ++ left) ++ right) ++ left)
      ((((right ++ afterPast) ++ right) ++ left) ++ left) := by
  have substituted :=
    derivesDoubleZTransportSubstitution
      (instantiateFourWords right afterPast left left)
  change
    Derives basis
      ((((right ++ afterPast) ++ right) ++ left) ++ left)
      ((((right ++ afterPast) ++ left) ++ right) ++ left)
    at substituted
  exact substituted.symm

/-- Past/future swap with both fillers empty. -/
theorem derivesSwapWithPastRightFutureLeftShort
    (left right : Word Nat) :
    Derives basis
      (((right ++ left) ++ right) ++ left)
      (((right ++ right) ++ left) ++ left) := by
  have substituted :=
    derivesDoubleZPrefixSubstitution
      (instantiateFourWords right right left left)
  change
    Derives basis
      (((right ++ right) ++ left) ++ left)
      (((right ++ left) ++ right) ++ left)
    at substituted
  exact substituted.symm

/-- Swap adjacent letters when both have past witnesses and both fillers are
nonempty. -/
theorem derivesSwapWithPastWitnesses
    (left right betweenWitnesses beforeCurrent : Word Nat) :
    Derives basis
      (((((left ++ betweenWitnesses) ++ right) ++ beforeCurrent) ++ left) ++
        right)
      (((((left ++ betweenWitnesses) ++ right) ++ beforeCurrent) ++ right) ++
        left) := by
  have substituted :=
    derivesCrossedWZSubstitution
      (instantiateFourWords left betweenWitnesses right beforeCurrent)
  change
    Derives basis
      (((((left ++ betweenWitnesses) ++ right) ++ beforeCurrent) ++ left) ++
        right)
      (((((left ++ betweenWitnesses) ++ right) ++ beforeCurrent) ++ right) ++
        left)
    at substituted
  exact substituted

/-- Past-witness swap with no filler between the earlier witnesses. -/
theorem derivesSwapWithPastWitnessesNoBetween
    (left right beforeCurrent : Word Nat) :
    Derives basis
      ((((left ++ right) ++ beforeCurrent) ++ left) ++ right)
      ((((left ++ right) ++ beforeCurrent) ++ right) ++ left) := by
  have substituted :=
    derivesWzCrossingSubstitution
      (instantiateFourWords left left right beforeCurrent)
  change
    Derives basis
      ((((left ++ right) ++ beforeCurrent) ++ left) ++ right)
      ((((left ++ right) ++ beforeCurrent) ++ right) ++ left)
    at substituted
  exact substituted

/-- Past-witness swap with no filler before the current adjacent pair. -/
theorem derivesSwapWithPastWitnessesNoBeforeCurrent
    (left right betweenWitnesses : Word Nat) :
    Derives basis
      ((((left ++ betweenWitnesses) ++ right) ++ left) ++ right)
      ((((left ++ betweenWitnesses) ++ right) ++ right) ++ left) := by
  have substituted :=
    derivesTerminalZTransportSubstitution
      (instantiateFourWords left betweenWitnesses right right)
  change
    Derives basis
      ((((left ++ betweenWitnesses) ++ right) ++ left) ++ right)
      ((((left ++ betweenWitnesses) ++ right) ++ right) ++ left)
    at substituted
  exact substituted

/-- Past-witness swap with both fillers empty. -/
theorem derivesSwapWithPastWitnessesShort
    (left right : Word Nat) :
    Derives basis
      (((left ++ right) ++ left) ++ right)
      (((left ++ right) ++ right) ++ left) := by
  have substituted :=
    derivesAlternatingZSubstitution
      (instantiateFourWords left left right right)
  change
    Derives basis
      (((left ++ right) ++ left) ++ right)
      (((left ++ right) ++ right) ++ left)
    at substituted
  exact substituted

/-- List-level future-witness swap. The two fillers may independently be
empty; each empty case uses the corresponding deletion instance already in
the semigroup basis. -/
theorem listDerivesSwapWithFutureWitnesses
    (left right : Nat) (middle beforeRight : List Nat) :
    ListDerives
      ([left, right] ++ middle ++ [left] ++ beforeRight ++ [right])
      ([right, left] ++ middle ++ [left] ++ beforeRight ++ [right]) := by
  cases middle with
  | nil =>
      cases beforeRight with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithFutureWitnessesShort
                  (Word.singleton left) (Word.singleton right)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithFutureWitnessesNoMiddle
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons beforeHead beforeTail)
  | cons middleHead middleTail =>
      cases beforeRight with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithFutureWitnessesNoBeforeRight
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons middleHead middleTail)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithFutureWitnesses
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons middleHead middleTail)
                  (S5_107.listWordOfCons beforeHead beforeTail)

/-- List-level past-right/future-left swap with independently empty
fillers. -/
theorem listDerivesSwapWithPastRightFutureLeft
    (left right : Nat) (afterPast beforeFuture : List Nat) :
    ListDerives
      ([right] ++ afterPast ++ [left, right] ++ beforeFuture ++ [left])
      ([right] ++ afterPast ++ [right, left] ++ beforeFuture ++ [left]) := by
  cases afterPast with
  | nil =>
      cases beforeFuture with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastRightFutureLeftShort
                  (Word.singleton left) (Word.singleton right)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastRightFutureLeftNoAfterPast
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons beforeHead beforeTail)
  | cons afterHead afterTail =>
      cases beforeFuture with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastRightFutureLeftNoBeforeFuture
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons afterHead afterTail)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastRightFutureLeft
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons afterHead afterTail)
                  (S5_107.listWordOfCons beforeHead beforeTail)

/-- List-level past-witness swap with independently empty fillers. -/
theorem listDerivesSwapWithPastWitnesses
    (left right : Nat) (betweenWitnesses beforeCurrent : List Nat) :
    ListDerives
      ([left] ++ betweenWitnesses ++ [right] ++ beforeCurrent ++
        [left, right])
      ([left] ++ betweenWitnesses ++ [right] ++ beforeCurrent ++
        [right, left]) := by
  cases betweenWitnesses with
  | nil =>
      cases beforeCurrent with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastWitnessesShort
                  (Word.singleton left) (Word.singleton right)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastWitnessesNoBetween
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons beforeHead beforeTail)
  | cons betweenHead betweenTail =>
      cases beforeCurrent with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastWitnessesNoBeforeCurrent
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons betweenHead betweenTail)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastWitnesses
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons betweenHead betweenTail)
                  (S5_107.listWordOfCons beforeHead beforeTail)

/-- Swap any adjacent pair whose two letters each have an occurrence in the
fixed outer contexts. The four past/future placements, and both possible
witness orders within one context, are covered by the three deletion-closed
swap families above. -/
theorem listDerivesSwapExternallyWitnessedAdjacent
    (prefixWords before : List Nat) (left right : Nat)
    (after suffix : List Nat)
    (leftExternal : left ∈ prefixWords ∨ left ∈ suffix)
    (rightExternal : right ∈ prefixWords ∨ right ∈ suffix) :
    ListDerives
      (prefixWords ++ before ++ [left, right] ++ after ++ suffix)
      (prefixWords ++ before ++ [right, left] ++ after ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl (basis := basis)
      (prefixWords ++ before ++ [left, left] ++ after ++ suffix)
  rcases leftExternal with leftPast | leftFuture <;>
    rcases rightExternal with rightPast | rightFuture
  · rcases List.append_of_mem leftPast with
      ⟨beforeLeft, afterLeft, prefixShape⟩
    have rightRelative : right ∈ beforeLeft ∨ right ∈ afterLeft := by
      rw [prefixShape] at rightPast
      simpa [equal, Ne.symm equal] using rightPast
    rcases rightRelative with rightBefore | rightAfter
    · rcases List.append_of_mem rightBefore with
        ⟨beforeRight, between, beforeLeftShape⟩
      rw [prefixShape, beforeLeftShape]
      simpa [List.append_assoc] using
        ((listDerivesSwapWithPastWitnesses
          right left between (afterLeft ++ before)).context
            beforeRight (after ++ suffix)).symm
    · rcases List.append_of_mem rightAfter with
        ⟨between, afterRight, afterLeftShape⟩
      rw [prefixShape, afterLeftShape]
      simpa [List.append_assoc] using
        (listDerivesSwapWithPastWitnesses
          left right between (afterRight ++ before)).context
            beforeLeft (after ++ suffix)
  · rcases List.append_of_mem leftPast with
      ⟨beforeLeft, afterLeft, prefixShape⟩
    rcases List.append_of_mem rightFuture with
      ⟨beforeRight, afterRight, suffixShape⟩
    rw [prefixShape, suffixShape]
    simpa [List.append_assoc] using
      ((listDerivesSwapWithPastRightFutureLeft
        right left (afterLeft ++ before) (after ++ beforeRight)).context
          beforeLeft afterRight).symm
  · rcases List.append_of_mem rightPast with
      ⟨beforeRight, afterRight, prefixShape⟩
    rcases List.append_of_mem leftFuture with
      ⟨beforeLeft, afterLeft, suffixShape⟩
    rw [prefixShape, suffixShape]
    simpa [List.append_assoc] using
      (listDerivesSwapWithPastRightFutureLeft
        left right (afterRight ++ before) (after ++ beforeLeft)).context
          beforeRight afterLeft
  · rcases List.append_of_mem leftFuture with
      ⟨beforeLeft, afterLeft, suffixShape⟩
    have rightRelative : right ∈ beforeLeft ∨ right ∈ afterLeft := by
      rw [suffixShape] at rightFuture
      simpa [equal, Ne.symm equal] using rightFuture
    rcases rightRelative with rightBefore | rightAfter
    · rcases List.append_of_mem rightBefore with
        ⟨beforeRight, between, beforeLeftShape⟩
      rw [suffixShape, beforeLeftShape]
      simpa [List.append_assoc] using
        ((listDerivesSwapWithFutureWitnesses
          right left (after ++ beforeRight) between).context
            (prefixWords ++ before) afterLeft).symm
    · rcases List.append_of_mem rightAfter with
        ⟨between, afterRight, afterLeftShape⟩
      rw [suffixShape, afterLeftShape]
      simpa [List.append_assoc] using
        (listDerivesSwapWithFutureWitnesses
          left right (after ++ beforeLeft) between).context
            (prefixWords ++ before) afterRight

/-! ## Context-uniform pair gathering -/

/-- Move the left displayed occurrence across an arbitrary interleaving and
make the two displayed occurrences adjacent. Every interleaved letter must
have a witness outside the displayed interval, either in the prefix or in
`suffix`. The proof is uniform in both contexts and uses no empty
substitution image. -/
theorem listDerivesGatherExternallyWitnessedPair
    (letter : Nat) :
    ∀ (prefixWords middle suffix : List Nat),
      (∀ other, other ∈ middle →
        other ∈ prefixWords ∨ other ∈ suffix) →
      ListDerives
        (prefixWords ++ [letter] ++ middle ++ [letter] ++ suffix)
        (prefixWords ++ middle ++ [letter, letter] ++ suffix)
  | prefixWords, [], suffix, _ => by
      simpa [List.append_assoc] using
        S5_107.ListDerives.refl (basis := basis)
          (prefixWords ++ [letter, letter] ++ suffix)
  | prefixWords, head :: tail, suffix, external => by
      have headExternal : head ∈ prefixWords ∨ head ∈ suffix :=
        external head (by simp)
      have swapped :
          ListDerives
            (prefixWords ++ [letter] ++ (head :: tail) ++ [letter] ++ suffix)
            ((prefixWords ++ [head]) ++ [letter] ++ tail ++ [letter] ++ suffix) := by
        rcases headExternal with headInPrefix | headInSuffix
        · rcases List.append_of_mem headInPrefix with
            ⟨before, afterPast, rfl⟩
          simpa [List.append_assoc] using
            (listDerivesSwapWithPastRightFutureLeft
              letter head afterPast tail).context before suffix
        · rcases List.append_of_mem headInSuffix with
            ⟨beforeRight, after, rfl⟩
          simpa [List.append_assoc] using
            (listDerivesSwapWithFutureWitnesses
              letter head tail beforeRight).context prefixWords after
      have tailExternal : ∀ other, other ∈ tail →
          other ∈ prefixWords ++ [head] ∨ other ∈ suffix := by
        intro other member
        rcases external other (List.mem_cons_of_mem head member) with
          inPrefix | inSuffix
        · exact Or.inl (List.mem_append_left [head] inPrefix)
        · exact Or.inr inSuffix
      have recurse :=
        listDerivesGatherExternallyWitnessedPair letter
          (prefixWords ++ [head]) tail suffix tailExternal
      exact swapped.trans <| by
        simpa [List.append_assoc] using recurse

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.BalancedCore

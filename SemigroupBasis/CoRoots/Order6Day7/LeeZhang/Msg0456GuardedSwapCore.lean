import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_254

/-! Eight balanced, first-order-preserving laws and their guarded swaps.
This core never swaps two distinct first occurrences and contains no
unanchored square-centrality rule. No class-specific endpoint is asserted. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordSwapCore

open SemigroupBasis

def basis : List (Identity Nat) :=
  [S5_254.zwzPrefixLaw,
   S5_254.doubleZPrefixLaw,
   S5_254.longZwzTransportLaw,
   S5_254.doubleZTransportLaw,
   S5_254.crossedWZLaw,
   S5_254.wzCrossingLaw,
   S5_254.terminalZTransportLaw,
   S5_254.alternatingZLaw]

theorem basis_length : basis.length = 8 := rfl

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private def instantiateFourWords
    (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | n + 4 => Word.singleton (n + 4)

theorem derivesZwzPrefix :
    Derives basis S5_254.zwzPrefixLaw.lhs S5_254.zwzPrefixLaw.rhs :=
  Derives.fromBasis (e := S5_254.zwzPrefixLaw) (by decide)

theorem derivesZwzPrefixSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.zwzPrefixLaw.lhs.bind substitution)
      (S5_254.zwzPrefixLaw.rhs.bind substitution) :=
  Derives.subst derivesZwzPrefix substitution

theorem derivesDoubleZPrefix :
    Derives basis S5_254.doubleZPrefixLaw.lhs S5_254.doubleZPrefixLaw.rhs :=
  Derives.fromBasis (e := S5_254.doubleZPrefixLaw) (by decide)

theorem derivesDoubleZPrefixSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.doubleZPrefixLaw.lhs.bind substitution)
      (S5_254.doubleZPrefixLaw.rhs.bind substitution) :=
  Derives.subst derivesDoubleZPrefix substitution

theorem derivesLongZwzTransport :
    Derives basis S5_254.longZwzTransportLaw.lhs S5_254.longZwzTransportLaw.rhs :=
  Derives.fromBasis (e := S5_254.longZwzTransportLaw) (by decide)

theorem derivesLongZwzTransportSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.longZwzTransportLaw.lhs.bind substitution)
      (S5_254.longZwzTransportLaw.rhs.bind substitution) :=
  Derives.subst derivesLongZwzTransport substitution

theorem derivesDoubleZTransport :
    Derives basis S5_254.doubleZTransportLaw.lhs S5_254.doubleZTransportLaw.rhs :=
  Derives.fromBasis (e := S5_254.doubleZTransportLaw) (by decide)

theorem derivesDoubleZTransportSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.doubleZTransportLaw.lhs.bind substitution)
      (S5_254.doubleZTransportLaw.rhs.bind substitution) :=
  Derives.subst derivesDoubleZTransport substitution

theorem derivesCrossedWZ :
    Derives basis S5_254.crossedWZLaw.lhs S5_254.crossedWZLaw.rhs :=
  Derives.fromBasis (e := S5_254.crossedWZLaw) (by decide)

theorem derivesCrossedWZSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.crossedWZLaw.lhs.bind substitution)
      (S5_254.crossedWZLaw.rhs.bind substitution) :=
  Derives.subst derivesCrossedWZ substitution

theorem derivesWzCrossing :
    Derives basis S5_254.wzCrossingLaw.lhs S5_254.wzCrossingLaw.rhs :=
  Derives.fromBasis (e := S5_254.wzCrossingLaw) (by decide)

theorem derivesWzCrossingSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.wzCrossingLaw.lhs.bind substitution)
      (S5_254.wzCrossingLaw.rhs.bind substitution) :=
  Derives.subst derivesWzCrossing substitution

theorem derivesTerminalZTransport :
    Derives basis S5_254.terminalZTransportLaw.lhs S5_254.terminalZTransportLaw.rhs :=
  Derives.fromBasis (e := S5_254.terminalZTransportLaw) (by decide)

theorem derivesTerminalZTransportSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.terminalZTransportLaw.lhs.bind substitution)
      (S5_254.terminalZTransportLaw.rhs.bind substitution) :=
  Derives.subst derivesTerminalZTransport substitution

theorem derivesAlternatingZ :
    Derives basis S5_254.alternatingZLaw.lhs S5_254.alternatingZLaw.rhs :=
  Derives.fromBasis (e := S5_254.alternatingZLaw) (by decide)

theorem derivesAlternatingZSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.alternatingZLaw.lhs.bind substitution)
      (S5_254.alternatingZLaw.rhs.bind substitution) :=
  Derives.subst derivesAlternatingZ substitution

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

/-- The externally witnessed adjacent swap is allowed only when at least
one selected letter already occurs in the fixed prefix. -/
theorem listDerivesSwapSeenAdjacent
    (prefixWords before : List Nat) (left right : Nat)
    (after suffix : List Nat)
    (leftExternal : left ∈ prefixWords ∨ left ∈ suffix)
    (rightExternal : right ∈ prefixWords ∨ right ∈ suffix)
    (seen : left ∈ prefixWords ∨ right ∈ prefixWords) :
    ListDerives
      (prefixWords ++ before ++ [left, right] ++ after ++ suffix)
      (prefixWords ++ before ++ [right, left] ++ after ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
  by_cases leftPast : left ∈ prefixWords
  · by_cases rightPast : right ∈ prefixWords
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
    · have rightFuture := rightExternal.resolve_left rightPast
      rcases List.append_of_mem leftPast with
        ⟨beforeLeft, afterLeft, prefixShape⟩
      rcases List.append_of_mem rightFuture with
        ⟨beforeRight, afterRight, suffixShape⟩
      rw [prefixShape, suffixShape]
      simpa [List.append_assoc] using
        ((listDerivesSwapWithPastRightFutureLeft
          right left (afterLeft ++ before) (after ++ beforeRight)).context
            beforeLeft afterRight).symm
  · have rightPast := seen.resolve_left leftPast
    have leftFuture := leftExternal.resolve_left leftPast
    rcases List.append_of_mem rightPast with
      ⟨beforeRight, afterRight, prefixShape⟩
    rcases List.append_of_mem leftFuture with
      ⟨beforeLeft, afterLeft, suffixShape⟩
    rw [prefixShape, suffixShape]
    simpa [List.append_assoc] using
      (listDerivesSwapWithPastRightFutureLeft
        left right (afterRight ++ before) (after ++ beforeLeft)).context
          beforeRight afterLeft

theorem external_of_repeated (prefixWords suffix : List Nat) (left right : Nat)
    (different : left ≠ right)
    (repeated : 2 ≤ (prefixWords ++ [left, right] ++ suffix).count left) :
    left ∈ prefixWords ∨ left ∈ suffix := by
  by_cases old : left ∈ prefixWords
  · exact Or.inl old
  · have zero := List.count_eq_zero.mpr old
    have total : (prefixWords ++ [left, right] ++ suffix).count left =
        prefixWords.count left + 1 + suffix.count left := by
      simp [List.count_append, Ne.symm different] <;> omega
    rw [total, zero] at repeated
    exact Or.inr (List.count_pos_iff.mp (by omega))

/-- Arbitrarily long contexts; both letters are globally non-simple and
at least one is already seen. No screen window appears in this premise. -/
theorem listDerivesSwapNonSimpleSeen (prefixWords suffix : List Nat) (left right : Nat)
    (leftRepeated : 2 ≤ (prefixWords ++ [left, right] ++ suffix).count left)
    (rightRepeated : 2 ≤ (prefixWords ++ [left, right] ++ suffix).count right)
    (seen : left ∈ prefixWords ∨ right ∈ prefixWords) :
    ListDerives (prefixWords ++ [left, right] ++ suffix)
      (prefixWords ++ [right, left] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
  have leftExternal := external_of_repeated prefixWords suffix left right equal leftRepeated
  have permutedCount : (prefixWords ++ [right, left] ++ suffix).count right =
      (prefixWords ++ [left, right] ++ suffix).count right := by
    simp [List.count_append, equal]
  have rightExternal := external_of_repeated prefixWords suffix right left (Ne.symm equal)
    (by rw [permutedCount]; exact rightRepeated)
  simpa using listDerivesSwapSeenAdjacent prefixWords [] left right [] suffix
    leftExternal rightExternal seen

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordSwapCore

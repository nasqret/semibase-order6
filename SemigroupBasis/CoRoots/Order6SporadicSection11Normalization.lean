import SemigroupBasis.CoRoots.Order6SporadicSection11
import SemigroupBasis.CoRoots.S5_107ListDerives

namespace SemigroupBasis.CoRoots.Order6SporadicSection11

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107

private abbrev ListDerives :=
  S5_107.ListDerives basis

private def instantiateFiveWords
    (x y z h k : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | 3 => h
  | 4 => k
  | n + 5 => Word.singleton (n + 5)

private theorem basis_11_1a_empty :
    Derives basis
      (⟨0, [0, 0, 0]⟩ : Word Nat)
      (⟨0, [0, 0]⟩ : Word Nat) :=
  Derives.fromBasis (e := law_11_1a_empty) (by simp [basis])

private theorem basis_11_1a_H :
    Derives basis
      (⟨0, [0, 0, 3, 0]⟩ : Word Nat)
      (⟨0, [0, 3, 0]⟩ : Word Nat) :=
  Derives.fromBasis (e := law_11_1a_H) (by simp [basis])

private theorem basis_11_1b :
    Derives basis
      (⟨0, [1, 0, 2]⟩ : Word Nat)
      (⟨0, [0, 1, 2]⟩ : Word Nat) :=
  Derives.fromBasis (e := law_11_1b) (by simp [basis])

private theorem basis_11_1c_empty :
    Derives basis
      (⟨0, [1, 0, 1]⟩ : Word Nat)
      (⟨0, [1, 1, 0]⟩ : Word Nat) :=
  Derives.fromBasis (e := law_11_1c_empty) (by simp [basis])

private theorem basis_11_1c_H :
    Derives basis
      (⟨0, [3, 1, 0, 1]⟩ : Word Nat)
      (⟨0, [3, 1, 1, 0]⟩ : Word Nat) :=
  Derives.fromBasis (e := law_11_1c_H) (by simp [basis])

private theorem basis_11_1c_K :
    Derives basis
      (⟨0, [1, 4, 0, 1]⟩ : Word Nat)
      (⟨0, [1, 4, 1, 0]⟩ : Word Nat) :=
  Derives.fromBasis (e := law_11_1c_K) (by simp [basis])

private theorem basis_11_1c_HK :
    Derives basis
      (⟨0, [3, 1, 4, 0, 1]⟩ : Word Nat)
      (⟨0, [3, 1, 4, 1, 0]⟩ : Word Nat) :=
  Derives.fromBasis (e := law_11_1c_HK) (by simp [basis])

/-- Contract four consecutive copies of a nonempty block to three. -/
theorem derivesPowerContract (u : Word Nat) :
    Derives basis
      (((u ++ u) ++ u) ++ u)
      ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basis_11_1a_empty
      (instantiateFiveWords u u u u u)
  change Derives basis
    (((u ++ u) ++ u) ++ u)
    ((u ++ u) ++ u) at substituted
  exact substituted

/-- Contract a leading cube before a separated terminal copy. -/
theorem derivesSeparatedPowerContract (u middle : Word Nat) :
    Derives basis
      ((((u ++ u) ++ u) ++ middle) ++ u)
      (((u ++ u) ++ middle) ++ u) := by
  have substituted :=
    Derives.subst basis_11_1a_H
      (instantiateFiveWords u u u middle u)
  change Derives basis
    ((((u ++ u) ++ u) ++ middle) ++ u)
    (((u ++ u) ++ middle) ++ u) at substituted
  exact substituted

/-- Gather a repeated block with its first occurrence when a nonempty suffix
remains to its right. -/
theorem derivesGatherNonfinal (u middle after : Word Nat) :
    Derives basis
      (((u ++ middle) ++ u) ++ after)
      (((u ++ u) ++ middle) ++ after) := by
  have substituted :=
    Derives.subst basis_11_1b
      (instantiateFiveWords u middle after u u)
  change Derives basis
    (((u ++ middle) ++ u) ++ after)
    (((u ++ u) ++ middle) ++ after) at substituted
  exact substituted

theorem derivesTerminalSwitchEmpty (u terminal : Word Nat) :
    Derives basis
      (((u ++ terminal) ++ u) ++ terminal)
      (((u ++ terminal) ++ terminal) ++ u) := by
  have substituted :=
    Derives.subst basis_11_1c_empty
      (instantiateFiveWords u terminal u u u)
  change Derives basis
    (((u ++ terminal) ++ u) ++ terminal)
    (((u ++ terminal) ++ terminal) ++ u) at substituted
  exact substituted

theorem derivesTerminalSwitchLeft
    (u left terminal : Word Nat) :
    Derives basis
      ((((u ++ left) ++ terminal) ++ u) ++ terminal)
      ((((u ++ left) ++ terminal) ++ terminal) ++ u) := by
  have substituted :=
    Derives.subst basis_11_1c_H
      (instantiateFiveWords u terminal u left u)
  change Derives basis
    ((((u ++ left) ++ terminal) ++ u) ++ terminal)
    ((((u ++ left) ++ terminal) ++ terminal) ++ u) at substituted
  exact substituted

theorem derivesTerminalSwitchRight
    (u terminal right : Word Nat) :
    Derives basis
      ((((u ++ terminal) ++ right) ++ u) ++ terminal)
      ((((u ++ terminal) ++ right) ++ terminal) ++ u) := by
  have substituted :=
    Derives.subst basis_11_1c_K
      (instantiateFiveWords u terminal u u right)
  change Derives basis
    ((((u ++ terminal) ++ right) ++ u) ++ terminal)
    ((((u ++ terminal) ++ right) ++ terminal) ++ u) at substituted
  exact substituted

theorem derivesTerminalSwitchBoth
    (u left terminal right : Word Nat) :
    Derives basis
      (((((u ++ left) ++ terminal) ++ right) ++ u) ++ terminal)
      (((((u ++ left) ++ terminal) ++ right) ++ terminal) ++ u) := by
  have substituted :=
    Derives.subst basis_11_1c_HK
      (instantiateFiveWords u terminal u left right)
  change Derives basis
    (((((u ++ left) ++ terminal) ++ right) ++ u) ++ terminal)
    (((((u ++ left) ++ terminal) ++ right) ++ terminal) ++ u) at substituted
  exact substituted

/-- Contextual four-to-three contraction for a singleton letter. -/
theorem listDerivesPowerContract
    (pre suffix : List Nat) (x : Nat) :
    ListDerives
      (pre ++ [x, x, x, x] ++ suffix)
      (pre ++ [x, x, x] ++ suffix) := by
  have core :=
    S5_107.ListDerives.ofWord <|
      derivesPowerContract (Word.singleton x)
  simpa [List.append_assoc] using core.context pre suffix

/-- In a pseudo-compact segment the terminal copy contributes the third
retained occurrence, so a leading cube contracts to a square. -/
theorem listDerivesPseudoPowerContract
    (pre suffix : List Nat) (x : Nat) (middle : List Nat) :
    ListDerives
      (pre ++ [x, x, x] ++ middle ++ [x] ++ suffix)
      (pre ++ [x, x] ++ middle ++ [x] ++ suffix) := by
  cases middle with
  | nil =>
      simpa [List.append_assoc] using
        listDerivesPowerContract pre suffix x
  | cons middleHead middleTail =>
      have core :=
        S5_107.ListDerives.ofWord <|
          derivesSeparatedPowerContract
            (Word.singleton x)
            (S5_107.listWordOfCons middleHead middleTail)
      simpa [S5_107.listWordOfCons, List.append_assoc] using
        core.context pre suffix

/-- Gather two occurrences of `x` at the front of a segment whenever a
nonempty suffix follows the second occurrence. -/
theorem listDerivesGatherNonfinal
    (pre suffix : List Nat) (x : Nat)
    (middle after : List Nat) (afterNonempty : after ≠ []) :
    ListDerives
      (pre ++ [x] ++ middle ++ [x] ++ after ++ suffix)
      (pre ++ [x, x] ++ middle ++ after ++ suffix) := by
  cases middle with
  | nil =>
      simpa [List.append_assoc] using
        S5_107.ListDerives.refl
          (basis := basis) (pre ++ [x, x] ++ after ++ suffix)
  | cons middleHead middleTail =>
      obtain ⟨afterHead, afterTail, rfl⟩ :=
        List.exists_cons_of_ne_nil afterNonempty
      have core :=
        S5_107.ListDerives.ofWord <|
          derivesGatherNonfinal
            (Word.singleton x)
            (S5_107.listWordOfCons middleHead middleTail)
            (S5_107.listWordOfCons afterHead afterTail)
      simpa [S5_107.listWordOfCons, List.append_assoc] using
        core.context pre suffix

/-- The four displayed forms of (11.1c) give one terminal switch with
independently optional left and right contexts. -/
theorem listDerivesTerminalSwitch
    (pre suffix : List Nat) (x terminal : Nat)
    (left right : List Nat) :
    ListDerives
      (pre ++ [x] ++ left ++ [terminal] ++ right ++ [x, terminal] ++ suffix)
      (pre ++ [x] ++ left ++ [terminal] ++ right ++ [terminal, x] ++ suffix) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          have core :=
            S5_107.ListDerives.ofWord <|
              derivesTerminalSwitchEmpty
                (Word.singleton x) (Word.singleton terminal)
          simpa [List.append_assoc] using core.context pre suffix
      | cons rightHead rightTail =>
          have core :=
            S5_107.ListDerives.ofWord <|
              derivesTerminalSwitchRight
                (Word.singleton x) (Word.singleton terminal)
                (S5_107.listWordOfCons rightHead rightTail)
          simpa [S5_107.listWordOfCons, List.append_assoc] using
            core.context pre suffix
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          have core :=
            S5_107.ListDerives.ofWord <|
              derivesTerminalSwitchLeft
                (Word.singleton x)
                (S5_107.listWordOfCons leftHead leftTail)
                (Word.singleton terminal)
          simpa [S5_107.listWordOfCons, List.append_assoc] using
            core.context pre suffix
      | cons rightHead rightTail =>
          have core :=
            S5_107.ListDerives.ofWord <|
              derivesTerminalSwitchBoth
                (Word.singleton x)
                (S5_107.listWordOfCons leftHead leftTail)
                (Word.singleton terminal)
                (S5_107.listWordOfCons rightHead rightTail)
          simpa [S5_107.listWordOfCons, List.append_assoc] using
            core.context pre suffix

/-- Render capped first-occurrence blocks. Mismatched tails are discarded;
signatures coming from words always have aligned fields. -/
def renderCappedBlocks : List Nat → List Nat → List Nat
  | letter :: letters, count :: counts =>
      List.replicate count letter ++ renderCappedBlocks letters counts
  | _, _ => []

/-- The rightmost first-occurrence variable whose capped count is at least
two. This is the pseudo-compact terminal owner. -/
def greatestRepeated : List Nat → List Nat → Option Nat
  | letter :: letters, count :: counts =>
      match greatestRepeated letters counts with
      | some selected => some selected
      | none => if 2 ≤ count then some letter else none
  | _, _ => none

/-- Render the pseudo-compact prefix, leaving one copy of the selected owner
for the final position. -/
def renderPseudoBlocks
    (selected : Nat) : List Nat → List Nat → List Nat
  | letter :: letters, count :: counts =>
      List.replicate
          (if letter = selected then count - 1 else count) letter ++
        renderPseudoBlocks selected letters counts
  | _, _ => []

/-- Deterministic compact or pseudo-compact representative of a signature.
The compact case applies when the terminal is simple or the last
first-occurrence variable is repeated. -/
def canonicalListFromSignature (data : Signature) : List Nat :=
  let compact :=
    renderCappedBlocks data.firstOccurrences data.cappedCounts
  match data.terminal with
  | .simple _ => compact
  | .nonsimple =>
      if 2 ≤ data.cappedCounts.getLastD 0 then
        compact
      else
        match greatestRepeated data.firstOccurrences data.cappedCounts with
        | none => compact
        | some selected =>
            renderPseudoBlocks selected
                data.firstOccurrences data.cappedCounts ++
              [selected]

private def wordOfListD : List Nat → Word Nat
  | [] => Word.singleton 0
  | head :: tail => ⟨head, tail⟩

def canonicalWord (word : Word Nat) : Word Nat :=
  wordOfListD (canonicalListFromSignature (signature word))

theorem canonicalWord_eq_of_signature_eq
    {left right : Word Nat}
    (same : signature left = signature right) :
    canonicalWord left = canonicalWord right := by
  unfold canonicalWord
  rw [same]

/-- Once normalization to `canonicalWord` is proved, the remaining global
derivational-completeness structure follows without any target-specific
argument. -/
theorem signatureDerivationCompleteness_of_normalizes
    (normalizes :
      ∀ word : Word Nat, Derives basis word (canonicalWord word)) :
    SignatureDerivationCompleteness where
  derives := by
    intro left right same
    have leftNormal := normalizes left
    have rightNormal := normalizes right
    rw [canonicalWord_eq_of_signature_eq same] at leftNormal
    exact leftNormal.trans rightNormal.symm

end SemigroupBasis.CoRoots.Order6SporadicSection11

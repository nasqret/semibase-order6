import SemigroupBasis.CoRoots.Order6SporadicSection11Normalization
import SemigroupBasis.Examples.FinalMarkerThree

namespace SemigroupBasis.CoRoots.Order6SporadicSection11

open SemigroupBasis
open SemigroupBasis.Examples

inductive OrdinaryGatherState where
  | one
  | two
  | three
deriving DecidableEq, Repr

namespace OrdinaryGatherState

def exponent : OrdinaryGatherState → Nat
  | .one => 1
  | .two => 2
  | .three => 3

def next : OrdinaryGatherState → OrdinaryGatherState
  | .one => .two
  | .two => .three
  | .three => .three

def advance : OrdinaryGatherState → Nat → OrdinaryGatherState
  | state, 0 => state
  | state, count + 1 => advance state.next count

theorem advance_exponent
    (state : OrdinaryGatherState) (count : Nat) :
    (state.advance count).exponent =
      Nat.min 3 (state.exponent + count) := by
  induction count generalizing state with
  | zero =>
      cases state <;> decide
  | succ count induction =>
      rw [advance, induction]
      cases state with
      | one =>
          simp only [next, exponent]
          apply congrArg (Nat.min 3)
          omega
      | two =>
          simp only [next, exponent]
          apply congrArg (Nat.min 3)
          omega
      | three =>
          simp only [next, exponent]
          calc
            Nat.min 3 (3 + count) = 3 :=
              Nat.min_eq_left (by omega)
            _ = Nat.min 3 (3 + (count + 1)) :=
              (Nat.min_eq_left (by omega)).symm

end OrdinaryGatherState

inductive TerminalGatherState where
  | one
  | two
deriving DecidableEq, Repr

namespace TerminalGatherState

def exponent : TerminalGatherState → Nat
  | .one => 1
  | .two => 2

def next : TerminalGatherState → TerminalGatherState
  | .one => .two
  | .two => .two

def advance : TerminalGatherState → Nat → TerminalGatherState
  | state, 0 => state
  | state, count + 1 => advance state.next count

theorem advance_exponent
    (state : TerminalGatherState) (count : Nat) :
    (state.advance count).exponent =
      Nat.min 2 (state.exponent + count) := by
  induction count generalizing state with
  | zero =>
      cases state <;> decide
  | succ count induction =>
      rw [advance, induction]
      cases state with
      | one =>
          simp only [next, exponent]
          apply congrArg (Nat.min 2)
          omega
      | two =>
          simp only [next, exponent]
          calc
            Nat.min 2 (2 + count) = 2 :=
              Nat.min_eq_left (by omega)
            _ = Nat.min 2 (2 + (count + 1)) :=
              (Nat.min_eq_left (by omega)).symm

end TerminalGatherState

private def ordinaryGatherList
    (state : OrdinaryGatherState)
    (selected : Nat) (middle rest : List Nat) (final : Nat) : List Nat :=
  List.replicate state.exponent selected ++ middle ++ rest ++ [final]

private theorem listDerivesOrdinaryGather :
    ∀ (state : OrdinaryGatherState)
        (selected : Nat) (middle rest : List Nat) (final : Nat),
      selected ≠ final →
      S5_107.ListDerives basis
        (ordinaryGatherList state selected middle rest final)
        (ordinaryGatherList
          (state.advance (rest.count selected)) selected middle
          (rest.filter (fun letter => decide (letter ≠ selected)))
          final)
  | state, selected, middle, [], final, _ => by
      simp [ordinaryGatherList, OrdinaryGatherState.advance]
      exact S5_107.ListDerives.refl _
  | state, selected, middle, letter :: rest, final, different => by
      by_cases equal : letter = selected
      · subst letter
        cases state with
        | one =>
            have first :=
              listDerivesGatherNonfinal
                [] [] selected middle (rest ++ [final]) (by simp)
            have remaining :=
              listDerivesOrdinaryGather
                .two selected middle rest final different
            have first' :
                S5_107.ListDerives basis
                  (ordinaryGatherList
                    .one selected middle (selected :: rest) final)
                  (ordinaryGatherList
                    .two selected middle rest final) := by
              simpa [ordinaryGatherList, List.append_assoc] using first
            simpa [ordinaryGatherList, OrdinaryGatherState.advance,
              List.append_assoc] using first'.trans remaining
        | two =>
            have first :=
              listDerivesGatherNonfinal
                [selected] [] selected middle
                (rest ++ [final]) (by simp)
            have remaining :=
              listDerivesOrdinaryGather
                .three selected middle rest final different
            have first' :
                S5_107.ListDerives basis
                  (ordinaryGatherList
                    .two selected middle (selected :: rest) final)
                  (ordinaryGatherList
                    .three selected middle rest final) := by
              simpa [ordinaryGatherList, List.append_assoc] using first
            simpa [ordinaryGatherList, OrdinaryGatherState.advance,
              List.append_assoc] using first'.trans remaining
        | three =>
            have gathered :=
              listDerivesGatherNonfinal
                [selected, selected] [] selected middle
                (rest ++ [final]) (by simp)
            have contracted :=
              listDerivesPowerContract
                [] (middle ++ rest ++ [final]) selected
            have remaining :=
              listDerivesOrdinaryGather
                .three selected middle rest final different
            have gathered' :
                S5_107.ListDerives basis
                  (ordinaryGatherList
                    .three selected middle (selected :: rest) final)
                  ([selected, selected, selected, selected] ++
                    middle ++ rest ++ [final]) := by
              simpa [ordinaryGatherList, List.append_assoc] using gathered
            have contracted' :
                S5_107.ListDerives basis
                  ([selected, selected, selected, selected] ++
                    middle ++ rest ++ [final])
                  (ordinaryGatherList
                    .three selected middle rest final) := by
              simpa [ordinaryGatherList, List.append_assoc] using contracted
            simpa [ordinaryGatherList, OrdinaryGatherState.advance,
              List.append_assoc] using
                gathered'.trans (contracted'.trans remaining)
      · have remaining :=
          listDerivesOrdinaryGather
            state selected (middle ++ [letter]) rest final different
        simpa [ordinaryGatherList, equal,
          List.count_cons_of_ne equal, List.append_assoc] using remaining

private def terminalGatherList
    (state : TerminalGatherState)
    (selected : Nat) (middle rest : List Nat) : List Nat :=
  List.replicate state.exponent selected ++ middle ++ rest ++ [selected]

private theorem listDerivesTerminalGather :
    ∀ (state : TerminalGatherState)
        (selected : Nat) (middle rest : List Nat),
      S5_107.ListDerives basis
        (terminalGatherList state selected middle rest)
        (terminalGatherList
          (state.advance (rest.count selected)) selected middle
          (rest.filter (fun letter => decide (letter ≠ selected))))
  | state, selected, middle, [] => by
      simp [terminalGatherList, TerminalGatherState.advance]
      exact S5_107.ListDerives.refl _
  | state, selected, middle, letter :: rest => by
      by_cases equal : letter = selected
      · subst letter
        cases state with
        | one =>
            have first :=
              listDerivesGatherNonfinal
                [] [] selected middle (rest ++ [selected]) (by simp)
            have remaining :=
              listDerivesTerminalGather .two selected middle rest
            have first' :
                S5_107.ListDerives basis
                  (terminalGatherList
                    .one selected middle (selected :: rest))
                  (terminalGatherList .two selected middle rest) := by
              simpa [terminalGatherList, List.append_assoc] using first
            simpa [terminalGatherList, TerminalGatherState.advance,
              List.append_assoc] using first'.trans remaining
        | two =>
            have gathered :=
              listDerivesGatherNonfinal
                [selected] [] selected middle
                (rest ++ [selected]) (by simp)
            have contracted :=
              listDerivesPseudoPowerContract
                [] [] selected (middle ++ rest)
            have remaining :=
              listDerivesTerminalGather .two selected middle rest
            have gathered' :
                S5_107.ListDerives basis
                  (terminalGatherList
                    .two selected middle (selected :: rest))
                  ([selected, selected, selected] ++
                    middle ++ rest ++ [selected]) := by
              simpa [terminalGatherList, List.append_assoc] using gathered
            have contracted' :
                S5_107.ListDerives basis
                  ([selected, selected, selected] ++
                    middle ++ rest ++ [selected])
                  (terminalGatherList .two selected middle rest) := by
              simpa [terminalGatherList, List.append_assoc] using contracted
            simpa [terminalGatherList, TerminalGatherState.advance,
              List.append_assoc] using
                gathered'.trans (contracted'.trans remaining)
      · have remaining :=
          listDerivesTerminalGather
            state selected (middle ++ [letter]) rest
        simpa [terminalGatherList, equal,
          List.count_cons_of_ne equal, List.append_assoc] using remaining

def prefixExponent
    (final letter : Nat) (count : Nat) : Nat :=
  if letter = final then Nat.min count 2 else Nat.min count 3

/-- Normalize a prefix into capped first-occurrence blocks while reserving the
separate final letter. -/
def gatheredPrefix (final : Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      let normalized := gatheredPrefix final rest
      List.replicate
          (prefixExponent final letter (normalized.count letter + 1))
          letter ++
        normalized.filter (fun value => decide (value ≠ letter))

theorem listDerivesGatheredPrefix :
    ∀ (stem : List Nat) (final : Nat),
      S5_107.ListDerives basis
        (stem ++ [final])
        (gatheredPrefix final stem ++ [final])
  | [], final => by
      simpa [gatheredPrefix] using
        S5_107.ListDerives.refl (basis := basis) [final]
  | letter :: rest, final => by
      have suffixNormal := listDerivesGatheredPrefix rest final
      have prefixed := suffixNormal.prepend [letter]
      let normalized := gatheredPrefix final rest
      by_cases terminalOwner : letter = final
      · subst final
        have gathered :=
          listDerivesTerminalGather .one letter [] normalized
        have exponent :=
          TerminalGatherState.advance_exponent
            .one (normalized.count letter)
        have exponent' :
            (TerminalGatherState.advance
              .one (normalized.count letter)).exponent =
              Nat.min 2 (1 + normalized.count letter) := by
          simpa only [TerminalGatherState.exponent] using exponent
        have combined := prefixed.trans gathered
        simpa [gatheredPrefix, normalized, prefixExponent,
          terminalGatherList, exponent', Nat.add_comm, Nat.min_comm,
          List.append_assoc] using combined
      · have gathered :=
          listDerivesOrdinaryGather
            .one letter [] normalized final terminalOwner
        have exponent :=
          OrdinaryGatherState.advance_exponent
            .one (normalized.count letter)
        have exponent' :
            (OrdinaryGatherState.advance
              .one (normalized.count letter)).exponent =
              Nat.min 3 (1 + normalized.count letter) := by
          simpa only [OrdinaryGatherState.exponent] using exponent
        have combined := prefixed.trans gathered
        simpa [gatheredPrefix, normalized, prefixExponent, terminalOwner,
          ordinaryGatherList, exponent', Nat.add_comm, Nat.min_comm,
          List.append_assoc] using combined

def gatheredWord (word : Word Nat) : Word Nat :=
  let split := splitPrefixFinal word
  wordOfPrefixFinal (gatheredPrefix split.2 split.1) split.2

/-- First unrestricted normalization stage: every word derives to capped
first-occurrence blocks with its literal final occurrence protected. -/
theorem derivesGatheredWord (word : Word Nat) :
    Derives basis word (gatheredWord word) := by
  let split := splitPrefixFinal word
  have listDerivation := listDerivesGatheredPrefix split.1 split.2
  have sourceWord : wordOfPrefixFinal split.1 split.2 = word :=
    wordOfPrefixFinal_split word
  have sourceList : split.1 ++ [split.2] = word.toList := by
    rw [← toList_wordOfPrefixFinal, sourceWord]
  have targetList :
      gatheredPrefix split.2 split.1 ++ [split.2] =
        (gatheredWord word).toList := by
    simp [gatheredWord, split, toList_wordOfPrefixFinal]
  rw [sourceList, targetList] at listDerivation
  cases word with
  | mk sourceHead sourceTail =>
      cases targetEquation : gatheredWord (Word.mk sourceHead sourceTail) with
      | mk targetHead targetTail =>
          apply S5_107.ListDerives.toWord
          simpa [targetEquation] using listDerivation

end SemigroupBasis.CoRoots.Order6SporadicSection11

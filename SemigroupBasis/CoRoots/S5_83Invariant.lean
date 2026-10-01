import SemigroupBasis.CoRoots.S5_83
import SemigroupBasis.Examples.FinalMarkerThree

namespace SemigroupBasis.CoRoots.S5_83

open SemigroupBasis
open SemigroupBasis.Examples

/-- A word is either a singleton or has an explicit stem followed by its
penultimate and final variables. -/
inductive TerminalSplit where
  | singleton (final : Nat)
  | pair (stem : List Nat) (penultimate final : Nat)
deriving Repr, DecidableEq

namespace TerminalSplit

def renderList : TerminalSplit → List Nat
  | singleton final => [final]
  | pair stem penultimate final =>
      stem ++ [penultimate, final]

def renderWord : TerminalSplit → Word Nat
  | singleton final => Word.singleton final
  | pair stem penultimate final =>
      wordOfPrefixFinal (stem ++ [penultimate]) final

@[simp]
theorem toList_renderWord (split : TerminalSplit) :
    split.renderWord.toList = split.renderList := by
  cases split with
  | singleton final =>
      rfl
  | pair stem penultimate final =>
      simp [renderWord, renderList, toList_wordOfPrefixFinal,
        List.append_assoc]

end TerminalSplit

private def terminalSplitAux (head : Nat) :
    List Nat → TerminalSplit
  | [] => .singleton head
  | next :: rest =>
      match terminalSplitAux next rest with
      | .singleton final => .pair [] head final
      | .pair stem penultimate final =>
          .pair (head :: stem) penultimate final

def terminalSplit (word : Word Nat) : TerminalSplit :=
  terminalSplitAux word.head word.tail

private theorem terminalSplitAux_renderList
    (head : Nat) (tail : List Nat) :
    (terminalSplitAux head tail).renderList = head :: tail := by
  induction tail generalizing head with
  | nil =>
      rfl
  | cons next rest ih =>
      rw [terminalSplitAux]
      cases splitEq : terminalSplitAux next rest with
      | singleton final =>
          have rendered := ih next
          rw [splitEq] at rendered
          simpa [TerminalSplit.renderList] using
            congrArg (List.cons head) rendered
      | pair stem penultimate final =>
          have rendered := ih next
          rw [splitEq] at rendered
          simpa [TerminalSplit.renderList, List.append_assoc] using
            congrArg (List.cons head) rendered

theorem terminalSplit_renderList (word : Word Nat) :
    (terminalSplit word).renderList = word.toList := by
  cases word with
  | mk head tail =>
      exact terminalSplitAux_renderList head tail

theorem terminalSplit_renderWord (word : Word Nat) :
    (terminalSplit word).renderWord = word := by
  apply Word.toList_injective
  rw [TerminalSplit.toList_renderWord, terminalSplit_renderList]

/-- Rendering and then splitting an explicit terminal decomposition recovers
the decomposition.  This is the converse of `terminalSplit_renderWord` and is
useful when a word has already been put into an explicit final-pair form. -/
theorem terminalSplit_renderWord_inverse (split : TerminalSplit) :
    terminalSplit split.renderWord = split := by
  cases split with
  | singleton final =>
      rfl
  | pair stem penultimate final =>
      induction stem with
      | nil =>
          rfl
      | cons head tail induction =>
          let rest :=
            wordOfPrefixFinal (tail ++ [penultimate]) final
          change
            (match terminalSplit rest with
            | .singleton restFinal =>
                TerminalSplit.pair [] head restFinal
            | .pair restStem restPenultimate restFinal =>
                TerminalSplit.pair
                  (head :: restStem) restPenultimate restFinal) =
              TerminalSplit.pair (head :: tail) penultimate final
          have restSplit :
              terminalSplit rest =
                .pair tail penultimate final := by
            simpa [rest, TerminalSplit.renderWord] using induction
          rw [restSplit]

/-- Support equality, without multiplicity. -/
def SameSupport (left right : Word Nat) : Prop :=
  ∀ z, z ∈ left.toList ↔ z ∈ right.toList

/-- The one-letter stratum. -/
def IsSingletonWord (word : Word Nat) : Prop :=
  match terminalSplit word with
  | .singleton _ => True
  | .pair _ _ _ => False

/-- A globally unique final variable. -/
def UniqueFinal (word : Word Nat) (z : Nat) : Prop :=
  match terminalSplit word with
  | .singleton final => final = z
  | .pair stem penultimate final =>
      final = z ∧ final ≠ penultimate ∧ final ∉ stem

/-- A globally unique penultimate variable followed by a globally unique
final variable. -/
def UniqueTerminalPair (word : Word Nat) (p t : Nat) : Prop :=
  match terminalSplit word with
  | .singleton _ => False
  | .pair stem penultimate final =>
      penultimate = p ∧ final = t ∧
        p ∉ stem ∧ t ≠ p ∧ t ∉ stem

theorem uniqueTerminalPair_penultimate_mem
    {word : Word Nat} {p t : Nat}
    (pair : UniqueTerminalPair word p t) :
    p ∈ word.toList := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      simp [UniqueTerminalPair, splitEq] at pair
  | pair stem penultimate final =>
      have pairParts :
          penultimate = p ∧ final = t ∧
            p ∉ stem ∧ t ≠ p ∧ t ∉ stem := by
        simpa [UniqueTerminalPair, splitEq] using pair
      have penultimateEq : penultimate = p := by
        exact pairParts.1
      rw [← terminalSplit_renderList word, splitEq]
      simp [TerminalSplit.renderList, penultimateEq]

/-- The longest globally unique terminal suffix, capped at length two. -/
def terminalUniqueSuffix (word : Word Nat) : List Nat :=
  match terminalSplit word with
  | .singleton final => [final]
  | .pair stem penultimate final =>
      if final = penultimate ∨ final ∈ stem then
        []
      else if penultimate ∈ stem then
        [final]
      else
        [penultimate, final]

/-- Componentwise presentation of the exact support plus capped
terminal-unique-suffix invariant. -/
structure SameTerminalUniqueSuffixSignature
    (left right : Word Nat) : Prop where
  support : SameSupport left right
  singleton :
    IsSingletonWord left ↔ IsSingletonWord right
  uniqueFinal :
    ∀ z, UniqueFinal left z ↔ UniqueFinal right z
  uniqueTerminalPair :
    ∀ p t,
      UniqueTerminalPair left p t ↔
        UniqueTerminalPair right p t

namespace SameTerminalUniqueSuffixSignature

theorem symm {left right : Word Nat}
    (same : SameTerminalUniqueSuffixSignature left right) :
    SameTerminalUniqueSuffixSignature right left :=
  ⟨fun z => (same.support z).symm,
    same.singleton.symm,
    fun z => (same.uniqueFinal z).symm,
    fun p t => (same.uniqueTerminalPair p t).symm⟩

/-- The componentwise fields recover the literal capped suffix. -/
theorem terminalUniqueSuffix_eq {left right : Word Nat}
    (same : SameTerminalUniqueSuffixSignature left right) :
    terminalUniqueSuffix left = terminalUniqueSuffix right := by
  classical
  cases leftSplitEq : terminalSplit left with
  | singleton leftFinal =>
      cases rightSplitEq : terminalSplit right with
      | singleton rightFinal =>
          have rightUnique :
              UniqueFinal right leftFinal :=
            (same.uniqueFinal leftFinal).mp <| by
              simp [UniqueFinal, leftSplitEq]
          have finals : rightFinal = leftFinal := by
            simpa [UniqueFinal, rightSplitEq] using rightUnique
          subst rightFinal
          simp [terminalUniqueSuffix, leftSplitEq, rightSplitEq]
      | pair rightPrefix rightPenultimate rightFinal =>
          have leftSingleton : IsSingletonWord left := by
            simp [IsSingletonWord, leftSplitEq]
          have rightSingleton := same.singleton.mp leftSingleton
          simp [IsSingletonWord, rightSplitEq] at rightSingleton
  | pair leftPrefix leftPenultimate leftFinal =>
      cases rightSplitEq : terminalSplit right with
      | singleton rightFinal =>
          have rightSingleton : IsSingletonWord right := by
            simp [IsSingletonWord, rightSplitEq]
          have leftSingleton := same.singleton.mpr rightSingleton
          simp [IsSingletonWord, leftSplitEq] at leftSingleton
      | pair rightPrefix rightPenultimate rightFinal =>
          by_cases leftRepeated :
              leftFinal = leftPenultimate ∨
                leftFinal ∈ leftPrefix
          · have rightRepeated :
                rightFinal = rightPenultimate ∨
                  rightFinal ∈ rightPrefix := by
              apply Decidable.byContradiction
              intro rightNotRepeated
              have rightParts := not_or.mp rightNotRepeated
              have rightUnique :
                  UniqueFinal right rightFinal := by
                simp [UniqueFinal, rightSplitEq,
                  rightParts.1, rightParts.2]
              have leftUnique :=
                (same.uniqueFinal rightFinal).mpr rightUnique
              have leftParts :
                  leftFinal = rightFinal ∧
                    leftFinal ≠ leftPenultimate ∧
                    leftFinal ∉ leftPrefix := by
                simpa [UniqueFinal, leftSplitEq] using leftUnique
              rcases leftRepeated with equal | member
              · exact leftParts.2.1 equal
              · exact leftParts.2.2 member
            simp [terminalUniqueSuffix, leftSplitEq, rightSplitEq,
              leftRepeated, rightRepeated]
          · have leftParts := not_or.mp leftRepeated
            have leftUnique :
                UniqueFinal left leftFinal := by
              simp [UniqueFinal, leftSplitEq,
                leftParts.1, leftParts.2]
            have rightUnique :=
              (same.uniqueFinal leftFinal).mp leftUnique
            have rightParts :
                rightFinal = leftFinal ∧
                  rightFinal ≠ rightPenultimate ∧
                  rightFinal ∉ rightPrefix := by
              simpa [UniqueFinal, rightSplitEq] using rightUnique
            have rightFinalEq : rightFinal = leftFinal := rightParts.1
            subst rightFinal
            by_cases leftPenultimateRepeated :
                leftPenultimate ∈ leftPrefix
            · have rightPenultimateRepeated :
                  rightPenultimate ∈ rightPrefix := by
                apply Decidable.byContradiction
                intro rightPenultimateUnique
                have rightPair :
                    UniqueTerminalPair right
                      rightPenultimate leftFinal := by
                  simp [UniqueTerminalPair, rightSplitEq,
                    rightPenultimateUnique, rightParts.2.1,
                    rightParts.2.2]
                have leftPair :=
                  (same.uniqueTerminalPair
                    rightPenultimate leftFinal).mpr rightPair
                have leftPairParts :
                    leftPenultimate = rightPenultimate ∧
                      leftFinal = leftFinal ∧
                      rightPenultimate ∉ leftPrefix ∧
                      leftFinal ≠ rightPenultimate ∧
                      leftFinal ∉ leftPrefix := by
                  simpa [UniqueTerminalPair, leftSplitEq] using leftPair
                exact leftPairParts.2.2.1 <| by
                  simpa [leftPairParts.1] using leftPenultimateRepeated
              simp [terminalUniqueSuffix, leftSplitEq, rightSplitEq,
                leftRepeated, rightParts.2.1, rightParts.2.2,
                leftPenultimateRepeated, rightPenultimateRepeated]
            · have leftPair :
                  UniqueTerminalPair left
                    leftPenultimate leftFinal := by
                simp [UniqueTerminalPair, leftSplitEq,
                  leftPenultimateRepeated, leftParts.1, leftParts.2]
              have rightPair :=
                (same.uniqueTerminalPair
                  leftPenultimate leftFinal).mp leftPair
              have rightPairParts :
                  rightPenultimate = leftPenultimate ∧
                    leftFinal = leftFinal ∧
                    leftPenultimate ∉ rightPrefix ∧
                    leftFinal ≠ leftPenultimate ∧
                    leftFinal ∉ rightPrefix := by
                simpa [UniqueTerminalPair, rightSplitEq] using rightPair
              have rightPenultimateEq :
                  rightPenultimate = leftPenultimate := rightPairParts.1
              subst rightPenultimate
              simp [terminalUniqueSuffix, leftSplitEq, rightSplitEq,
                leftParts.1, leftParts.2,
                rightParts.2.2,
                leftPenultimateRepeated, rightPairParts.2.2.1]

end SameTerminalUniqueSuffixSignature

end SemigroupBasis.CoRoots.S5_83

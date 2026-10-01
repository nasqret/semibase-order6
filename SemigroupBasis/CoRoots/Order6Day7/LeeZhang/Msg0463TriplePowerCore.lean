import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463TripleOccurrenceSplit

/-! A table-independent three-law power-absorption engine. Every word with
three occurrences of a letter derives to itself followed by a pair of that
letter. The proof includes all empty-gap cases; no table or completeness
assumption is present. A target basis must actually derive these three laws
before this engine can be transported into its derivation theory. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.TriplePowerCore

open SemigroupBasis

def cubeLaw : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0, 0]⟩⟩
def centralLaw : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨1, [0, 0]⟩⟩
def separatedLaw : Identity Nat := ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 0, 2, 0, 0, 0]⟩⟩
def basis : List (Identity Nat) := [cubeLaw, centralLaw, separatedLaw]

private abbrev ListDerives : List Nat → List Nat → Prop := S5_107.ListDerives basis

theorem derivesPrefixRotationSubstitution (substitution : Nat → Word Nat) :
    Derives basis (centralLaw.lhs.bind substitution) (centralLaw.rhs.bind substitution) :=
  Derives.subst (Derives.fromBasis (by decide)) substitution

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

private def instantiateThreeWords (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

theorem listDerivesTripleExpansion (letter : Nat) :
    ListDerives [letter, letter, letter] [letter, letter, letter, letter, letter] := by
  have original : Derives basis cubeLaw.lhs cubeLaw.rhs :=
    Derives.fromBasis (by decide)
  have substituted := original.subst (fun _ => Word.singleton letter)
  exact S5_107.ListDerives.words substituted

/-- Three displayed occurrences support pair insertion even when either
internal gap is empty. No empty word is ever substituted into a law. -/
theorem listDerivesExpandTripleInterval (letter : Nat) (firstGap secondGap : List Nat) :
    ListDerives
      ([letter] ++ firstGap ++ [letter] ++ secondGap ++ [letter])
      ([letter] ++ firstGap ++ [letter] ++ secondGap ++ [letter, letter, letter]) := by
  cases firstGap with
  | nil =>
      have first : ListDerives
          ([letter, letter] ++ secondGap ++ [letter])
          (secondGap ++ [letter, letter, letter]) := by
        simpa [List.append_assoc] using (listDerivesPairAcross letter secondGap).append [letter]
      have expanded := (listDerivesTripleExpansion letter).prepend secondGap
      have last : ListDerives
          (secondGap ++ [letter, letter, letter, letter, letter])
          ([letter, letter] ++ secondGap ++ [letter, letter, letter]) := by
        simpa [List.append_assoc] using
          ((listDerivesPairAcross letter secondGap).append [letter, letter, letter]).symm
      simpa [List.append_assoc] using first.trans (expanded.trans last)
  | cons firstHead firstTail =>
      cases secondGap with
      | nil =>
          have first : ListDerives
              ([letter] ++ (firstHead :: firstTail) ++ [letter, letter])
              ([letter, letter, letter] ++ (firstHead :: firstTail)) := by
            simpa [List.append_assoc] using
              ((listDerivesPairAcross letter (firstHead :: firstTail)).prepend [letter]).symm
          have expanded := (listDerivesTripleExpansion letter).append (firstHead :: firstTail)
          have last : ListDerives
              ([letter, letter, letter, letter, letter] ++ (firstHead :: firstTail))
              ([letter] ++ (firstHead :: firstTail) ++ [letter, letter, letter, letter]) := by
            simpa [List.append_assoc] using
              (listDerivesBlockSquareAcross [letter, letter] (firstHead :: firstTail)).prepend [letter]
          simpa [List.append_assoc] using first.trans (expanded.trans last)
      | cons secondHead secondTail =>
          have original : Derives basis separatedLaw.lhs separatedLaw.rhs :=
            Derives.fromBasis (by decide)
          have substituted := original.subst
            (instantiateThreeWords (Word.singleton letter)
              (S5_107.listWordOfCons firstHead firstTail)
              (S5_107.listWordOfCons secondHead secondTail))
          have atList := S5_107.ListDerives.ofWord substituted
          simp only [Word.toList_bind] at atList
          simpa [separatedLaw, instantiateThreeWords,
            S5_107.listWordOfCons, Word.toList, Word.singleton,
            List.append_assoc] using atList

/-- Append a central pair after any word with at least three occurrences.
The displayed three occurrences may be arbitrarily far apart. -/
theorem listDerivesAppendPairOfCountGeThree (letters : List Nat) (letter : Nat)
    (triple : 3 ≤ letters.count letter) :
    ListDerives letters (letters ++ [letter, letter]) := by
  obtain ⟨before, firstGap, secondGap, after, shape⟩ :=
    Msg0463NilZ2.exists_three_occurrence_split letter triple
  let interval := [letter] ++ firstGap ++ [letter] ++ secondGap ++ [letter]
  have intervalStep : ListDerives interval (interval ++ [letter, letter]) := by
    simpa [interval, List.append_assoc] using
      listDerivesExpandTripleInterval letter firstGap secondGap
  have expanded : ListDerives
      (before ++ interval ++ after)
      (before ++ interval ++ [letter, letter] ++ after) := by
    simpa [List.append_assoc] using intervalStep.context before after
  have moved := listDerivesPairAcrossContext (before ++ interval) letter after []
  have normalized : ListDerives
      (before ++ interval ++ after)
      ((before ++ interval ++ after) ++ [letter, letter]) :=
    expanded.trans (by simpa [List.append_assoc] using moved)
  simpa [interval, shape, List.append_assoc] using normalized

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.TriplePowerCore

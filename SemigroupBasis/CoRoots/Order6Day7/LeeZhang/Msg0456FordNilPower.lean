import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456FordNilBasis
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463TripleOccurrenceSplit

/-! Pair movement with an actual earlier occurrence, and unrestricted pair
insertion after two occurrences. Empty contexts are list contexts, never
empty images of a semigroup substitution. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

open SemigroupBasis

private abbrev LD := S5_107.ListDerives basis

private def threeWords (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

theorem listDerivesOldLaw (identity : Identity Nat)
    (member : identity ∈ Msg0446NilZ2.Ford.basis) (substitution : Nat → Word Nat) :
    LD (identity.lhs.toList.flatMap (fun letter => (substitution letter).toList))
      (identity.rhs.toList.flatMap (fun letter => (substitution letter).toList)) := by
  have derivation := Derives.subst
    (Derives.fromBasis (e := identity) (old_basis_subset identity member)) substitution
  simpa only [Word.toList_bind] using S5_107.ListDerives.ofWord derivation

/-- An adjacent pair may cross arbitrary words only after an earlier copy
of its own letter. The first copy never moves. -/
theorem listDerivesAnchoredPair (letter : Nat) (between payload : List Nat) :
    LD ([letter] ++ between ++ [letter, letter] ++ payload)
      ([letter] ++ between ++ payload ++ [letter, letter]) := by
  cases payload with
  | nil =>
      simpa using S5_107.ListDerives.refl (basis := basis)
        ([letter] ++ between ++ [letter, letter])
  | cons payloadHead payloadTail =>
      cases between with
      | nil =>
          have moved := listDerivesOldLaw Msg0446NilZ2.Ford.law18 (by decide)
            (threeWords (Word.singleton letter)
              (S5_107.listWordOfCons payloadHead payloadTail) (Word.singleton letter))
          simpa [Msg0446NilZ2.Ford.law18, threeWords, Word.toList, Word.singleton,
            S5_107.listWordOfCons, List.append_assoc] using moved
      | cons betweenHead betweenTail =>
          let substitution := threeWords (Word.singleton letter)
            (S5_107.listWordOfCons betweenHead betweenTail)
            (S5_107.listWordOfCons payloadHead payloadTail)
          have first := (listDerivesOldLaw Msg0446NilZ2.Ford.law07 (by decide) substitution).symm
          have second := listDerivesOldLaw Msg0446NilZ2.Ford.law08 (by decide) substitution
          have firstAligned :
              LD ([letter] ++ (betweenHead :: betweenTail) ++ [letter, letter] ++
                    (payloadHead :: payloadTail))
                ([letter, letter, letter] ++ (betweenHead :: betweenTail) ++
                    (payloadHead :: payloadTail)) := by
            simpa [Msg0446NilZ2.Ford.law07, substitution, threeWords, Word.toList,
              Word.singleton, S5_107.listWordOfCons, List.append_assoc] using first
          have secondAligned :
              LD ([letter, letter, letter] ++ (betweenHead :: betweenTail) ++
                    (payloadHead :: payloadTail))
                ([letter] ++ (betweenHead :: betweenTail) ++ (payloadHead :: payloadTail) ++
                    [letter, letter]) := by
            simpa [Msg0446NilZ2.Ford.law08, substitution, threeWords, Word.toList,
              Word.singleton, S5_107.listWordOfCons, List.append_assoc] using second
          exact firstAligned.trans secondAligned

theorem listDerivesPairAcrossSeen (prefixWords payload : List Nat) (letter : Nat)
    (seen : letter ∈ prefixWords) :
    LD (prefixWords ++ [letter, letter] ++ payload)
      (prefixWords ++ payload ++ [letter, letter]) := by
  obtain ⟨before, between, shape⟩ := List.append_of_mem seen
  rw [shape]
  simpa [List.append_assoc] using (listDerivesAnchoredPair letter between payload).context before []

theorem listDerivesPairAcrossSeenContext (prefixWords payload suffix : List Nat) (letter : Nat)
    (seen : letter ∈ prefixWords) :
    LD (prefixWords ++ [letter, letter] ++ payload ++ suffix)
      (prefixWords ++ payload ++ [letter, letter] ++ suffix) := by
  simpa [List.append_assoc] using (listDerivesPairAcrossSeen prefixWords payload letter seen).append suffix

theorem listDerivesExpandTwoOccurrenceInterval (letter : Nat) (between : List Nat) :
    LD ([letter] ++ between ++ [letter])
      ([letter] ++ between ++ [letter, letter, letter]) := by
  cases between with
  | nil =>
      have expanded := listDerivesOldLaw Msg0446NilZ2.Ford.law00 (by decide)
        (fun _ => Word.singleton letter)
      simpa [Msg0446NilZ2.Ford.law00, Word.toList, Word.singleton] using expanded
  | cons head tail =>
      have expanded := listDerivesOldLaw Msg0446NilZ2.Ford.law03 (by decide)
        (threeWords (Word.singleton letter) (S5_107.listWordOfCons head tail) (Word.singleton letter))
      simpa [Msg0446NilZ2.Ford.law03, threeWords, Word.toList, Word.singleton,
        S5_107.listWordOfCons, List.append_assoc] using expanded

/-- Two occurrences anywhere suffice; the inserted pair is moved through
the entire suffix by the proved, genuinely anchored transport. -/
theorem listDerivesAppendPairOfCountGeTwo (letters : List Nat) (letter : Nat)
    (repeated : 2 ≤ letters.count letter) :
    LD letters (letters ++ [letter, letter]) := by
  obtain ⟨before, between, after, shape⟩ :=
    Msg0463NilZ2.exists_two_occurrence_split letter repeated
  let stem := before ++ [letter] ++ between ++ [letter]
  have seen : letter ∈ stem := by simp [stem]
  have expanded : LD letters (stem ++ [letter, letter] ++ after) := by
    simpa [shape, stem, List.append_assoc] using
      (listDerivesExpandTwoOccurrenceInterval letter between).context before after
  have moved := listDerivesPairAcrossSeen stem after letter seen
  apply expanded.trans
  simpa [shape, stem, List.append_assoc] using moved

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

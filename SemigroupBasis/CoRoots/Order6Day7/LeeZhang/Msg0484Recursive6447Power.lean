import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0484SimpleCapTwo
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0468RecursivePower

/-! Actual B12 expansion and deletion across arbitrary, independently empty
gaps. The proof uses the displayed power and sandwich laws; no new finite
lemma or bounded completeness assertion is assumed. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive6447

open SemigroupBasis Order6Sunday
open Recursive9726 (substituteFour)

abbrev basis := RecursiveDepth7Delta.S6_6447.basis
abbrev table := RecursivePublishedFinite.S6_6447.table
abbrev LD := S5_107.ListDerives basis

theorem derivesOldLaw (identity : Identity Nat)
    (member : identity ∈ RecursivePublishedFinite.S6_6447.basis) :
    Derives basis identity.lhs identity.rhs :=
  Derives.fromBasis (List.mem_append_left _ member)

theorem listDerivesSquareExpansion (letter : Nat) :
    LD [letter, letter] [letter, letter, letter] := by
  have law := derivesOldLaw RecursivePublishedFinite.S6_6447.basisLaw0 (by decide)
  exact S5_107.ListDerives.words (law.subst (fun _ => Word.singleton letter))

theorem listDerivesFirstExpansion (letter : Nat) (gap : List Nat) :
    LD ([letter] ++ gap ++ [letter]) ([letter, letter] ++ gap ++ [letter]) := by
  cases gap with
  | nil => simpa using listDerivesSquareExpansion letter
  | cons head tail =>
      have law := derivesOldLaw RecursivePublishedFinite.S6_6447.basisLaw1 (by decide)
      have substituted := law.subst (substituteFour (Word.singleton letter) ⟨head, tail⟩
        (Word.singleton letter) (Word.singleton letter))
      have listed := S5_107.ListDerives.ofWord substituted
      simp only [Word.toList_bind] at listed
      simpa [RecursivePublishedFinite.S6_6447.basisLaw1, Recursive9726.substituteFour,
        Word.toList, Word.singleton, List.append_assoc] using listed

theorem listDerivesHeadExpansion (letter : Nat) (tail : List Nat) (later : letter ∈ tail) :
    LD (letter :: tail) (letter :: letter :: tail) := by
  obtain ⟨gap, after, shape⟩ := List.mem_iff_append.mp later
  have expanded := (listDerivesFirstExpansion letter gap).append after
  simpa [shape, List.append_assoc] using expanded

theorem listDerivesPrefixSquareInsertion (payload : Word Nat) (letter : Nat) :
    LD (payload.toList ++ [letter, letter]) ([letter] ++ payload.toList ++ [letter, letter]) := by
  have law := derivesOldLaw RecursivePublishedFinite.S6_6447.basisLaw2 (by decide)
  have substituted := law.subst (substituteFour payload (Word.singleton letter)
    (Word.singleton letter) (Word.singleton letter))
  have listed := S5_107.ListDerives.ofWord substituted
  simp only [Word.toList_bind] at listed
  simpa [RecursivePublishedFinite.S6_6447.basisLaw2, Recursive9726.substituteFour,
    Word.toList, Word.singleton, List.append_assoc] using listed

/-- An extra earliest copy is dispensable when two actual later copies remain. -/
theorem prepend_at_two (letters : List Nat) (letter : Nat) (twice : 2 ≤ letters.count letter) :
    LD letters (letter :: letters) := by
  obtain ⟨before, middle, after, shape⟩ := Msg0463NilZ2.exists_two_occurrence_split letter twice
  cases before with
  | nil =>
      have expanded := (listDerivesFirstExpansion letter middle).append after
      simpa [shape, List.append_assoc] using expanded
  | cons beforeHead beforeTail =>
      have grow := listDerivesFirstExpansion letter middle
      have step1 := grow.context (beforeHead :: beforeTail) after
      have step2 := (listDerivesPrefixSquareInsertion (⟨beforeHead, beforeTail⟩ : Word Nat) letter).append
        (middle ++ [letter] ++ after)
      have step2Aligned :
          LD ((beforeHead :: beforeTail) ++ ([letter, letter] ++ middle ++ [letter]) ++ after)
            (([letter] ++ (beforeHead :: beforeTail)) ++ ([letter, letter] ++ middle ++ [letter]) ++ after) := by
        simpa [Word.toList, List.append_assoc] using step2
      have step3 := grow.symm.context ([letter] ++ (beforeHead :: beforeTail)) after
      have combined := step1.trans (step2Aligned.trans step3)
      simpa [shape, List.append_assoc] using combined

theorem growOpposite : SimplePrefix.GrowAtTwo (reversedBasis basis) := by
  intro letters letter twice
  have original := prepend_at_two letters.reverse letter (by simpa using twice)
  have reversed := SimplePrefix.reverse_listDerives original
  simpa [List.reverse_cons] using reversed

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive6447

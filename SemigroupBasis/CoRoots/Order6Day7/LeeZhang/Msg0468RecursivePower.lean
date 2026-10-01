import SemigroupBasis.CoRoots.Order6Sunday.RecursiveSeparatedCubeFinite
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0468PrefixNormalization

/-! Actual B8 interval growth, importing S3's recorded separated-cube
proof unchanged. The two arbitrary gaps are independently allowed to be
empty; no empty semigroup-word substitution is used. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive9726

open SemigroupBasis Order6Sunday

abbrev basis := RecursiveDepth7Delta.S6_9726.basis
abbrev table := RecursivePublishedFinite.S6_9726.table
abbrev LD := S5_107.ListDerives basis

def substituteFour (x y z t : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

theorem derivesOldLaw (identity : Identity Nat)
    (member : identity ∈ RecursivePublishedFinite.S6_9726.basis) :
    Derives basis identity.lhs identity.rhs :=
  Derives.fromBasis (List.mem_append_left _ member)

theorem listDerivesCubeExpansion (letter : Nat) :
    LD [letter, letter, letter] [letter, letter, letter, letter] := by
  have law := derivesOldLaw RecursivePublishedFinite.S6_9726.basisLaw0 (by decide)
  exact S5_107.ListDerives.words (law.subst (fun _ => Word.singleton letter))

theorem listDerivesTripleRotation (letter : Nat) (payload : Word Nat) :
    LD ([letter, letter, letter] ++ payload.toList)
      ([letter, letter] ++ payload.toList ++ [letter]) := by
  have law := derivesOldLaw RecursivePublishedFinite.S6_9726.basisLaw1 (by decide)
  have substituted := law.subst (substituteFour (Word.singleton letter) payload
    (Word.singleton letter) (Word.singleton letter))
  have listed := S5_107.ListDerives.ofWord substituted
  simp only [Word.toList_bind] at listed
  simpa [RecursivePublishedFinite.S6_9726.basisLaw1, substituteFour,
    Word.toList, Word.singleton, List.append_assoc] using listed

theorem listDerivesTripleExpansion (letter : Nat) (firstGap secondGap : List Nat) :
    LD ([letter] ++ firstGap ++ [letter] ++ secondGap ++ [letter])
      ([letter] ++ firstGap ++ [letter] ++ secondGap ++ [letter, letter]) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil => simpa using listDerivesCubeExpansion letter
      | cons head tail =>
          have rotation := listDerivesTripleRotation letter (⟨head, tail⟩ : Word Nat)
          have first : LD ([letter, letter] ++ (head :: tail) ++ [letter])
              ([letter, letter, letter] ++ (head :: tail)) := rotation.symm
          have expansion := (listDerivesCubeExpansion letter).append (head :: tail)
          have second : LD ([letter, letter, letter, letter] ++ (head :: tail))
              ([letter, letter, letter] ++ (head :: tail) ++ [letter]) := by
            simpa [List.append_assoc] using rotation.prepend [letter]
          have third := rotation.append [letter]
          simpa [List.append_assoc] using first.trans (expansion.trans (second.trans third))
  | cons firstHead firstTail =>
      cases secondGap with
      | nil =>
          have law := derivesOldLaw RecursivePublishedFinite.S6_9726.basisLaw2 (by decide)
          have substituted := law.subst (substituteFour (Word.singleton letter) ⟨firstHead, firstTail⟩
            (Word.singleton letter) (Word.singleton letter))
          have listed := S5_107.ListDerives.ofWord substituted
          simp only [Word.toList_bind] at listed
          simpa [RecursivePublishedFinite.S6_9726.basisLaw2, substituteFour,
            Word.toList, Word.singleton, List.append_assoc] using listed
      | cons secondHead secondTail =>
          have substituted := RecursiveSeparatedCubeFinite.separatedCubeFromB8.subst
            (substituteFour (Word.singleton letter) ⟨firstHead, firstTail⟩ ⟨secondHead, secondTail⟩
              (Word.singleton letter))
          have listed := S5_107.ListDerives.ofWord substituted
          simp only [Word.toList_bind] at listed
          simpa [RecursiveSeparatedCubeFinite.separatedCube, substituteFour,
            Word.toList, Word.singleton, List.append_assoc] using listed

theorem tripleIntervalGrowth : PrefixCount.TripleIntervalGrowth basis := listDerivesTripleExpansion

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive9726

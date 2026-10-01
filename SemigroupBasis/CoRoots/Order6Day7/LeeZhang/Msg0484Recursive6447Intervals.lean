import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0484Recursive6447Power

/-! B12 swaps with arbitrary past/future witness gaps. The two additional
fixed derivations are exactly the finite inputs requested from S3; all
substitutions and independently empty gaps are handled by the owner here. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive6447

open SemigroupBasis Order6Sunday
open Recursive9726 (substituteFour)

structure FixedSwaps : Prop where
  squareCommute : Derives basis (⟨0, [0, 1, 1]⟩ : Word Nat) (⟨1, [1, 0, 0]⟩ : Word Nat)
  mixedEmptyPrefix : Derives basis (⟨0, [0, 1, 2, 1]⟩ : Word Nat) (⟨0, [1, 0, 2, 1]⟩ : Word Nat)

theorem listDerivesSquareCommute (fixed : FixedSwaps) (left right : Nat) :
    LD [left, left, right, right] [right, right, left, left] :=
  S5_107.ListDerives.words (fixed.squareCommute.subst
    (substituteFour (Word.singleton left) (Word.singleton right)
      (Word.singleton left) (Word.singleton left)))

theorem listDerivesSwapPastInterval (left right : Nat) (firstGap secondGap : List Nat) :
    LD ([left] ++ firstGap ++ [right] ++ secondGap ++ [left, right])
      ([left] ++ firstGap ++ [right] ++ secondGap ++ [right, left]) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          have law3 := derivesOldLaw RecursivePublishedFinite.S6_6447.basisLaw3 (by decide)
          have law4 := derivesOldLaw RecursivePublishedFinite.S6_6447.basisLaw4 (by decide)
          have first : LD [left, left, right, right] [left, right, left, right] :=
            S5_107.ListDerives.words (law3.subst (substituteFour (Word.singleton left)
              (Word.singleton right) (Word.singleton left) (Word.singleton left)))
          have second : LD [left, left, right, right] [left, right, right, left] :=
            S5_107.ListDerives.words (law4.subst (substituteFour (Word.singleton left)
              (Word.singleton right) (Word.singleton left) (Word.singleton left)))
          exact first.symm.trans second
      | cons head tail =>
          have law := derivesOldLaw RecursivePublishedFinite.S6_6447.basisLaw8 (by decide)
          have substituted := law.subst (substituteFour (Word.singleton left) (Word.singleton right)
            ⟨head, tail⟩ (Word.singleton left))
          have listed := S5_107.ListDerives.ofWord substituted
          simp only [Word.toList_bind] at listed
          simpa [RecursivePublishedFinite.S6_6447.basisLaw8, Recursive9726.substituteFour,
            Word.toList, Word.singleton, List.append_assoc] using listed
  | cons firstHead firstTail =>
      cases secondGap with
      | nil =>
          have law6 := derivesOldLaw RecursivePublishedFinite.S6_6447.basisLaw6 (by decide)
          have law7 := derivesOldLaw RecursivePublishedFinite.S6_6447.basisLaw7 (by decide)
          let substitution := substituteFour (Word.singleton left) ⟨firstHead, firstTail⟩
            (Word.singleton right) (Word.singleton left)
          have substituted := (law6.subst substitution).symm.trans (law7.subst substitution)
          have listed := S5_107.ListDerives.ofWord substituted
          simp only [Word.toList_bind] at listed
          simpa [RecursivePublishedFinite.S6_6447.basisLaw6, RecursivePublishedFinite.S6_6447.basisLaw7,
            substitution, Recursive9726.substituteFour, Word.toList, Word.singleton, List.append_assoc] using listed
      | cons secondHead secondTail =>
          have law : Derives basis RecursiveDepth7Delta.S6_6447.addedLaw2.lhs
              RecursiveDepth7Delta.S6_6447.addedLaw2.rhs := Derives.fromBasis (by decide)
          have substituted := law.subst (substituteFour (Word.singleton left) ⟨firstHead, firstTail⟩
            (Word.singleton right) ⟨secondHead, secondTail⟩)
          have listed := S5_107.ListDerives.ofWord substituted
          simp only [Word.toList_bind] at listed
          simpa [RecursiveDepth7Delta.S6_6447.addedLaw2, Recursive9726.substituteFour,
            Word.toList, Word.singleton, List.append_assoc] using listed

theorem listDerivesSwapMixedInterval (fixed : FixedSwaps) (left right : Nat)
    (firstGap secondGap : List Nat) :
    LD ([left] ++ firstGap ++ [left, right] ++ secondGap ++ [right])
      ([left] ++ firstGap ++ [right, left] ++ secondGap ++ [right]) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          have law := derivesOldLaw RecursivePublishedFinite.S6_6447.basisLaw3 (by decide)
          exact S5_107.ListDerives.words (law.subst (substituteFour (Word.singleton left)
            (Word.singleton right) (Word.singleton left) (Word.singleton left)))
      | cons head tail =>
          have substituted := fixed.mixedEmptyPrefix.subst
            (substituteFour (Word.singleton left) (Word.singleton right) ⟨head, tail⟩ (Word.singleton left))
          have listed := S5_107.ListDerives.ofWord substituted
          simp only [Word.toList_bind] at listed
          simpa [Recursive9726.substituteFour, Word.toList, Word.singleton, List.append_assoc] using listed
  | cons firstHead firstTail =>
      cases secondGap with
      | nil =>
          have law := derivesOldLaw RecursivePublishedFinite.S6_6447.basisLaw6 (by decide)
          have substituted := law.subst (substituteFour (Word.singleton left) ⟨firstHead, firstTail⟩
            (Word.singleton right) (Word.singleton left))
          have listed := S5_107.ListDerives.ofWord substituted
          simp only [Word.toList_bind] at listed
          simpa [RecursivePublishedFinite.S6_6447.basisLaw6, Recursive9726.substituteFour,
            Word.toList, Word.singleton, List.append_assoc] using listed
      | cons secondHead secondTail =>
          have law : Derives basis RecursiveDepth7Delta.S6_6447.addedLaw0.lhs
              RecursiveDepth7Delta.S6_6447.addedLaw0.rhs := Derives.fromBasis (by decide)
          have substituted := law.subst (substituteFour (Word.singleton left) ⟨firstHead, firstTail⟩
            (Word.singleton right) ⟨secondHead, secondTail⟩)
          have listed := S5_107.ListDerives.ofWord substituted
          simp only [Word.toList_bind] at listed
          simpa [RecursiveDepth7Delta.S6_6447.addedLaw0, Recursive9726.substituteFour,
            Word.toList, Word.singleton, List.append_assoc] using listed

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive6447

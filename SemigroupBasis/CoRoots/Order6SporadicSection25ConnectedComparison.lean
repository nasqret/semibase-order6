import SemigroupBasis.CoRoots.Order6SporadicSection25ConnectedClosure
import SemigroupBasis.CoRoots.Order6SporadicSection25LibraryBridges

/-! Unbounded comparison for two nontrivial support-connected words with
the same actual head. Global component matching is not assumed proved. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

theorem connected_to_headSquareEnvelope (withB0 : Bool) (head : Nat)
    (tail : List Nat) (tailNonempty : tail ≠ [])
    (connected : SupportConnected (head :: tail)) :
    ListDerives withB0 (head :: tail)
      ([head,head] ++ (head :: tail) ++ [head,head]) := by
  have appended := connected_append_headSquare withB0 head tail tailNonempty connected
  have padded : ListDerives withB0 ((head :: tail) ++ [head,head])
      ([head,head] ++ (head :: tail) ++ [head,head]) := by
    simpa only [Word.toList_singleton, List.append_nil, List.nil_append,
      List.cons_append, List.append_assoc] using
      (ruleA withB0 (Word.singleton head) [] (tail ++ [head])).symm
  exact appended.trans padded

theorem connected_sameHead_affineCompare (withB0 : Bool) (head : Nat)
    (leftTail rightTail : List Nat) (leftNonempty : leftTail ≠ [])
    (rightNonempty : rightTail ≠ [])
    (leftConnected : SupportConnected (head :: leftTail))
    (rightConnected : SupportConnected (head :: rightTail))
    (valid : (⟨⟨head,leftTail⟩,⟨head,rightTail⟩⟩ : Identity Nat).SatisfiedBy
      Generated.Catalogue.S4_96.table.semigroup.opposite) :
    ListDerives withB0 (head :: leftTail) (head :: rightTail) := by
  have left := connected_to_headSquareEnvelope withB0 head leftTail leftNonempty leftConnected
  have right := connected_to_headSquareEnvelope withB0 head rightTail rightNonempty rightConnected
  have middle : ListDerives withB0
      ([head,head] ++ (head :: leftTail) ++ [head,head])
      ([head,head] ++ (head :: rightTail) ++ [head,head]) := by
    simpa only [Word.toList, List.append_nil, List.nil_append, List.append_assoc] using
      actualAffineValid_anchored withB0 ⟨⟨head,leftTail⟩,⟨head,rightTail⟩⟩ valid
        ⟨head,[head]⟩ [] []
  exact left.trans (middle.trans right.symm)

theorem connected_sameHead_affineCompare_words (withB0 : Bool) (head : Nat)
    (leftTail rightTail : List Nat) (leftNonempty : leftTail ≠ [])
    (rightNonempty : rightTail ≠ [])
    (leftConnected : SupportConnected (head :: leftTail))
    (rightConnected : SupportConnected (head :: rightTail))
    (valid : (⟨⟨head,leftTail⟩,⟨head,rightTail⟩⟩ : Identity Nat).SatisfiedBy
      Generated.Catalogue.S4_96.table.semigroup.opposite) :
    Derives (basis withB0) ⟨head,leftTail⟩ ⟨head,rightTail⟩ :=
  S5_107.ListDerives.toWord
    (connected_sameHead_affineCompare withB0 head leftTail rightTail leftNonempty
      rightNonempty leftConnected rightConnected valid)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.connected_to_headSquareEnvelope
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.connected_sameHead_affineCompare
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.connected_sameHead_affineCompare_words

end SemigroupBasis.CoRoots.Order6SporadicSection25

import SemigroupBasis.CoRoots.Order6SporadicSection25AnchoredAffine

/-! Constructive Section25 Lemma25.3: move an actual head-square marker
through every crossed cut. No arbitrary interior permutation is assumed. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

def SupportConnected (word : List Nat) : Prop :=
  ∀ left right, word = left ++ right → left ≠ [] → right ≠ [] →
    ∃ letter, letter ∈ left ∧ letter ∈ right

theorem headSquareAcrossSame (withB0 : Bool) (head : Nat)
    (before middle after : List Nat) :
    ListDerives withB0
      ([head] ++ before ++ [head,head] ++ middle ++ [head] ++ after)
      ([head] ++ before ++ middle ++ [head,head,head] ++ after) := by
  have first : ListDerives withB0
      ([head] ++ before ++ [head,head] ++ middle ++ [head] ++ after)
      ([head] ++ before ++ middle ++ [head] ++ after) := by
    simpa only [Word.toList_singleton, List.append_assoc, List.cons_append, List.nil_append] using
      (ruleA withB0 (Word.singleton head) before middle).append after
  have second : ListDerives withB0
      ([head] ++ before ++ middle ++ [head] ++ after)
      ([head] ++ before ++ middle ++ [head,head,head] ++ after) := by
    simpa only [Word.toList_singleton, List.append_assoc, List.cons_append,
      List.nil_append, List.append_nil] using
      (ruleA withB0 (Word.singleton head) (before ++ middle) []).symm.append after
  exact first.trans second

theorem headSquareAcrossCrossing (withB0 : Bool) (head crossing : Nat)
    (before between middle after : List Nat) :
    ListDerives withB0
      ([head] ++ before ++ [crossing] ++ between ++ [head,head] ++ middle ++ [crossing] ++ after)
      ([head] ++ before ++ [crossing] ++ between ++ middle ++ [crossing] ++ [head,head] ++ after) := by
  simpa only [Word.toList_singleton, List.append_assoc, List.cons_append, List.nil_append] using
    (ruleC withB0 (Word.singleton head) (Word.singleton crossing) before between middle).append after

theorem moveHeadSquare (withB0 : Bool) (head : Nat)
    (before suffix : List Nat)
    (connected : SupportConnected ([head] ++ before ++ suffix)) :
    ListDerives withB0
      ([head] ++ before ++ [head,head] ++ suffix)
      ([head] ++ before ++ suffix ++ [head,head]) := by
  cases suffixShape : suffix with
  | nil =>
      simpa only [List.append_nil] using
        S5_107.ListDerives.refl (basis := basis withB0) ([head] ++ before ++ [head,head])
  | cons first rest =>
      have connectedCurrent : SupportConnected ([head] ++ before ++ (first :: rest)) := by
        simpa only [suffixShape] using connected
      have leftNonempty : [head] ++ before ≠ [] := by
        intro impossible
        cases impossible
      rcases connectedCurrent ([head] ++ before) (first :: rest) rfl leftNonempty (by simp) with
        ⟨crossing, leftMember, rightMember⟩
      rcases List.mem_iff_append.mp rightMember with ⟨middle, after, shape⟩
      have nextConnected : SupportConnected
          ([head] ++ (before ++ middle ++ [crossing]) ++ after) := by
        simpa only [shape, List.append_assoc, List.cons_append, List.nil_append] using connectedCurrent
      have firstStep : ListDerives withB0
          ([head] ++ before ++ [head,head] ++ (first :: rest))
          ([head] ++ (before ++ middle ++ [crossing]) ++ [head,head] ++ after) := by
        rw [shape]
        simp only [List.mem_append, List.mem_singleton] at leftMember
        rcases leftMember with same | inBefore
        · subst crossing
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using
            headSquareAcrossSame withB0 head before middle after
        · rcases List.mem_iff_append.mp inBefore with ⟨preSegment, between, beforeShape⟩
          rw [beforeShape]
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using
            headSquareAcrossCrossing withB0 head crossing preSegment between middle after
      have remaining := moveHeadSquare withB0 head (before ++ middle ++ [crossing]) after nextConnected
      simpa only [shape, List.append_assoc, List.cons_append, List.nil_append] using
        firstStep.trans remaining
termination_by suffix.length
decreasing_by
  have sourceLength := congrArg List.length suffixShape
  have lengths := congrArg List.length shape
  simp only [List.length_append, List.length_cons] at sourceLength lengths
  omega

theorem connected_append_headSquare (withB0 : Bool) (head : Nat)
    (tail : List Nat) (tailNonempty : tail ≠ [])
    (connected : SupportConnected (head :: tail)) :
    ListDerives withB0 (head :: tail) ((head :: tail) ++ [head,head]) := by
  rcases connected [head] tail rfl (by intro impossible; cases impossible) tailNonempty with
    ⟨letter, singletonMember, tailMember⟩
  have equal : letter = head := List.mem_singleton.mp singletonMember
  subst letter
  rcases List.mem_iff_append.mp tailMember with ⟨before, after, shape⟩
  have expanded : ListDerives withB0 (head :: tail)
      ([head] ++ (before ++ [head]) ++ [head,head] ++ after) := by
    simpa only [shape, Word.toList_singleton, List.append_assoc,
      List.cons_append, List.nil_append, List.append_nil] using
      (ruleA withB0 (Word.singleton head) before []).symm.append after
  have nextConnected : SupportConnected ([head] ++ (before ++ [head]) ++ after) := by
    simpa only [shape, List.append_assoc, List.cons_append, List.nil_append] using connected
  have shifted := moveHeadSquare withB0 head (before ++ [head]) after nextConnected
  simpa only [shape, List.append_assoc, List.cons_append, List.nil_append] using expanded.trans shifted

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.headSquareAcrossSame
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.headSquareAcrossCrossing
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.moveHeadSquare
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.connected_append_headSquare

end SemigroupBasis.CoRoots.Order6SporadicSection25

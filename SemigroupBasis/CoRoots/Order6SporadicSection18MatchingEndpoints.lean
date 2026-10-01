import SemigroupBasis.CoRoots.Order6SporadicSection18ConnectedEnds
import SemigroupBasis.CoRoots.Order6SporadicSection18CrossingRules

/-! Direct C7 endpoint propagation using (18.1e). The endpoint may be
duplicated while crossing a linked suffix; no B7/B8 swapping identity or
multiplicity-preserving normalization is assumed. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6SporadicSection12

theorem supportConnected_of_connected {word : Word Nat} (connected : Connected word) :
    ConnectedComponentSupportConnected word.toList := by
  intro left right shape leftNonempty rightNonempty
  apply Classical.byContradiction
  intro disjoint
  obtain ⟨leftHead, leftTail, leftShape⟩ := List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨rightHead, rightTail, rightShape⟩ := List.exists_cons_of_ne_nil rightNonempty
  subst left
  subst right
  apply connected.2
  let leftWord : Word Nat := ⟨leftHead, leftTail⟩
  let rightWord : Word Nat := ⟨rightHead, rightTail⟩
  refine ⟨leftWord, rightWord, ?_, ?_⟩
  · apply Word.toList_injective
    exact shape
  · intro letter leftMember rightMember
    exact disjoint ⟨letter, leftMember, rightMember⟩

private theorem exists_last_occurrence {tested : Nat} :
    ∀ {letters : List Nat}, tested ∈ letters →
      ∃ before after, letters = before ++ tested :: after ∧ tested ∉ after
  | [], member => by simp at member
  | head :: tail, member => by
      by_cases later : tested ∈ tail
      · obtain ⟨before, after, shape, absent⟩ := exists_last_occurrence later
        exact ⟨head :: before, after, by simp [shape], absent⟩
      · have headEq : head = tested := by
          rcases List.mem_cons.mp member with equal | tailMember
          · exact equal.symm
          · exact False.elim (later tailMember)
        subst head
        exact ⟨[], tail, by simp, later⟩

/-- A crossing letter permits appending the distinguished endpoint farther
right. The unprocessed suffix strictly shortens on every recursive step. -/
theorem appendEndpointThroughLinked (endpoint : Nat) :
    ∀ (interior suffix : List Nat), endpoint ∉ suffix →
      ConnectedComponentSuffixLinked (endpoint :: interior ++ [endpoint]) suffix →
      ∃ finalInterior, ListDerives
        (endpoint :: interior ++ endpoint :: suffix)
        (endpoint :: finalInterior ++ [endpoint])
  | interior, [], _, _ =>
      ⟨interior, S5_107.ListDerives.refl _⟩
  | interior, next :: rest, endpointAbsent, linked => by
      obtain ⟨letter, frontMember, suffixMember⟩ :=
        linked [] (next :: rest) (by simp) (by simp)
      have notEndpoint : letter ≠ endpoint := by
        intro equal
        subst letter
        exact endpointAbsent suffixMember
      have inInterior : letter ∈ interior := by
        have member : letter ∈ endpoint :: interior ++ [endpoint] := by
          simpa only [List.append_nil] using frontMember
        rcases List.mem_append.mp member with first | final
        · rcases List.mem_cons.mp first with equal | present
          · exact False.elim (notEndpoint equal)
          · exact present
        · have equal : letter = endpoint := by simpa using final
          exact False.elim (notEndpoint equal)
      obtain ⟨interiorLeft, interiorRight, interiorShape⟩ := List.mem_iff_append.mp inInterior
      obtain ⟨before, after, suffixShape⟩ := List.mem_iff_append.mp suffixMember
      let nextInterior := interior ++ [endpoint] ++ before ++ [letter]
      have crossing :=
        (appendCrossing (Word.singleton endpoint) (Word.singleton letter)
          interiorLeft interiorRight before).append after
      have first : ListDerives
          (endpoint :: interior ++ endpoint :: next :: rest)
          (endpoint :: nextInterior ++ endpoint :: after) := by
        simpa [Word.singleton, Word.toList, interiorShape, suffixShape,
          nextInterior, List.append_assoc] using crossing
      have afterAbsent : endpoint ∉ after := by
        intro present
        apply endpointAbsent
        rw [suffixShape]
        exact List.mem_append.mpr (Or.inr (List.Mem.tail letter present))
      have afterLinked :
          ConnectedComponentSuffixLinked (endpoint :: nextInterior ++ [endpoint]) after := by
        intro left right afterShape rightNonempty
        have oldShape : next :: rest = (before ++ [letter] ++ left) ++ right := by
          simp [suffixShape, afterShape, List.append_assoc]
        obtain ⟨value, oldMember, rightMember⟩ :=
          linked (before ++ [letter] ++ left) right oldShape rightNonempty
        refine ⟨value, ?_, rightMember⟩
        simpa [nextInterior, List.mem_append, or_assoc, or_left_comm, or_comm] using oldMember
      have shorter : after.length < (next :: rest).length := by
        have lengths := congrArg List.length suffixShape
        simp only [List.length_append, List.length_cons] at lengths ⊢
        omega
      obtain ⟨finalInterior, finalDerivation⟩ :=
        appendEndpointThroughLinked endpoint nextInterior after afterAbsent afterLinked
      exact ⟨finalInterior, first.trans finalDerivation⟩
termination_by _ suffix => suffix.length
decreasing_by omega

/-- Every connected C7 word derives to a word with the same initial letter
at both ends. The derivation is unrestricted in word length and alphabet. -/
theorem connected_matching_endpoints (word : Word Nat) (connected : Connected word) :
    ∃ interior, ListDerives word.toList (word.head :: interior ++ [word.head]) := by
  cases word with
  | mk head tail =>
      have tailNonempty : tail ≠ [] := by
        intro empty
        subst tail
        simp [Connected, Word.toList] at connected
      have supportConnected := supportConnected_of_connected connected
      have headInTail : head ∈ tail :=
        connectedComponentSupportConnected_cons_tail supportConnected tailNonempty
      obtain ⟨before, after, tailShape, headAbsent⟩ := exists_last_occurrence headInTail
      have wordShape : (Word.mk head tail).toList = (head :: before ++ [head]) ++ after := by
        simp [Word.toList, tailShape, List.append_assoc]
      have linked : ConnectedComponentSuffixLinked (head :: before ++ [head]) after :=
        connectedComponentSuffixLinked_of_connected supportConnected wordShape (by simp)
      obtain ⟨interior, derivation⟩ := appendEndpointThroughLinked head before after headAbsent linked
      exact ⟨interior, by simpa [Word.toList, tailShape, List.append_assoc] using derivation⟩

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization.supportConnected_of_connected
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization.appendEndpointThroughLinked
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization.connected_matching_endpoints

end SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization

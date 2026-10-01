import SemigroupBasis.CoRoots.Order6SporadicSection25F3Connectivity

/-! Constructive block merging for Section25 Lemma25.6. The comparison
route needs a nontrivial connected representative; it does not assume one.
No disjoint-support or bounded-search premise is needed for the merge. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

def NontrivialConnected (word : List Nat) : Prop :=
  2 ≤ word.length ∧ SupportConnected word

theorem nonempty_split_last (word : List Nat) :
    word ≠ [] → ∃ front last, word = front ++ [last] := by
  induction word with
  | nil =>
      intro nonempty
      exact False.elim (nonempty rfl)
  | cons head tail ih =>
      intro _
      rcases tail with _ | ⟨next, rest⟩
      · exact ⟨[], head, rfl⟩
      · rcases ih (by simp) with ⟨front, last, shape⟩
        refine ⟨head :: front, last, ?_⟩
        simpa only [List.cons_append] using congrArg (List.cons head) shape

theorem connected_repeated_last (word : List Nat)
    (connected : NontrivialConnected word) :
    ∃ a b last, word = a ++ [last] ++ b ++ [last] := by
  have nonempty : word ≠ [] := by
    intro empty
    have lengthBound := connected.1
    simp only [empty, List.length_nil] at lengthBound
    omega
  rcases nonempty_split_last word nonempty with ⟨front, last, shape⟩
  have frontNonempty : front ≠ [] := by
    intro empty
    have lengthBound := connected.1
    simp only [shape, empty, List.nil_append, List.length_cons, List.length_nil] at lengthBound
    omega
  rcases connected.2 front [last] shape frontNonempty (by simp) with
    ⟨letter, inFront, inLast⟩
  have equal : letter = last := List.mem_singleton.mp inLast
  subst letter
  rcases List.mem_iff_append.mp inFront with ⟨a, b, frontShape⟩
  refine ⟨a, b, last, ?_⟩
  simpa only [frontShape, List.append_assoc, List.cons_append, List.nil_append] using shape

theorem connected_repeated_head (word : List Nat)
    (connected : NontrivialConnected word) :
    ∃ head c d, word = [head] ++ c ++ [head] ++ d := by
  rcases word with _ | ⟨head, tail⟩
  · have lengthBound := connected.1
    simp only [List.length_nil] at lengthBound
    omega
  · have tailNonempty : tail ≠ [] := by
      intro empty
      have lengthBound := connected.1
      simp only [empty, List.length_cons, List.length_nil] at lengthBound
      omega
    rcases connected.2 [head] tail rfl (by simp) tailNonempty with
      ⟨letter, inHead, inTail⟩
    have equal : letter = head := List.mem_singleton.mp inHead
    subst letter
    rcases List.mem_iff_append.mp inTail with ⟨c, d, tailShape⟩
    refine ⟨head, c, d, ?_⟩
    simp only [tailShape, List.append_assoc, List.cons_append, List.nil_append]

theorem mergeConnectedPair (left right : List Nat)
    (leftConnected : NontrivialConnected left)
    (rightConnected : NontrivialConnected right) :
    ∃ merged, NontrivialConnected merged ∧
      ListDerives true (left ++ right) merged ∧
      ∀ letter, letter ∈ merged ↔ letter ∈ left ++ right := by
  rcases connected_repeated_last left leftConnected with ⟨a, b, last, leftShape⟩
  rcases connected_repeated_head right rightConnected with ⟨head, c, d, rightShape⟩
  have lastMember : last ∈ left := by rw [leftShape]; simp
  have headMember : head ∈ right := by rw [rightShape]; simp
  let merged := left ++ [head,head,last,last] ++ right
  have mergedConnected : SupportConnected merged :=
    supportConnected_bridge left right last head leftConnected.2 rightConnected.2 lastMember headMember
  have mergedLength : 2 ≤ merged.length := by
    simp only [merged, List.length_append, List.length_cons, List.length_nil]
    omega
  have derives : ListDerives true (left ++ right) merged := by
    dsimp only [merged]
    rw [leftShape, rightShape]
    simpa only [List.append_assoc] using (B0_bridgeCollapse a b c d last head).symm
  exact ⟨merged, ⟨mergedLength, mergedConnected⟩, derives,
    fun letter => bridge_support_iff left right last head letter lastMember headMember⟩

theorem mergeConnectedList (parts : List (List Nat)) :
    (∀ part, part ∈ parts → NontrivialConnected part) → parts ≠ [] →
    ∃ merged, NontrivialConnected merged ∧
      ListDerives true parts.flatten merged ∧
      ∀ letter, letter ∈ merged ↔ letter ∈ parts.flatten := by
  induction parts with
  | nil =>
      intro _ nonempty
      exact False.elim (nonempty rfl)
  | cons first rest ih =>
      intro all _
      have firstConnected : NontrivialConnected first := all first (List.Mem.head _)
      rcases rest with _ | ⟨second, remaining⟩
      · refine ⟨first, firstConnected, ?_, ?_⟩
        · simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using
            S5_107.ListDerives.refl (basis := basis true) first
        · intro letter
          simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      · have restConnected : ∀ part, part ∈ second :: remaining → NontrivialConnected part := by
          intro part member
          exact all part (List.mem_cons_of_mem first member)
        rcases ih restConnected (by simp) with ⟨middle, middleConnected, middleDerives, middleSupport⟩
        rcases mergeConnectedPair first middle firstConnected middleConnected with
          ⟨merged, mergedConnected, mergedDerives, mergedSupport⟩
        have firstStep : ListDerives true ((first :: second :: remaining).flatten) (first ++ middle) := by
          simpa only [List.flatten_cons] using middleDerives.prepend first
        refine ⟨merged, mergedConnected, firstStep.trans mergedDerives, ?_⟩
        intro letter
        exact (mergedSupport letter).trans (by
          simpa only [List.mem_append, List.flatten_cons] using
            or_congr (Iff.rfl : letter ∈ first ↔ letter ∈ first) (middleSupport letter))

theorem mergeConnectedList_allow_empty (parts : List (List Nat))
    (all : ∀ part, part ∈ parts → NontrivialConnected part) :
    ∃ merged, (merged = [] ∨ NontrivialConnected merged) ∧
      ListDerives true parts.flatten merged ∧
      ∀ letter, letter ∈ merged ↔ letter ∈ parts.flatten := by
  by_cases empty : parts = []
  · subst parts
    exact ⟨[], Or.inl rfl, S5_107.ListDerives.refl [], fun _ => Iff.rfl⟩
  · rcases mergeConnectedList parts all empty with ⟨merged, connected, derives, support⟩
    exact ⟨merged, Or.inr connected, derives, support⟩

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.nonempty_split_last
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.connected_repeated_last
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.connected_repeated_head
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.mergeConnectedPair
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.mergeConnectedList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.mergeConnectedList_allow_empty

end SemigroupBasis.CoRoots.Order6SporadicSection25

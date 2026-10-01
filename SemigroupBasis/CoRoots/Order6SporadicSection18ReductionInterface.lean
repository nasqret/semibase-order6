import SemigroupBasis.CoRoots.Order6SporadicSection12Data
import SemigroupBasis.Examples.UniqueSeparatorFourInvariant
import SemigroupBasis.Examples.ConnectedComponentFourComponents
import SemigroupBasis.Transfer

/-! Pure reduction interfaces and helper proofs extracted verbatim from the
pinned Section12/S5_441 sources. Their concrete model-check imports are not
logical hypotheses of these generic statements and are intentionally absent. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction
open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6SporadicSection12

def SameContent (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList

def SingletonRigidity (candidate : FiniteTable) : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy candidate.semigroup →
    identity.lhs.toList.length = 1 →
    identity.lhs = identity.rhs

theorem eval_constant_idempotent
    (candidate : FiniteTable) (idempotent : Fin candidate.order)
    (idempotent_mul :
      candidate.mul idempotent idempotent = idempotent)
    (word : Word Nat) :
    candidate.semigroup.eval (fun _ => idempotent) word = idempotent := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      induction tail with
      | nil => rfl
      | cons next rest ih =>
          simp only [List.foldl_cons]
          rw [show candidate.semigroup.mul idempotent idempotent = idempotent by
            exact idempotent_mul]
          exact ih

theorem eval_eq_of_agree_on_word
    (candidate : FiniteTable)
    {first second : Nat → Fin candidate.order} {word : Word Nat}
    (agree :
      ∀ letter, letter ∈ word.toList → first letter = second letter) :
    candidate.semigroup.eval first word =
      candidate.semigroup.eval second word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval, Word.toList] at *
      have headAgree : first head = second head :=
        agree head (List.Mem.head tail)
      have tailAgree :
          ∀ letter ∈ tail, first letter = second letter := by
        intro letter member
        exact agree letter (List.Mem.tail head member)
      have foldAgree :
          ∀ (letters : List Nat)
            (leftInitial rightInitial : Fin candidate.order),
            leftInitial = rightInitial →
            (∀ letter ∈ letters, first letter = second letter) →
            letters.foldl
                (fun current letter =>
                  candidate.mul current (first letter))
                leftInitial =
              letters.foldl
                (fun current letter =>
                  candidate.mul current (second letter))
                rightInitial := by
        intro letters
        induction letters with
        | nil =>
            intro leftInitial rightInitial initialEq _
            exact initialEq
        | cons letter rest ih =>
            intro leftInitial rightInitial initialEq valuesAgree
            simp only [List.foldl_cons]
            apply ih
            · rw [initialEq,
                valuesAgree letter (List.Mem.head rest)]
            · intro value member
              exact valuesAgree value (List.Mem.tail letter member)
      exact foldAgree tail (first head) (second head)
        headAgree tailAgree

def IdempotentSeparable (candidate : FiniteTable) : Prop :=
  ∀ x y : Fin candidate.order, x ≠ y →
    (∃ leftIdempotent : Fin candidate.order,
      candidate.mul leftIdempotent leftIdempotent = leftIdempotent ∧
      candidate.mul leftIdempotent x ≠ candidate.mul leftIdempotent y) ∧
    (∃ rightIdempotent : Fin candidate.order,
      candidate.mul rightIdempotent rightIdempotent = rightIdempotent ∧
      candidate.mul x rightIdempotent ≠ candidate.mul y rightIdempotent)

private theorem connectedComponent_pairwise_flatten_append_disjoint
    {before after : List (List Nat)}
    (pairwise :
      (before ++ after).Pairwise
        ConnectedComponentSupportsDisjoint) :
    ConnectedComponentSupportsDisjoint
      before.flatten after.flatten := by
  have cross :=
    (List.pairwise_append.mp pairwise).2.2
  intro letter beforeMember afterMember
  rw [List.mem_flatten] at beforeMember afterMember
  rcases beforeMember with
    ⟨left, leftMember, letterInLeft⟩
  rcases afterMember with
    ⟨right, rightMember, letterInRight⟩
  exact
    (cross left leftMember right rightMember)
      letter letterInLeft letterInRight

private theorem connectedComponentDecomposeList_singleton_exactCut
    {gap : List Nat} {before after : List (List Nat)}
    {separator : Nat}
    (decompositionEq :
      connectedComponentDecomposeList gap =
        before ++ [separator] :: after) :
    UniqueSeparatorFourExactCut gap
      before.flatten separator after.flatten := by
  have flattenEq :=
    connectedComponentDecomposeList_flatten gap
  rw [decompositionEq] at flattenEq
  have gapShape :
      gap = before.flatten ++ separator :: after.flatten := by
    simpa [List.append_assoc] using flattenEq.symm
  have pairwise :=
    connectedComponentDecomposeList_pairwiseDisjoint gap
  rw [decompositionEq] at pairwise
  have beforeSuffixDisjoint :
      ConnectedComponentSupportsDisjoint
        before.flatten
        ([separator] :: after).flatten :=
    connectedComponent_pairwise_flatten_append_disjoint
      (before := before)
      (after := [separator] :: after)
      pairwise
  have tailPairwise :
      ([separator] :: after).Pairwise
        ConnectedComponentSupportsDisjoint :=
    (List.pairwise_append.mp pairwise).2.1
  have singletonAfterDisjoint :
      ConnectedComponentSupportsDisjoint
        [[separator]].flatten after.flatten :=
    connectedComponent_pairwise_flatten_append_disjoint
      (before := [[separator]])
      (after := after)
      (by simpa using tailPairwise)
  have separatorNotBefore :
      separator ∉ before.flatten := by
    intro separatorBefore
    apply
      beforeSuffixDisjoint separator separatorBefore
    change separator ∈ [separator] ++ after.flatten
    simp
  have separatorNotAfter :
      separator ∉ after.flatten := by
    exact singletonAfterDisjoint separator (by simp)
  have beforeCountZero :
      before.flatten.count separator = 0 :=
    List.count_eq_zero.mpr separatorNotBefore
  have afterCountZero :
      after.flatten.count separator = 0 :=
    List.count_eq_zero.mpr separatorNotAfter
  have countOne : gap.count separator = 1 := by
    rw [gapShape, List.count_append, List.count_cons_self,
      beforeCountZero, afterCountZero]
  have disjoint :
      UniqueSeparatorFourSupportsDisjoint
        before.flatten after.flatten := by
    intro letter beforeMember afterMember
    apply beforeSuffixDisjoint letter beforeMember
    change letter ∈ [separator] ++ after.flatten
    exact List.mem_append_right _ afterMember
  exact ⟨gapShape, countOne, disjoint⟩

/-- If a list has no exact separator cut, none of its deterministic support
components can be a singleton. -/
theorem connectedComponentDecomposeList_component_length_ge_two_of_no_exactCut
    {gap component : List Nat}
    (noExactCut :
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut
          gap left separator right)
    (componentMember :
      component ∈ connectedComponentDecomposeList gap) :
    2 ≤ component.length := by
  by_cases lengthAtLeastTwo : 2 ≤ component.length
  · exact lengthAtLeastTwo
  · have componentNonempty :
        component ≠ [] :=
      connectedComponentDecomposeList_nonempty_components
        gap component componentMember
    have componentPositive : 0 < component.length :=
      List.length_pos_iff.mpr componentNonempty
    have componentLengthOne : component.length = 1 := by
      omega
    obtain ⟨separator, componentEq⟩ :=
      List.length_eq_one_iff.mp componentLengthOne
    obtain ⟨before, after, decompositionEq⟩ :=
      List.mem_iff_append.mp componentMember
    have localCut :
        UniqueSeparatorFourExactCut gap
          before.flatten separator after.flatten := by
      apply connectedComponentDecomposeList_singleton_exactCut
      simpa [componentEq] using decompositionEq
    exact False.elim <|
      noExactCut
        ⟨before.flatten, separator, after.flatten, localCut⟩

/-- Quantified form of the lower bound for all support components. -/
theorem connectedComponentDecomposeList_components_length_ge_two_of_no_exactCut
    {gap : List Nat}
    (noExactCut :
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut
          gap left separator right) :
    ∀ component ∈ connectedComponentDecomposeList gap,
      2 ≤ component.length := by
  intro component componentMember
  exact
    connectedComponentDecomposeList_component_length_ge_two_of_no_exactCut
      noExactCut componentMember

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.eval_constant_idempotent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.eval_eq_of_agree_on_word
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.connectedComponentDecomposeList_components_length_ge_two_of_no_exactCut

end SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction

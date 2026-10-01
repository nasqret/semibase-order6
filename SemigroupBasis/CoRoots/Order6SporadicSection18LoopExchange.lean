import SemigroupBasis.CoRoots.Order6SporadicSection18ThirdAnchor

/-! Actual derivation-producing exchange of two nonempty loops at the same
anchor. At a first mismatch this advances the desired literal prefix, preserving
all remaining slots and exact letter counts. Canonical preservation is separate. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis

private def threeWords (anchor left right : Word Nat) : Nat → Word Nat
  | 0 => anchor
  | 1 => left
  | _ => right

theorem three_anchor_exchange (anchor left right : List Nat)
    (anchorNonempty : anchor ≠ []) (leftNonempty : left ≠ []) (rightNonempty : right ≠ []) :
    ListDerives (anchor ++ left ++ anchor ++ right ++ anchor)
      (anchor ++ right ++ anchor ++ left ++ anchor) := by
  obtain ⟨a, as, anchorShape⟩ := List.exists_cons_of_ne_nil anchorNonempty
  obtain ⟨l, ls, leftShape⟩ := List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨r, rs, rightShape⟩ := List.exists_cons_of_ne_nil rightNonempty
  let substitution := threeWords (S5_107.listWordOfCons a as) (S5_107.listWordOfCons l ls) (S5_107.listWordOfCons r rs)
  have law : Derives basis law05.lhs law05.rhs := Derives.fromBasis (by decide)
  have raw : ListDerives (law05.lhs.bind substitution).toList (law05.rhs.bind substitution).toList :=
    S5_107.ListDerives.ofWord (Derives.subst law substitution)
  rw [anchorShape, leftShape, rightShape]
  simpa [law05, substitution, threeWords, Word.bind, Word.toList, Word.append,
    S5_107.listWordOfCons, List.append_assoc] using raw

private theorem append_nonempty_right (before after : List Nat) (nonempty : after ≠ []) : before ++ after ≠ [] := by
  intro empty
  have lengths := congrArg List.length empty
  simp only [List.length_append, List.length_nil] at lengths
  apply nonempty
  apply List.eq_nil_of_length_eq_zero
  omega

theorem render_loop_exchange (common : List Slot) (current : Slot)
    (beforePivot : List Slot) (pivot : Slot) (beforeThird : List Slot) (third : Slot) (after : List Slot)
    (anchorNonempty : current.block ≠ []) (pivotGap : pivot.gap ≠ []) (thirdGap : third.gap ≠ [])
    (pivotEqual : pivot.block = current.block) (thirdEqual : third.block = current.block) :
    ListDerives (render (common ++ current :: ((beforePivot ++ [pivot]) ++ (beforeThird ++ [third]) ++ after)))
      (render (common ++ current :: ((beforeThird ++ [third]) ++ (beforePivot ++ [pivot]) ++ after))) := by
  have squareNonempty : squareList current.block ≠ [] := by
    obtain ⟨head, tail, shape⟩ := List.exists_cons_of_ne_nil anchorNonempty
    rw [shape, squareList_cons]
    simp
  have exchange := (three_anchor_exchange (squareList current.block)
    (render beforePivot ++ pivot.gap) (render beforeThird ++ third.gap) squareNonempty
    (append_nonempty_right _ _ pivotGap) (append_nonempty_right _ _ thirdGap)).context
      (render common ++ current.gap) (render after)
  simpa only [render_append, render, List.append_nil, pivotEqual, thirdEqual, List.append_assoc] using exchange

private theorem slotMoveToFront (x : Slot) (before after : List Slot) :
    (before ++ x :: after).Perm (x :: before ++ after) := by
  induction before with
  | nil => exact List.Perm.refl _
  | cons head tail ih => exact (List.Perm.cons head ih).trans (List.Perm.swap x head (tail ++ after))

private theorem slotPermAppend (left right : List Slot) : (left ++ right).Perm (right ++ left) := by
  induction left with
  | nil => simp
  | cons head tail ih =>
      simpa using (List.Perm.cons head ih).trans (slotMoveToFront head right tail).symm

theorem loop_swap_slotPermutation (common : List Slot) (current : Slot) (left right after : List Slot) :
    (common ++ current :: (left ++ right ++ after)).Perm (common ++ current :: (right ++ left ++ after)) :=
  (List.Perm.refl common).append (List.Perm.cons current ((slotPermAppend left right).append (List.Perm.refl after)))

theorem loop_swap_count (common : List Slot) (current : Slot) (left right after : List Slot) (x : Nat) :
    (render (common ++ current :: (right ++ left ++ after))).count x =
      (render (common ++ current :: (left ++ right ++ after))).count x := by
  simp only [render_append, render, List.count_append]
  omega

/-- A genuine Derives step now advances the source's desired next slot.
The output tail is a permutation of the unprocessed source tail and exact
letter counts are unchanged. No canonical-output hypothesis is smuggled in. -/
theorem canonical_mismatch_derived_prefix {left right : Word Nat}
    {leftAlphabet rightAlphabet : List Nat} {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (same : Actual.SameEval left.toList right.toList)
    (leftWitness : CanonicalWitness left.toList leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right.toList rightAlphabet rightFirst rightRest)
    (common : List Slot) (current wanted other : Slot) (sourceTail targetTail : List Slot)
    (leftShape : leftFirst :: leftRest = common ++ current :: wanted :: sourceTail)
    (rightShape : rightFirst :: rightRest = common ++ current :: other :: targetTail)
    (different : wanted ≠ other) :
    ∃ newTail : List Slot,
      ListDerives right.toList (render (common ++ current :: wanted :: newTail)) ∧
      newTail.Perm sourceTail ∧
      ∀ x, (render (common ++ current :: wanted :: newTail)).count x = right.toList.count x := by
  obtain ⟨loop1, loop2Tail, after, beforePivot, pivot, beforeThird, third,
    loop1Shape, loop2Shape, pivotEqual, thirdEqual, targetLoops⟩ :=
    canonical_mismatch_has_two_loops same leftWitness rightWitness common current wanted other
      sourceTail targetTail leftShape rightShape different
  have inputShape : rightFirst :: rightRest = common ++ current ::
      ((beforePivot ++ [pivot]) ++ (beforeThird ++ [third]) ++ after) := by
    simpa only [loop1Shape, loop2Shape] using targetLoops
  have currentMember : current ∈ rightFirst :: rightRest := by rw [rightShape]; simp
  have anchorNonempty := (rightWitness.2.2.2.2.2.2.2.1.1 current currentMember).1
  have pivotShape : rightFirst :: rightRest = (common ++ current :: beforePivot) ++
      pivot :: ((beforeThird ++ [third]) ++ after) := by
    rw [inputShape]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have thirdShape : rightFirst :: rightRest =
      (common ++ current :: ((beforePivot ++ [pivot]) ++ beforeThird)) ++ third :: after := by
    rw [inputShape]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have pivotGap := rightWitness.noninitial_gap_nonempty (common ++ current :: beforePivot) pivot
    ((beforeThird ++ [third]) ++ after) pivotShape (by simp)
  have thirdGap := rightWitness.noninitial_gap_nonempty
    (common ++ current :: ((beforePivot ++ [pivot]) ++ beforeThird)) third after thirdShape (by simp)
  let newTail := loop2Tail ++ loop1 ++ after
  have outputShape : common ++ current :: ((beforeThird ++ [third]) ++ (beforePivot ++ [pivot]) ++ after) =
      common ++ current :: wanted :: newTail := by
    rw [← loop2Shape, ← loop1Shape]
    simp only [newTail, List.cons_append, List.append_assoc]
  have exchange := render_loop_exchange common current beforePivot pivot beforeThird third after
    anchorNonempty pivotGap thirdGap pivotEqual thirdEqual
  rw [← inputShape, outputShape, rightWitness.2.2.2.2.2.2.2.2] at exchange
  have outputLoops : common ++ current :: ((wanted :: loop2Tail) ++ loop1 ++ after) =
      common ++ current :: wanted :: newTail := by simp only [newTail, List.cons_append, List.append_assoc]
  have swapped := loop_swap_slotPermutation common current loop1 (wanted :: loop2Tail) after
  rw [← targetLoops, outputLoops] at swapped
  have sourcePermutation := canonicalChainPermutation same leftWitness rightWitness
  rw [leftShape] at sourcePermutation
  have residual := perm_cancel_prefix common (current :: wanted :: sourceTail) (current :: wanted :: newTail)
    (sourcePermutation.trans swapped)
  have tailPermutation : newTail.Perm sourceTail := (List.Perm.cons_inv (List.Perm.cons_inv residual)).symm
  refine ⟨newTail, exchange, tailPermutation, ?_⟩
  intro x
  have counts := loop_swap_count common current loop1 (wanted :: loop2Tail) after x
  rw [← targetLoops, outputLoops, rightWitness.2.2.2.2.2.2.2.2] at counts
  exact counts

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.three_anchor_exchange
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.render_loop_exchange
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.loop_swap_slotPermutation
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.loop_swap_count
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonical_mismatch_derived_prefix

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

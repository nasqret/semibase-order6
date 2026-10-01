import SemigroupBasis.CoRoots.Order6SporadicSection17C5InputTerminal

/-! Maximal simple blocks sharing a marker are literally the same block.
The proof aligns the unique occurrence, compares the maximal tagged suffix
before it, and then uses literal prefix comparability. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem taggedPrefixes_unique (tag : Nat → Prop) (leftPrefix : List Nat) :
    ∀ (rightPrefix leftAfter rightAfter : List Nat),
      leftPrefix ++ leftAfter = rightPrefix ++ rightAfter →
      (∀ x ∈ leftPrefix, tag x) → (∀ x ∈ rightPrefix, tag x) →
      (∀ x tail, leftAfter = x :: tail → ¬ tag x) →
      (∀ x tail, rightAfter = x :: tail → ¬ tag x) → leftPrefix = rightPrefix := by
  induction leftPrefix with
  | nil =>
      intro rightPrefix leftAfter rightAfter shape leftTagged rightTagged leftBlocked rightBlocked
      cases rightPrefix with
      | nil => rfl
      | cons y ys =>
          exact False.elim (leftBlocked y (ys ++ rightAfter) shape (rightTagged y List.mem_cons_self))
  | cons x xs ih =>
      intro rightPrefix leftAfter rightAfter shape leftTagged rightTagged leftBlocked rightBlocked
      cases rightPrefix with
      | nil =>
          exact False.elim (rightBlocked x (xs ++ leftAfter) shape.symm (leftTagged x List.mem_cons_self))
      | cons y ys =>
          have equal : x = y := (List.cons.inj shape).1
          subst y
          have tail := ih ys leftAfter rightAfter (List.cons.inj shape).2
            (fun z member => leftTagged z (List.mem_cons_of_mem x member))
            (fun z member => rightTagged z (List.mem_cons_of_mem x member)) leftBlocked rightBlocked
          exact congrArg (List.cons x) tail

theorem taggedSuffixes_unique (tag : Nat → Prop) (leftBefore leftPart rightBefore rightPart : List Nat)
    (shape : leftBefore ++ leftPart = rightBefore ++ rightPart)
    (leftTagged : ∀ x ∈ leftPart, tag x) (rightTagged : ∀ x ∈ rightPart, tag x)
    (leftBlocked : ∀ leading x, leftBefore = leading ++ [x] → ¬ tag x)
    (rightBlocked : ∀ leading x, rightBefore = leading ++ [x] → ¬ tag x) : leftPart = rightPart := by
  have reversed : leftPart.reverse = rightPart.reverse := by
    apply taggedPrefixes_unique tag leftPart.reverse rightPart.reverse leftBefore.reverse rightBefore.reverse
    · simpa only [List.reverse_append] using congrArg List.reverse shape
    · intro x member
      exact leftTagged x (by simpa only [List.mem_reverse] using member)
    · intro x member
      exact rightTagged x (by simpa only [List.mem_reverse] using member)
    · intro x tail equal
      apply leftBlocked tail.reverse x
      simpa only [List.reverse_reverse,List.reverse_cons] using congrArg List.reverse equal
    · intro x tail equal
      apply rightBlocked tail.reverse x
      simpa only [List.reverse_reverse,List.reverse_cons] using congrArg List.reverse equal
  simpa only [List.reverse_reverse] using congrArg List.reverse reversed

theorem marker_context (x : Nat) (letters : List Nat) :
    x ∈ letters → ∃ before after, letters = before ++ x :: after := by
  induction letters with
  | nil => intro member; cases member
  | cons y ys ih =>
      intro member
      rcases List.mem_cons.mp member with rfl | found
      · exact ⟨[],ys,rfl⟩
      · rcases ih found with ⟨before,after,shape⟩
        exact ⟨y :: before,after,by rw [shape]; rfl⟩

theorem MaximalSimpleBlock.leftBoundary {word part : List Nat} (maximal : MaximalSimpleBlock word part)
    (before after : List Nat) (shape : word = before ++ part ++ after) :
    ∀ leading x, before = leading ++ [x] → word.count x ≠ 1 := by
  intro leading x beforeShape one
  apply maximal.2.2.1 x
  refine ⟨leading,after,?_,?_⟩
  · simpa only [beforeShape,List.append_assoc,List.cons_append,List.nil_append] using shape
  · intro y member
    rcases List.mem_cons.mp member with rfl | found
    · exact one
    · exact maximal.2.1.countOne y found

theorem fixedSuffix_cancel (left right suffix : List Nat)
    (equal : left ++ suffix = right ++ suffix) : left = right := by
  have reversed : suffix.reverse ++ left.reverse = suffix.reverse ++ right.reverse := by
    simpa only [List.reverse_append] using congrArg List.reverse equal
  have parts := fixedPrefix_cancel suffix.reverse left.reverse right.reverse reversed
  simpa only [List.reverse_reverse] using congrArg List.reverse parts

theorem MaximalSimpleBlock.eq_of_common_marker {word left right : List Nat}
    (first : MaximalSimpleBlock word left) (second : MaximalSimpleBlock word right)
    (x : Nat) (inLeft : x ∈ left) (inRight : x ∈ right) : left = right := by
  rcases first.2.1 with ⟨leftBefore,leftAfter,leftShape,leftCounts⟩
  rcases second.2.1 with ⟨rightBefore,rightAfter,rightShape,rightCounts⟩
  rcases marker_context x left inLeft with ⟨leftInner,leftTail,leftPart⟩
  rcases marker_context x right inRight with ⟨rightInner,rightTail,rightPart⟩
  have one := leftCounts x inLeft
  have leftPosition : word = (leftBefore ++ leftInner) ++ x :: (leftTail ++ leftAfter) := by
    simpa only [leftPart,List.append_assoc,List.cons_append] using leftShape
  have rightPosition : word = (rightBefore ++ rightInner) ++ x :: (rightTail ++ rightAfter) := by
    simpa only [rightPart,List.append_assoc,List.cons_append] using rightShape
  have position := first_split_unique x (leftBefore ++ leftInner) (leftTail ++ leftAfter)
    (rightBefore ++ rightInner) (rightTail ++ rightAfter)
    (countOne_prefix_absent one leftPosition) (countOne_prefix_absent one rightPosition)
    (leftPosition.symm.trans rightPosition)
  have leftInnerTagged : ∀ y ∈ leftInner, word.count y = 1 := by
    intro y member
    apply leftCounts y
    rw [leftPart]
    exact List.mem_append.mpr (Or.inl member)
  have rightInnerTagged : ∀ y ∈ rightInner, word.count y = 1 := by
    intro y member
    apply rightCounts y
    rw [rightPart]
    exact List.mem_append.mpr (Or.inl member)
  have inner := taggedSuffixes_unique (fun y => word.count y = 1)
    leftBefore leftInner rightBefore rightInner position.1 leftInnerTagged rightInnerTagged
    (MaximalSimpleBlock.leftBoundary first leftBefore leftAfter leftShape)
    (MaximalSimpleBlock.leftBoundary second rightBefore rightAfter rightShape)
  have beforeEqual : leftBefore = rightBefore := by
    apply fixedSuffix_cancel leftBefore rightBefore rightInner
    simpa only [inner] using position.1
  have afterEqual : left ++ leftAfter = right ++ rightAfter := by
    apply fixedPrefix_cancel leftBefore (left ++ leftAfter) (right ++ rightAfter)
    simpa only [beforeEqual,List.append_assoc] using leftShape.symm.trans rightShape
  have firstPrefix : left <+: right ++ rightAfter := ⟨leftAfter,afterEqual⟩
  have secondPrefix : right <+: right ++ rightAfter := ⟨rightAfter,rfl⟩
  rcases List.prefix_or_prefix_of_prefix firstPrefix secondPrefix with firstInSecond | secondInFirst
  · rcases firstInSecond with ⟨tail,equal⟩
    exact (MaximalSimpleBlock.eq_of_prefix first second.2.1 ⟨tail,equal.symm⟩).symm
  · rcases secondInFirst with ⟨tail,equal⟩
    exact MaximalSimpleBlock.eq_of_prefix second first.2.1 ⟨tail,equal.symm⟩

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.taggedPrefixes_unique
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.taggedSuffixes_unique
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.marker_context
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.MaximalSimpleBlock.leftBoundary
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.fixedSuffix_cancel
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.MaximalSimpleBlock.eq_of_common_marker

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6

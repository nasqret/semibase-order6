import SemigroupBasis.CoRoots.Order6SporadicSection12RestrictedReduction
import SemigroupBasis.CoRoots.Order6SporadicSection12Semantics
import SemigroupBasis.Examples.ConnectedComponentFourSemantics

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis
open SemigroupBasis.Examples

namespace S6_5626

/-!
The B8 connected-basis reduction.  The embedded `S4_70` is the paper's
`A0`.  Its prefix-cut detectors locate the matching right-hand cut, while
idempotent separability proves that the two resulting factor identities are
valid in B8.  The generic strong induction then supplies finite derivation
support for every valid identity.
-/

private theorem valid_a0_equalEval
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ valuation : Nat → Fin 4,
      connectedComponentFour.semigroup.eval valuation identity.lhs =
        connectedComponentFour.semigroup.eval valuation identity.rhs := by
  simpa [Generated.S4_70.table] using valid_a0 identity valid

private theorem valid_sameContent
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameContent identity.lhs identity.rhs := by
  intro letter
  exact connectedComponentFourEqualEval_support_iff
    identity.lhs identity.rhs
      (valid_a0_equalEval identity valid) letter

private theorem wordDisjoint_symm
    {left right : Word Nat}
    (disjoint : WordDisjoint left right) :
    WordDisjoint right left := by
  intro letter rightMember leftMember
  exact disjoint letter leftMember rightMember

private theorem component_left_valid
    {identity : Identity Nat} {left right left' right' : Word Nat}
    (valid : identity.SatisfiedBy table.semigroup)
    (leftSplit : identity.lhs = left ++ right)
    (rightSplit : identity.rhs = left' ++ right')
    (disjoint : WordDisjoint left right)
    (leftContent : SameContent left left')
    (rightContent : SameContent right right') :
    (Identity.mk left left').SatisfiedBy table.semigroup := by
  intro valuation
  by_cases same :
      table.semigroup.eval valuation left =
        table.semigroup.eval valuation left'
  · exact same
  have different :
      table.semigroup.eval valuation left ≠
        table.semigroup.eval valuation left' := same
  rcases idempotentSeparable
      (table.semigroup.eval valuation left)
      (table.semigroup.eval valuation left') different with
    ⟨_, ⟨rightIdempotent, rightIdempotent_mul, separates⟩⟩
  let combined : Nat → Fin table.order := fun letter =>
    if letter ∈ left.toList then valuation letter else rightIdempotent
  have evalLeft :
      table.semigroup.eval combined left =
        table.semigroup.eval valuation left :=
    eval_eq_of_agree_on_word table (by
      intro letter member
      simp [combined, member])
  have evalLeft' :
      table.semigroup.eval combined left' =
        table.semigroup.eval valuation left' :=
    eval_eq_of_agree_on_word table (by
      intro letter member
      have inLeft := (leftContent letter).mpr member
      simp [combined, inLeft])
  have evalRight :
      table.semigroup.eval combined right = rightIdempotent := by
    rw [eval_eq_of_agree_on_word table
      (second := fun _ => rightIdempotent) (by
        intro letter member
        have notLeft := wordDisjoint_symm disjoint letter member
        simp [combined, notLeft])]
    exact eval_constant_idempotent table rightIdempotent
      rightIdempotent_mul right
  have evalRight' :
      table.semigroup.eval combined right' = rightIdempotent := by
    rw [eval_eq_of_agree_on_word table
      (second := fun _ => rightIdempotent) (by
        intro letter member
        have inRight := (rightContent letter).mpr member
        have notLeft := wordDisjoint_symm disjoint letter inRight
        simp [combined, notLeft])]
    exact eval_constant_idempotent table rightIdempotent
      rightIdempotent_mul right'
  have wholeEquality := valid combined
  rw [leftSplit, rightSplit, Semigroup.eval_append,
    Semigroup.eval_append, evalLeft, evalLeft', evalRight,
    evalRight'] at wholeEquality
  exact (separates wholeEquality).elim

private theorem component_right_valid
    {identity : Identity Nat} {left right left' right' : Word Nat}
    (valid : identity.SatisfiedBy table.semigroup)
    (leftSplit : identity.lhs = left ++ right)
    (rightSplit : identity.rhs = left' ++ right')
    (disjoint : WordDisjoint left right)
    (leftContent : SameContent left left')
    (rightContent : SameContent right right') :
    (Identity.mk right right').SatisfiedBy table.semigroup := by
  intro valuation
  by_cases same :
      table.semigroup.eval valuation right =
        table.semigroup.eval valuation right'
  · exact same
  have different :
      table.semigroup.eval valuation right ≠
        table.semigroup.eval valuation right' := same
  rcases idempotentSeparable
      (table.semigroup.eval valuation right)
      (table.semigroup.eval valuation right') different with
    ⟨⟨leftIdempotent, leftIdempotent_mul, separates⟩, _⟩
  let combined : Nat → Fin table.order := fun letter =>
    if letter ∈ right.toList then valuation letter else leftIdempotent
  have evalRight :
      table.semigroup.eval combined right =
        table.semigroup.eval valuation right :=
    eval_eq_of_agree_on_word table (by
      intro letter member
      simp [combined, member])
  have evalRight' :
      table.semigroup.eval combined right' =
        table.semigroup.eval valuation right' :=
    eval_eq_of_agree_on_word table (by
      intro letter member
      have inRight := (rightContent letter).mpr member
      simp [combined, inRight])
  have evalLeft :
      table.semigroup.eval combined left = leftIdempotent := by
    rw [eval_eq_of_agree_on_word table
      (second := fun _ => leftIdempotent) (by
        intro letter member
        have notRight := disjoint letter member
        simp [combined, notRight])]
    exact eval_constant_idempotent table leftIdempotent
      leftIdempotent_mul left
  have evalLeft' :
      table.semigroup.eval combined left' = leftIdempotent := by
    rw [eval_eq_of_agree_on_word table
      (second := fun _ => leftIdempotent) (by
        intro letter member
        have inLeft := (leftContent letter).mpr member
        have notRight := disjoint letter inLeft
        simp [combined, notRight])]
    exact eval_constant_idempotent table leftIdempotent
      leftIdempotent_mul left'
  have wholeEquality := valid combined
  rw [leftSplit, rightSplit, Semigroup.eval_append,
    Semigroup.eval_append, evalLeft, evalLeft', evalRight,
    evalRight'] at wholeEquality
  exact (separates wholeEquality).elim

theorem singletonRigidity : SingletonRigidity table := by
  intro identity valid lengthOne
  cases lhsEq : identity.lhs with
  | mk head tail =>
      simp only [lhsEq, Word.toList, List.length_cons] at lengthOne
      have tailEmpty : tail = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      subst tail
      have equalEval := valid_a0_equalEval identity valid
      have sourceCut :
          connectedComponentFourUnaryCut [] head
            identity.lhs.toList := by
        exact
          ⟨[], [], by simp [lhsEq, Word.toList], by simp, by simp,
            by simp⟩
      have targetCut :=
        (connectedComponentFourEqualEval_unaryCut_iff
          identity.lhs identity.rhs equalEval [] head
          (by simp) (by simp [lhsEq, Word.toList])
          (by simp)).mp sourceCut
      rcases targetCut with
        ⟨leftLetters, rightLetters, rhsShape, leftExact,
          headAbsent, _⟩
      have leftEmpty : leftLetters = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro letter member
        have impossible : letter ∈ ([] : List Nat) :=
          (leftExact letter).mp member
        simpa using impossible
      have wholeContent := valid_sameContent identity valid
      have rightEmpty : rightLetters = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro letter member
        have rightMember : letter ∈ identity.rhs.toList := by
          rw [rhsShape]
          exact List.mem_append.mpr <|
            Or.inr (List.Mem.tail head member)
        have leftMember := (wholeContent letter).mpr rightMember
        have letterEq : letter = head := by
          simpa [lhsEq, Word.toList] using leftMember
        subst letter
        exact headAbsent member
      apply Word.toList_injective
      have rhsList : identity.rhs.toList = [head] := by
        simpa [leftEmpty, rightEmpty] using rhsShape
      simpa [lhsEq, Word.toList] using rhsList.symm

theorem orderedSplit : OrderedSplitProperty table := by
  intro identity left right valid leftSplit disjoint
  have equalEval := valid_a0_equalEval identity valid
  have covered :
      ∀ letter, letter ∈ left.toList →
        letter ∈ identity.lhs.toList := by
    intro letter member
    rw [leftSplit, Word.toList_append]
    exact List.mem_append.mpr (Or.inl member)
  have sourceCut :
      connectedComponentFourPrefixUnionCut
        left.toList identity.lhs.toList := by
    refine
      ⟨left.toList, right.toList, ?_, ?_, ?_, ?_, disjoint⟩
    · rw [leftSplit, Word.toList_append]
    · simp [Word.toList]
    · simp [Word.toList]
    · intro letter
      exact Iff.rfl
  have targetCut :=
    (connectedComponentFourEqualEval_prefixUnionCut_iff
      identity.lhs identity.rhs equalEval left.toList covered).mp
      sourceCut
  rcases targetCut with
    ⟨leftLetters, rightLetters, rhsLettersSplit,
      leftNonempty, rightNonempty, leftExact, rightDisjoint⟩
  cases leftLetters with
  | nil => exact False.elim (leftNonempty rfl)
  | cons leftHead leftTail =>
      cases rightLetters with
      | nil => exact False.elim (rightNonempty rfl)
      | cons rightHead rightTail =>
          let left' : Word Nat := ⟨leftHead, leftTail⟩
          let right' : Word Nat := ⟨rightHead, rightTail⟩
          have rightSplit : identity.rhs = left' ++ right' := by
            apply Word.toList_injective
            exact rhsLettersSplit
          have leftContent : SameContent left left' := by
            intro letter
            exact (leftExact letter).symm
          have wholeContent := valid_sameContent identity valid
          have rightContent : SameContent right right' := by
            intro letter
            constructor
            · intro inRight
              have inLhs : letter ∈ identity.lhs.toList := by
                rw [leftSplit, Word.toList_append]
                exact List.mem_append.mpr (Or.inr inRight)
              have inRhs := (wholeContent letter).mp inLhs
              rw [rhsLettersSplit] at inRhs
              rcases List.mem_append.mp inRhs with
                inLeftPrime | inRightPrime
              · have inLeft := (leftExact letter).mp inLeftPrime
                exact False.elim <|
                  wordDisjoint_symm disjoint letter inRight inLeft
              · exact inRightPrime
            · intro inRightPrime
              have inRhs : letter ∈ identity.rhs.toList := by
                rw [rhsLettersSplit]
                exact List.mem_append.mpr (Or.inr inRightPrime)
              have inLhs := (wholeContent letter).mpr inRhs
              rw [leftSplit, Word.toList_append] at inLhs
              rcases List.mem_append.mp inLhs with inLeft | inRight
              · have inLeftPrime := (leftExact letter).mpr inLeft
                exact False.elim <|
                  rightDisjoint letter inLeftPrime inRightPrime
              · exact inRight
          have targetDisjoint : WordDisjoint left' right' := by
            intro letter inLeft inRight
            exact rightDisjoint letter inLeft inRight
          exact
            ⟨left', right', rightSplit, targetDisjoint,
              leftContent, rightContent,
              component_left_valid valid leftSplit rightSplit disjoint
                leftContent rightContent,
              component_right_valid valid leftSplit rightSplit disjoint
                leftContent rightContent⟩

theorem connectedReduction :
    RestrictedBasisReduction table Connected :=
  restrictedBasisReduction_of_orderedSplit table
    singletonRigidity orderedSplit

end S6_5626

end SemigroupBasis.CoRoots.Order6SporadicSection12

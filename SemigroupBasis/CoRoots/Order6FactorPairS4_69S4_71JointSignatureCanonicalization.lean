import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71EventOrder
import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71CoveredSimpleFirstSwap

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

open SemigroupBasis

/-!
# Joint-signature canonicalization for `S4_69 x S4_71`

The old letter-level bubble premise compared first occurrences even when the
displayed occurrence was a last endpoint.  That statement is false.  This
module instead records the occurrence-selected event-position contract and a
durable final-crossing lemma which does not depend on the invalid bubble API.

At the final crossing against an already aligned target initial, an uncovered
simple letter would be an exact `S4_69` separator in the target but not in the
source.  The exact-cut component of `SameJointSignature` rules this out.  The
remaining theorem is the purely combinatorial occurrence-resolved schedule.
-/

/-! ## Occurrence-resolved event positions -/

/-- The occurrence at `position` has last-endpoint role exactly when the same
letter already occurs in its strict initial.  For a simple letter and a first
endpoint this is `false`; for a last endpoint it is `true`. -/
def occurrenceRoleIsLast
    (letters : List Nat) (position letter : Nat) : Bool :=
  decide (letter ∈ letters.take position)

/-- Position selected by an endpoint role.  This is the first occurrence for
`false` and the last occurrence for `true`. -/
def eventPos (letters : List Nat) (letter : Nat) (isLast : Bool) : Nat :=
  if isLast then
    letters.length - 1 - letters.reverse.idxOf letter
  else
    letters.idxOf letter

/-- The adjacent source occurrences `x,e` are oppositely ordered in the target
after selecting first/last occurrences from their actual source roles. -/
def OccurrenceResolvedAdjacentInversionAt
    (left right : List Nat) (position x e : Nat) : Prop :=
  left[position]? = some x ∧
    left[position + 1]? = some e ∧
      eventPos right e
          (occurrenceRoleIsLast left (position + 1) e) <
        eventPos right x
          (occurrenceRoleIsLast left position x)

@[simp] theorem occurrenceRoleIsLast_eq_true_iff
    {letters : List Nat} {position letter : Nat} :
    occurrenceRoleIsLast letters position letter = true ↔
      letter ∈ letters.take position := by
  simp [occurrenceRoleIsLast]

/-! ## Exact-cut extremality at the aligned initial -/

/-- A quadratic guard has one occurrence in the strict initial and its other
occurrence strictly after the adjacent site. -/
def QuadraticGuardCoversAt (letters : List Nat) (position : Nat) : Prop :=
  ∃ guard,
    letters.count guard = 2 ∧
      guard ∈ letters.take position ∧
        guard ∈ letters.drop (position + 2)

private theorem splitAtValue
    {letters : List Nat} {position value : Nat}
    (atPosition : letters[position]? = some value) :
    letters =
      letters.take position ++ value :: letters.drop (position + 1) := by
  obtain ⟨inBounds, valueAtPosition⟩ :=
    List.getElem?_eq_some_iff.mp atPosition
  calc
    letters = letters.take position ++ letters.drop position :=
      (List.take_append_drop position letters).symm
    _ = letters.take position ++ value :: letters.drop (position + 1) := by
      congr 1
      simpa [valueAtPosition] using
        List.drop_eq_getElem_cons inBounds

private theorem splitAtAdjacentValues
    {letters : List Nat} {position first second : Nat}
    (firstAt : letters[position]? = some first)
    (secondAt : letters[position + 1]? = some second) :
    letters =
      letters.take position ++
        first :: second :: letters.drop (position + 2) := by
  obtain ⟨firstInBounds, firstValue⟩ :=
    List.getElem?_eq_some_iff.mp firstAt
  obtain ⟨secondInBounds, secondValue⟩ :=
    List.getElem?_eq_some_iff.mp secondAt
  have firstSplit :
      letters =
        letters.take position ++
          first :: letters.drop (position + 1) := by
    calc
      letters = letters.take position ++ letters.drop position :=
        (List.take_append_drop position letters).symm
      _ = letters.take position ++ first :: letters.drop (position + 1) := by
        congr 1
        simpa [firstValue] using
          List.drop_eq_getElem_cons firstInBounds
  have tailSplit :
      letters.drop (position + 1) =
        second :: letters.drop (position + 2) := by
    simpa [secondValue, Nat.add_assoc] using
      List.drop_eq_getElem_cons secondInBounds
  calc
    letters =
        letters.take position ++
          first :: letters.drop (position + 1) := firstSplit
    _ =
        letters.take position ++
          first :: second :: letters.drop (position + 2) := by
      rw [tailSplit]

private theorem separatorAbsentLeft
    {letters left right : List Nat} {separator : Nat}
    (split : letters = left ++ separator :: right)
    (countOne : letters.count separator = 1) :
    separator ∉ left := by
  intro member
  have positive : 0 < left.count separator :=
    List.count_pos_iff.mpr member
  rw [split, List.count_append, List.count_cons_self] at countOne
  omega

private theorem separatorSplitInjective
    {separator : Nat} :
    ∀ {left right leftTail rightTail : List Nat},
      separator ∉ left →
      separator ∉ right →
      left ++ separator :: leftTail =
        right ++ separator :: rightTail →
      left = right ∧ leftTail = rightTail
  | [], [], leftTail, rightTail, _, _, equality => by
      simpa using equality
  | [], rightHead :: right, leftTail, rightTail, _,
      separatorNotRight, equality => by
      have separatorNeRightHead : separator ≠ rightHead := by
        intro equal
        subst rightHead
        exact separatorNotRight (by simp)
      have headsEqual : separator = rightHead := by
        simpa using congrArg List.head? equality
      exact (separatorNeRightHead headsEqual).elim
  | leftHead :: left, [], leftTail, rightTail,
      separatorNotLeft, _, equality => by
      have separatorNeLeftHead : separator ≠ leftHead := by
        intro equal
        subst leftHead
        exact separatorNotLeft (by simp)
      have headsEqual : leftHead = separator := by
        simpa using congrArg List.head? equality
      exact (separatorNeLeftHead headsEqual.symm).elim
  | leftHead :: left, rightHead :: right, leftTail, rightTail,
      separatorNotLeft, separatorNotRight, equality => by
      have leftAbsence :
          separator ≠ leftHead ∧ separator ∉ left := by
        simpa only [List.mem_cons, not_or] using separatorNotLeft
      have rightAbsence :
          separator ≠ rightHead ∧ separator ∉ right := by
        simpa only [List.mem_cons, not_or] using separatorNotRight
      have consEquality :
          leftHead = rightHead ∧
            left ++ separator :: leftTail =
              right ++ separator :: rightTail := by
        simpa only [List.cons_append, List.cons.injEq] using equality
      rcases consEquality with ⟨rfl, tailEquality⟩
      have result :=
        separatorSplitInjective
          leftAbsence.2 rightAbsence.2 tailEquality
      exact
        ⟨congrArg (List.cons leftHead) result.1, result.2⟩

/-- A quadratic occurrence in the strict initial and another in the strict
suffix is exactly a guard for the intervening adjacent site. -/
theorem coveredAtOfQuadraticBridge
    {letters : List Nat} {position guard : Nat}
    (countTwo : letters.count guard = 2)
    (past : guard ∈ letters.take position)
    (future : guard ∈ letters.drop (position + 2)) :
    QuadraticGuardCoversAt letters position :=
  ⟨guard, countTwo, past, future⟩

/-- Target-initial extremality repairs the false mirror-coverage statement.

The source has `first x, simple e` at `position, position + 1`; the target has
already placed `e` at `position`, and both words have the same literal initial
before that position.  If no older quadratic interval covered the source
site, that initial would be disjoint from the target suffix, making `e` an
exact target separator.  Transporting this cut back forces the source initial
before `e` to omit `x`, contradicting the displayed first occurrence. -/
theorem prefixAlignedFirstSimpleCovered
    {left right : Word Nat} {position x e : Nat}
    (same : SameJointSignature left right)
    (leftTwo : ∀ tested, left.toList.count tested ≤ 2)
    (rightTwo : ∀ tested, right.toList.count tested ≤ 2)
    (prefixAligned :
      left.toList.take position = right.toList.take position)
    (xAt : left.toList[position]? = some x)
    (eAt : left.toList[position + 1]? = some e)
    (targetEAt : right.toList[position]? = some e)
    (xNoEarlier : x ∉ left.toList.take position)
    (eSimple : left.toList.count e = 1) :
    QuadraticGuardCoversAt left.toList position := by
  apply Classical.byContradiction
  intro covered
  have sourceShape := splitAtAdjacentValues xAt eAt
  have targetShape := splitAtValue targetEAt
  have targetECount : right.toList.count e = 1 := by
    rw [← reduced_count_eq_of_sameJointSignature
      same leftTwo rightTwo e]
    exact eSimple
  have targetDisjoint :
      SemigroupBasis.Examples.UniqueSeparatorFourSupportsDisjoint
        (right.toList.take position)
        (right.toList.drop (position + 1)) := by
    intro guard guardPast guardFuture
    have guardNeE : guard ≠ e := by
      intro equal
      subst guard
      have pastPositive :
          0 < (right.toList.take position).count e :=
        List.count_pos_iff.mpr guardPast
      have futurePositive :
          0 < (right.toList.drop (position + 1)).count e :=
        List.count_pos_iff.mpr guardFuture
      rw [targetShape, List.count_append,
        List.count_cons_self] at targetECount
      omega
    have targetGuardCount : right.toList.count guard = 2 := by
      have pastPositive :
          0 < (right.toList.take position).count guard :=
        List.count_pos_iff.mpr guardPast
      have futurePositive :
          0 < (right.toList.drop (position + 1)).count guard :=
        List.count_pos_iff.mpr guardFuture
      have bound := rightTwo guard
      rw [targetShape, List.count_append] at bound
      simp only [List.count_cons_of_ne (Ne.symm guardNeE)] at bound
      rw [targetShape, List.count_append]
      simp only [List.count_cons_of_ne (Ne.symm guardNeE)]
      omega
    have targetPastCount :
        (right.toList.take position).count guard = 1 := by
      have pastPositive :
          0 < (right.toList.take position).count guard :=
        List.count_pos_iff.mpr guardPast
      have futurePositive :
          0 < (right.toList.drop (position + 1)).count guard :=
        List.count_pos_iff.mpr guardFuture
      rw [targetShape, List.count_append] at targetGuardCount
      simp only [List.count_cons_of_ne (Ne.symm guardNeE)] at targetGuardCount
      omega
    have sourcePast : guard ∈ left.toList.take position := by
      rw [prefixAligned]
      exact guardPast
    have guardNeX : guard ≠ x := by
      intro equal
      subst guard
      exact xNoEarlier sourcePast
    have sourceGuardCount : left.toList.count guard = 2 := by
      exact
        (reduced_count_eq_of_sameJointSignature
          same leftTwo rightTwo guard).trans targetGuardCount
    have sourcePastCount :
        (left.toList.take position).count guard = 1 := by
      have counts := congrArg (List.count guard) prefixAligned
      exact counts.trans targetPastCount
    have sourceFuturePositive :
        0 < (left.toList.drop (position + 2)).count guard := by
      rw [sourceShape, List.count_append] at sourceGuardCount
      simp only [List.count_cons_of_ne (Ne.symm guardNeX),
        List.count_cons_of_ne (Ne.symm guardNeE)] at sourceGuardCount
      omega
    have sourceFuture :
        guard ∈ left.toList.drop (position + 2) :=
      List.count_pos_iff.mp sourceFuturePositive
    exact covered <|
      coveredAtOfQuadraticBridge
        sourceGuardCount sourcePast sourceFuture
  have targetCut :
      SemigroupBasis.Examples.UniqueSeparatorFourExactCut
        right.toList (right.toList.take position) e
          (right.toList.drop (position + 1)) :=
    ⟨targetShape, targetECount, targetDisjoint⟩
  have targetSignature :
      SemigroupBasis.CoRoots.S5_378.ExactCutSignature
        right e (right.toList.take position)
          (right.toList.drop (position + 1)) :=
    ⟨right.toList.take position,
      right.toList.drop (position + 1), targetCut,
      fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  have sourceSignature :
      SemigroupBasis.CoRoots.S5_378.ExactCutSignature
        left e (right.toList.take position)
          (right.toList.drop (position + 1)) :=
    (same.separator.exactCuts e
      (right.toList.take position)
      (right.toList.drop (position + 1))).mpr targetSignature
  obtain
    ⟨sourceLeft, sourceRight, sourceCut,
      sourceLeftSupport, _sourceRightSupport⟩ := sourceSignature
  have sourceKnownSplit :
      left.toList =
        (left.toList.take position ++ [x]) ++
          e :: left.toList.drop (position + 2) := by
    simpa [List.append_assoc] using sourceShape
  have knownLeftAbsent :
      e ∉ left.toList.take position ++ [x] :=
    separatorAbsentLeft sourceKnownSplit eSimple
  have cutLeftAbsent : e ∉ sourceLeft :=
    separatorAbsentLeft sourceCut.1 sourceCut.2.1
  have cutSides :=
    separatorSplitInjective
      knownLeftAbsent cutLeftAbsent
      (sourceKnownSplit.symm.trans sourceCut.1)
  have xInSourceLeft : x ∈ sourceLeft := by
    rw [← cutSides.1]
    simp
  have xInTargetPrefix : x ∈ right.toList.take position :=
    (sourceLeftSupport x).mp xInSourceLeft
  have xInSourcePrefix : x ∈ left.toList.take position := by
    rw [prefixAligned]
    exact xInTargetPrefix
  exact xNoEarlier xInSourcePrefix

private theorem listDerivesOfSourceEq
    {source displayed target : List Nat}
    (shape : source = displayed)
    (listed : ListDerives displayed target) :
    ListDerives source target := by
  subst displayed
  exact listed

/-- Direct derivation of the final occurrence-resolved `first, simple`
crossing.  Unlike the retired `bubble_step`, this statement uses no raw
first-occurrence comparison: the source occurrence is specified by its
literal position and strict-initial role, and the target occurrence is at the
already aligned initial boundary. -/
theorem listDerivesPrefixAlignedFirstSimpleSwap
    {left right : Word Nat} {position x e : Nat}
    (same : SameJointSignature left right)
    (leftTwo : ∀ tested, left.toList.count tested ≤ 2)
    (rightTwo : ∀ tested, right.toList.count tested ≤ 2)
    (prefixAligned :
      left.toList.take position = right.toList.take position)
    (xAt : left.toList[position]? = some x)
    (eAt : left.toList[position + 1]? = some e)
    (targetEAt : right.toList[position]? = some e)
    (xNoEarlier : x ∉ left.toList.take position)
    (xFuture : x ∈ left.toList.drop (position + 2))
    (eSimple : left.toList.count e = 1) :
    ListDerives left.toList
      (left.toList.take position ++
        e :: x :: left.toList.drop (position + 2)) := by
  obtain ⟨guard, _guardCount, guardPast, guardFuture⟩ :=
    prefixAlignedFirstSimpleCovered
      same leftTwo rightTwo prefixAligned
      xAt eAt targetEAt xNoEarlier eSimple
  have localSwap :=
    listDerivesCoveredFirstSimpleSwap
      (left.toList.take position)
      (left.toList.drop (position + 2))
      guard e x guardPast guardFuture xFuture
  exact
    listDerivesOfSourceEq
      (splitAtAdjacentValues xAt eAt) localSwap

/-! ## Derivational move calculus -/

/-- The primitive move families needed by the target-head normalizer after
count reduction.  Every constructor is a purely list-theoretic certificate. -/
inductive ReducedJointStep : List Nat → List Nat → Prop
  | quadratic
      (initial suffix : List Nat) (x y : Nat)
      (different : x ≠ y)
      (xCount : (initial ++ x :: y :: suffix).count x = 2)
      (yCount : (initial ++ x :: y :: suffix).count y = 2) :
      ReducedJointStep
        (initial ++ x :: y :: suffix)
        (initial ++ y :: x :: suffix)
  | coveredSimpleFirst
      (initial suffix : List Nat) (guard simple first : Nat)
      (guardPast : guard ∈ initial)
      (guardFuture : guard ∈ suffix)
      (firstFuture : first ∈ suffix) :
      ReducedJointStep
        (initial ++ simple :: first :: suffix)
        (initial ++ first :: simple :: suffix)
  | coveredFirstSimple
      (initial suffix : List Nat) (guard simple first : Nat)
      (guardPast : guard ∈ initial)
      (guardFuture : guard ∈ suffix)
      (firstFuture : first ∈ suffix) :
      ReducedJointStep
        (initial ++ first :: simple :: suffix)
        (initial ++ simple :: first :: suffix)

private theorem reducedJointStepOfSourceEq
    {source displayed target : List Nat}
    (shape : source = displayed)
    (step : ReducedJointStep displayed target) :
    ReducedJointStep source target := by
  subst displayed
  exact step

/-- The exact-cut final crossing is an edge of the corrected reduced move
calculus, not merely an isolated derivation. -/
theorem reducedJointStepPrefixAlignedFirstSimple
    {left right : Word Nat} {position x e : Nat}
    (same : SameJointSignature left right)
    (leftTwo : ∀ tested, left.toList.count tested ≤ 2)
    (rightTwo : ∀ tested, right.toList.count tested ≤ 2)
    (prefixAligned :
      left.toList.take position = right.toList.take position)
    (xAt : left.toList[position]? = some x)
    (eAt : left.toList[position + 1]? = some e)
    (targetEAt : right.toList[position]? = some e)
    (xNoEarlier : x ∉ left.toList.take position)
    (xFuture : x ∈ left.toList.drop (position + 2))
    (eSimple : left.toList.count e = 1) :
    ReducedJointStep left.toList
      (left.toList.take position ++
        e :: x :: left.toList.drop (position + 2)) := by
  obtain ⟨guard, _guardCount, guardPast, guardFuture⟩ :=
    prefixAlignedFirstSimpleCovered
      same leftTwo rightTwo prefixAligned
      xAt eAt targetEAt xNoEarlier eSimple
  exact
    reducedJointStepOfSourceEq
      (splitAtAdjacentValues xAt eAt) <|
        .coveredFirstSimple
          (left.toList.take position)
          (left.toList.drop (position + 2))
          guard e x guardPast guardFuture xFuture

/-- Every certified reduced move is realized by the displayed fourteen laws. -/
theorem listDerivesOfReducedJointStep
    {source target : List Nat}
    (step : ReducedJointStep source target) :
    ListDerives source target := by
  cases step with
  | quadratic initial suffix x y different xCount yCount =>
      exact
        listDerivesAdjacentQuadraticSwap
          different xCount yCount
  | coveredSimpleFirst initial suffix guard simple first
      guardPast guardFuture firstFuture =>
      exact
        listDerivesCoveredSimpleFirstSwap
          initial suffix guard simple first
          guardPast guardFuture firstFuture
  | coveredFirstSimple initial suffix guard simple first
      guardPast guardFuture firstFuture =>
      exact
        listDerivesCoveredFirstSimpleSwap
          initial suffix guard simple first
          guardPast guardFuture firstFuture

/-- A target-directed path whose every nontrivial edge swaps the literal
adjacent occurrences selected by the corrected first/last roles.  The
`inverted` field prevents a proof from silently falling back to a raw
letter-level `idxOf` comparison. -/
inductive OccurrenceResolvedReducedJointClosure
    (target : List Nat) : List Nat → Prop
  | refl :
      OccurrenceResolvedReducedJointClosure target target
  | cons {source next : List Nat} {position x e : Nat}
      (inverted :
        OccurrenceResolvedAdjacentInversionAt
          source target position x e)
      (nextShape :
        next = source.take position ++
          e :: x :: source.drop (position + 2))
      (step : ReducedJointStep source next)
      (rest : OccurrenceResolvedReducedJointClosure target next) :
      OccurrenceResolvedReducedJointClosure target source

/-- The occurrence-resolved move calculus contains no unverified equational
edge.  Event-direction data guide the schedule; derivability comes only from
the three sound `ReducedJointStep` constructors. -/
theorem listDerivesOfOccurrenceResolvedReducedJointClosure
    {source target : List Nat}
    (closure : OccurrenceResolvedReducedJointClosure target source) :
    ListDerives source target := by
  induction closure with
  | refl =>
      exact S5_107.ListDerives.refl target
  | cons inverted nextShape step rest inductionHypothesis =>
      exact
        (listDerivesOfReducedJointStep step).trans
          inductionHypothesis

private theorem wordDerivesOfListDerives
    {left right : Word Nat}
    (listed : ListDerives left.toList right.toList) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [S5_107.listWordOfCons, Word.toList] using
            S5_107.ListDerives.toWord listed

/-- The first exact unresolved theorem after the durable local mathematics:
the target-head schedule must use the occurrence-selected order at every
edge, and only quadratic or covered simple/first swaps.  It is a statement
over unrestricted natural-number words; no bounded alphabet or length
appears. -/
def OccurrenceResolvedTargetHeadConnectivity : Prop :=
  ∀ {left right : Word Nat},
    SameJointSignature left right →
      (∀ tested, left.toList.count tested ≤ 2) →
        (∀ tested, right.toList.count tested ≤ 2) →
          OccurrenceResolvedReducedJointClosure
            right.toList left.toList

/-- A proof of the pure reduced move-scheduling theorem yields the requested
unrestricted joint-signature canonicalization.  Count reduction is derivable
and preserves the complete joint signature on both sides. -/
theorem jointSignatureCanonicalizationOfOccurrenceResolvedConnectivity
    (connect : OccurrenceResolvedTargetHeadConnectivity) :
    JointSignatureCanonicalization := by
  intro left right _leftLong _rightLong same
  have reduced := countReducedPair same
  have middleClosure :=
    connect reduced.reducedSame
      reduced.leftTwoLimited reduced.rightTwoLimited
  have middleDerivation :
      Derives basis
        (countReducedWord left) (countReducedWord right) :=
    wordDerivesOfListDerives
      (listDerivesOfOccurrenceResolvedReducedJointClosure
        middleClosure)
  exact
    reduced.leftDerives.trans <|
      middleDerivation.trans reduced.rightDerives.symm

end SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

import SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw
import SemigroupBasis.CoRoots.S5_794Family

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

/-- Evaluation in the left regular band, with its identity adjoined only for
the purpose of evaluating a possibly empty list. -/
def initialListEval
    (valuation : Nat → Fin 3) (letters : List Nat) : Fin 3 :=
  letters.foldl
    (fun current letter =>
      leftRegularBandThreeMul current (valuation letter)) 1

/-- Evaluation in the right regular band. This records the last nonidentity
marker in a possibly empty list. -/
def finalListEval
    (valuation : Nat → Fin 3) (letters : List Nat) : Fin 3 :=
  letters.foldl
    (fun current letter =>
      leftRegularBandThreeMul (valuation letter) current) 1

private theorem initialEval_eq_listEval
    (valuation : Nat → Fin 3) (word : Word Nat) :
    SemigroupBasis.Generated.S3_16.table.semigroup.eval valuation word =
      initialListEval valuation word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              leftRegularBandThreeMul current (valuation letter))
            (valuation head) =
          tail.foldl
            (fun current letter =>
              leftRegularBandThreeMul current (valuation letter))
            (leftRegularBandThreeMul 1 (valuation head))
      rw [show leftRegularBandThreeMul 1 (valuation head) =
          valuation head by
        simp [leftRegularBandThreeMul]]

private theorem finalEval_eq_listEval
    (valuation : Nat → Fin 3) (word : Word Nat) :
    rightRegularBandThreeTable.semigroup.eval valuation word =
      finalListEval valuation word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              leftRegularBandThreeMul (valuation letter) current)
            (valuation head) =
          tail.foldl
            (fun current letter =>
              leftRegularBandThreeMul (valuation letter) current)
            (leftRegularBandThreeMul (valuation head) 1)
      rw [show leftRegularBandThreeMul (valuation head) 1 =
          valuation head by
        have rightIdentity :
            ∀ value : Fin 3,
              leftRegularBandThreeMul value 1 = value := by
          decide
        exact rightIdentity (valuation head)]

/-- Exact unrestricted endpoint equivalence: equality under every valuation
in both the left and right three-element regular bands. -/
structure EndpointEquivalent (left right : List Nat) : Prop where
  initial :
    ∀ valuation,
      initialListEval valuation left =
        initialListEval valuation right
  final :
    ∀ valuation,
      finalListEval valuation left =
        finalListEval valuation right

namespace EndpointEquivalent

theorem refl (letters : List Nat) :
    EndpointEquivalent letters letters :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem symm {left right : List Nat}
    (equivalent : EndpointEquivalent left right) :
    EndpointEquivalent right left :=
  ⟨fun valuation => (equivalent.initial valuation).symm,
    fun valuation => (equivalent.final valuation).symm⟩

theorem trans {left middle right : List Nat}
    (first : EndpointEquivalent left middle)
    (second : EndpointEquivalent middle right) :
    EndpointEquivalent left right :=
  ⟨fun valuation =>
      (first.initial valuation).trans (second.initial valuation),
    fun valuation =>
      (first.final valuation).trans (second.final valuation)⟩

theorem ofDerives {left right : List Nat}
    (derivation : ListDerives left right) :
    EndpointEquivalent left right := by
  cases derivation with
  | empty =>
      exact refl []
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      constructor
      · intro valuation
        have sound :=
          wordDerivation.sound modelsS3_16 valuation
        simpa only [initialEval_eq_listEval] using sound
      · intro valuation
        have sound :=
          wordDerivation.sound modelsRightRegularBandThree valuation
        simpa only [finalEval_eq_listEval] using sound

end EndpointEquivalent

private def pairValuation (x y : Nat) : Nat → Fin 3 :=
  fun letter => if letter = x then 0 else if letter = y then 2 else 1

@[simp]
private theorem pairValuation_x (x y : Nat) :
    pairValuation x y x = 0 := by
  simp [pairValuation]

@[simp]
private theorem pairValuation_y {x y : Nat} (different : x ≠ y) :
    pairValuation x y y = 2 := by
  simp [pairValuation, Ne.symm different]

private theorem initialFold_zero (x y : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            leftRegularBandThreeMul current
              (pairValuation x y letter)) 0 = 0
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show
        leftRegularBandThreeMul 0 (pairValuation x y letter) = 0 by
          simp [leftRegularBandThreeMul]]
      exact initialFold_zero x y rest

private theorem initialFold_two (x y : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            leftRegularBandThreeMul current
              (pairValuation x y letter)) 2 = 2
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show
        leftRegularBandThreeMul 2 (pairValuation x y letter) = 2 by
          simp [leftRegularBandThreeMul]]
      exact initialFold_two x y rest

private theorem initialFold_identity_of_absent
    (x y : Nat) :
    ∀ initial : List Nat,
      x ∉ initial →
      y ∉ initial →
      initial.foldl
          (fun current letter =>
            leftRegularBandThreeMul current
              (pairValuation x y letter)) 1 = 1
  | [], _, _ => rfl
  | letter :: rest, xAbsent, yAbsent => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact xAbsent (List.Mem.head rest)
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact yAbsent (List.Mem.head rest)
      have restXAbsent : x ∉ rest :=
        fun member => xAbsent (List.Mem.tail letter member)
      have restYAbsent : y ∉ rest :=
        fun member => yAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show pairValuation x y letter = 1 by
        simp [pairValuation, letterNeX, letterNeY]]
      rw [show leftRegularBandThreeMul 1 1 = 1 by decide]
      exact initialFold_identity_of_absent x y rest
        restXAbsent restYAbsent

private theorem initialEval_firstX
    {x y : Nat} (different : x ≠ y)
    (initial rest : List Nat)
    (xAbsent : x ∉ initial) (yAbsent : y ∉ initial) :
    initialListEval (pairValuation x y) (initial ++ x :: rest) = 0 := by
  unfold initialListEval
  rw [List.foldl_append]
  rw [initialFold_identity_of_absent x y initial xAbsent yAbsent]
  simp only [List.foldl_cons]
  rw [pairValuation_x]
  rw [show leftRegularBandThreeMul 1 0 = 0 by decide]
  exact initialFold_zero x y rest

private theorem initialEval_firstY
    {x y : Nat} (different : x ≠ y)
    (initial rest : List Nat)
    (xAbsent : x ∉ initial) (yAbsent : y ∉ initial) :
    initialListEval (pairValuation x y) (initial ++ y :: rest) = 2 := by
  unfold initialListEval
  rw [List.foldl_append]
  rw [initialFold_identity_of_absent x y initial xAbsent yAbsent]
  simp only [List.foldl_cons]
  rw [pairValuation_y different]
  rw [show leftRegularBandThreeMul 1 2 = 2 by decide]
  exact initialFold_two x y rest

private theorem finalFold_identity_of_absent
    (x y : Nat) :
    ∀ letters : List Nat, ∀ current : Fin 3,
      x ∉ letters →
      y ∉ letters →
      letters.foldl
          (fun accumulated letter =>
            leftRegularBandThreeMul
              (pairValuation x y letter) accumulated) current = current
  | [], current, _, _ => rfl
  | letter :: rest, current, xAbsent, yAbsent => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact xAbsent (List.Mem.head rest)
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact yAbsent (List.Mem.head rest)
      have restXAbsent : x ∉ rest :=
        fun member => xAbsent (List.Mem.tail letter member)
      have restYAbsent : y ∉ rest :=
        fun member => yAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show pairValuation x y letter = 1 by
        simp [pairValuation, letterNeX, letterNeY]]
      rw [show leftRegularBandThreeMul 1 current = current by
        simp [leftRegularBandThreeMul]]
      exact finalFold_identity_of_absent x y rest current
        restXAbsent restYAbsent

private theorem finalFold_zero_of_y_absent
    {x y : Nat} (different : x ≠ y) :
    ∀ letters : List Nat,
      y ∉ letters →
      letters.foldl
          (fun current letter =>
            leftRegularBandThreeMul
              (pairValuation x y letter) current) 0 = 0
  | [], _ => rfl
  | letter :: rest, yAbsent => by
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact yAbsent (List.Mem.head rest)
      have restYAbsent : y ∉ rest :=
        fun member => yAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases letterX : letter = x
      · subst letter
        rw [pairValuation_x]
        rw [show leftRegularBandThreeMul 0 0 = 0 by decide]
        exact
          finalFold_zero_of_y_absent different rest restYAbsent
      · rw [show pairValuation x y letter = 1 by
          simp [pairValuation, letterX, letterNeY]]
        rw [show leftRegularBandThreeMul 1 0 = 0 by decide]
        exact
          finalFold_zero_of_y_absent different rest restYAbsent

private theorem finalEval_lastY
    {x y : Nat} (different : x ≠ y)
    (initial rest : List Nat)
    (xAbsent : x ∉ rest) (yAbsent : y ∉ rest) :
    finalListEval (pairValuation x y)
        (initial ++ y :: rest) = 2 := by
  unfold finalListEval
  rw [List.foldl_append]
  simp only [List.foldl_cons]
  rw [pairValuation_y different]
  rw [show leftRegularBandThreeMul 2
      (initial.foldl
        (fun current letter =>
          leftRegularBandThreeMul
            (pairValuation x y letter) current) 1) = 2 by
    simp [leftRegularBandThreeMul]]
  exact finalFold_identity_of_absent x y rest 2 xAbsent yAbsent

private theorem finalEval_xAfterY
    {x y : Nat} (different : x ≠ y)
    (initial targetTail : List Nat)
    (xPresent : x ∈ targetTail)
    (yAbsent : y ∉ targetTail) :
    finalListEval (pairValuation x y)
        (initial ++ y :: targetTail) = 0 := by
  rcases List.append_of_mem xPresent with
    ⟨before, after, targetShape⟩
  have yAbsentAfter : y ∉ after := by
    intro member
    apply yAbsent
    rw [targetShape]
    simp [member]
  unfold finalListEval
  rw [targetShape, List.foldl_append]
  simp only [List.foldl_cons]
  rw [List.foldl_append]
  simp only [List.foldl_cons]
  rw [pairValuation_x]
  rw [show leftRegularBandThreeMul 0
      ((before.foldl
        (fun current letter =>
          leftRegularBandThreeMul
            (pairValuation x y letter) current)
        (leftRegularBandThreeMul
          (pairValuation x y y)
          ((initial.foldl
            (fun current letter =>
              leftRegularBandThreeMul
                (pairValuation x y letter) current) 1))))) = 0 by
    simp [leftRegularBandThreeMul]]
  exact finalFold_zero_of_y_absent different after yAbsentAfter

private theorem seen_of_equivalent_target_head
    {fixedPrefix crossed rest targetTail : List Nat}
    {x y : Nat}
    (different : x ≠ y)
    (equivalent :
      EndpointEquivalent
        (fixedPrefix ++ crossed ++ x :: y :: rest)
        (fixedPrefix ++ y :: targetTail)) :
    x ∈ fixedPrefix ++ crossed ∨
      y ∈ fixedPrefix ++ crossed := by
  by_cases xSeen : x ∈ fixedPrefix ++ crossed
  · exact Or.inl xSeen
  · by_cases ySeen : y ∈ fixedPrefix ++ crossed
    · exact Or.inr ySeen
    · have xAbsentFixed : x ∉ fixedPrefix :=
        fun member =>
          xSeen (List.mem_append_left crossed member)
      have yAbsentFixed : y ∉ fixedPrefix :=
        fun member =>
          ySeen (List.mem_append_left crossed member)
      have evaluated := equivalent.initial (pairValuation x y)
      rw [show
            fixedPrefix ++ crossed ++ x :: y :: rest =
              (fixedPrefix ++ crossed) ++ x :: (y :: rest) by
            simp [List.append_assoc],
          initialEval_firstX different
            (fixedPrefix ++ crossed) (y :: rest) xSeen ySeen,
          initialEval_firstY different
            fixedPrefix targetTail xAbsentFixed yAbsentFixed] at evaluated
      exact False.elim ((by decide : (0 : Fin 3) ≠ 2) evaluated)

private theorem future_of_equivalent_target_head
    {fixedPrefix crossed rest targetTail : List Nat}
    {x y : Nat}
    (different : x ≠ y)
    (yNotCrossed : y ∉ crossed)
    (remainingPermutation :
      (crossed ++ x :: rest).Perm targetTail)
    (equivalent :
      EndpointEquivalent
        (fixedPrefix ++ crossed ++ x :: y :: rest)
        (fixedPrefix ++ y :: targetTail)) :
    x ∈ rest ∨ y ∈ rest := by
  by_cases xFuture : x ∈ rest
  · exact Or.inl xFuture
  · by_cases yFuture : y ∈ rest
    · exact Or.inr yFuture
    · have xInTarget : x ∈ targetTail :=
        remainingPermutation.mem_iff.mp <| by
          simp
      have yNotTarget : y ∉ targetTail := by
        intro targetMember
        have sourceMember :=
          remainingPermutation.mem_iff.mpr targetMember
        simp [yNotCrossed, Ne.symm different, yFuture] at sourceMember
      have evaluated := equivalent.final (pairValuation x y)
      rw [show
            fixedPrefix ++ crossed ++ x :: y :: rest =
              (fixedPrefix ++ crossed ++ [x]) ++ y :: rest by
            simp [List.append_assoc],
          finalEval_lastY different
            (fixedPrefix ++ crossed ++ [x]) rest xFuture yFuture,
          finalEval_xAfterY different
            fixedPrefix targetTail xInTarget yNotTarget] at evaluated
      exact False.elim ((by decide : (2 : Fin 3) ≠ 0) evaluated)

private theorem listDerivesAdjacentStraddle
    {x y : Nat} {pre post : List Nat}
    (different : x ≠ y)
    (limited : UniqueSeparatorTwoLimited (pre ++ x :: y :: post))
    (seen : x ∈ pre ∨ y ∈ pre)
    (future : x ∈ post ∨ y ∈ post) :
    ListDerives
      (pre ++ x :: y :: post)
      (pre ++ y :: x :: post) := by
  rcases seen with xSeen | ySeen
  · rcases future with xFuture | yFuture
    · have prePositive : 1 ≤ pre.count x :=
        List.one_le_count_iff.mpr xSeen
      have postPositive : 1 ≤ post.count x :=
        List.one_le_count_iff.mpr xFuture
      have bound := limited x
      simp only [List.count_append, List.count_cons_self,
        List.count_cons_of_ne (Ne.symm different)] at bound
      omega
    · rcases List.append_of_mem xSeen with
        ⟨before, left, preShape⟩
      rcases List.append_of_mem yFuture with
        ⟨right, after, postShape⟩
      rw [preShape, postShape]
      simpa [List.append_assoc] using
        (listDerivesL7 x y left right).symm.context before after
  · rcases future with xFuture | yFuture
    · rcases List.append_of_mem ySeen with
        ⟨before, left, preShape⟩
      rcases List.append_of_mem xFuture with
        ⟨right, after, postShape⟩
      rw [preShape, postShape]
      simpa [List.append_assoc] using
        (listDerivesL7 y x left right).context before after
    · have prePositive : 1 ≤ pre.count y :=
        List.one_le_count_iff.mpr ySeen
      have postPositive : 1 ≤ post.count y :=
        List.one_le_count_iff.mpr yFuture
      have bound := limited y
      simp only [List.count_append,
        List.count_cons_of_ne different, List.count_cons_self] at bound
      omega

private theorem listDerivesMoveMemberToFront
    (fixedPrefix targetTail : List Nat) (selected : Nat) :
    ∀ (crossed source : List Nat),
      selected ∉ crossed →
      (crossed ++ source).Perm (selected :: targetTail) →
      UniqueSeparatorTwoLimited
        (fixedPrefix ++ crossed ++ source) →
      EndpointEquivalent
        (fixedPrefix ++ crossed ++ source)
        (fixedPrefix ++ selected :: targetTail) →
      ListDerives
        (fixedPrefix ++ crossed ++ source)
        (fixedPrefix ++ crossed ++
          selected :: source.erase selected)
  | crossed, [], selectedNotCrossed, permutation, _, _ => by
      have selectedInCrossed : selected ∈ crossed := by
        simpa using
          permutation.mem_iff.mpr (List.Mem.head targetTail)
      exact False.elim (selectedNotCrossed selectedInCrossed)
  | crossed, head :: tail, selectedNotCrossed, permutation,
      limited, equivalent => by
      by_cases equal : head = selected
      · subst head
        simpa [selectedNotCrossed] using
          SemigroupBasis.CoRoots.S5_107.ListDerives.refl
            (basis := basis)
            (fixedPrefix ++ crossed ++ selected :: tail)
      · have selectedInTail : selected ∈ tail := by
          have selectedInWhole :
              selected ∈ crossed ++ head :: tail :=
            permutation.mem_iff.mpr (by simp)
          simpa [selectedNotCrossed, Ne.symm equal] using
            selectedInWhole
        have selectedNotNextCrossed :
            selected ∉ crossed ++ [head] := by
          simp [selectedNotCrossed, Ne.symm equal]
        have nextPermutation :
            ((crossed ++ [head]) ++ tail).Perm
              (selected :: targetTail) := by
          simpa [List.append_assoc] using permutation
        have nextLimited :
            UniqueSeparatorTwoLimited
              (fixedPrefix ++ (crossed ++ [head]) ++ tail) := by
          simpa [List.append_assoc] using limited
        have nextEquivalent :
            EndpointEquivalent
              (fixedPrefix ++ (crossed ++ [head]) ++ tail)
              (fixedPrefix ++ selected :: targetTail) := by
          simpa [List.append_assoc] using equivalent
        have moveTail :=
          listDerivesMoveMemberToFront
            fixedPrefix targetTail selected
            (crossed ++ [head]) tail
            selectedNotNextCrossed nextPermutation
            nextLimited nextEquivalent
        have movedEquivalent :
            EndpointEquivalent
              (fixedPrefix ++ crossed ++
                head :: selected :: tail.erase selected)
              (fixedPrefix ++ selected :: targetTail) := by
          have sound := EndpointEquivalent.ofDerives moveTail
          exact by
            simpa [List.append_assoc] using
              sound.symm.trans nextEquivalent
        have tailExpose :
            tail.Perm (selected :: tail.erase selected) :=
          List.perm_cons_erase selectedInTail
        have blockExpose :
            (head :: tail).Perm
              (head :: selected :: tail.erase selected) :=
          List.Perm.cons head tailExpose
        have wholeExpose :
            (fixedPrefix ++ crossed ++ head :: tail).Perm
              (fixedPrefix ++ crossed ++
                head :: selected :: tail.erase selected) :=
          List.Perm.append_left (fixedPrefix ++ crossed) blockExpose
        have movedLimited :
            UniqueSeparatorTwoLimited
              (fixedPrefix ++ crossed ++
                head :: selected :: tail.erase selected) := by
          intro letter
          calc
            (fixedPrefix ++ crossed ++
                head :: selected :: tail.erase selected).count letter =
                (fixedPrefix ++ crossed ++ head :: tail).count letter := by
              exact (wholeExpose.count letter).symm
            _ ≤ 2 := by
              simpa [List.append_assoc] using limited letter
        have remainingPermutation :
            (crossed ++ head :: tail.erase selected).Perm targetTail := by
          simpa [List.erase_append, selectedNotCrossed,
            equal] using permutation.erase selected
        have seen :
            head ∈ fixedPrefix ++ crossed ∨
              selected ∈ fixedPrefix ++ crossed :=
          seen_of_equivalent_target_head equal movedEquivalent
        have future :
            head ∈ tail.erase selected ∨
              selected ∈ tail.erase selected :=
          future_of_equivalent_target_head
            equal selectedNotCrossed remainingPermutation movedEquivalent
        have swap :=
          listDerivesAdjacentStraddle
            (pre := fixedPrefix ++ crossed)
            (post := tail.erase selected)
            equal
            (by simpa [List.append_assoc] using movedLimited)
            seen future
        have complete := moveTail.trans <| by
          simpa [List.append_assoc] using swap
        simpa [equal, List.append_assoc] using complete
termination_by
  _ source => source.length

private theorem listDerivesCappedAgainst :
    ∀ (target source fixedPrefix : List Nat),
      source.Perm target →
      UniqueSeparatorTwoLimited (fixedPrefix ++ source) →
      EndpointEquivalent
        (fixedPrefix ++ source) (fixedPrefix ++ target) →
      ListDerives
        (fixedPrefix ++ source) (fixedPrefix ++ target)
  | [], source, fixedPrefix, permutation, _, _ => by
      have sourceEmpty : source = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using permutation.length_eq
      subst source
      exact
        SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) _
  | selected :: targetTail, source, fixedPrefix,
      permutation, limited, equivalent => by
      have selectedInSource : selected ∈ source :=
        permutation.mem_iff.mpr (by simp)
      have move :=
        listDerivesMoveMemberToFront
          fixedPrefix targetTail selected [] source
          (by simp) (by simpa using permutation)
          (by simpa using limited) (by simpa using equivalent)
      have sourceExpose :
          source.Perm (selected :: source.erase selected) :=
        List.perm_cons_erase selectedInSource
      have wholeExpose :
          (fixedPrefix ++ source).Perm
            ((fixedPrefix ++ [selected]) ++ source.erase selected) := by
        simpa [List.append_assoc] using
          List.Perm.append_left fixedPrefix sourceExpose
      have erasedPermutation :
          (source.erase selected).Perm targetTail := by
        simpa using permutation.erase selected
      have exposedLimited :
          UniqueSeparatorTwoLimited
            ((fixedPrefix ++ [selected]) ++ source.erase selected) := by
        intro letter
        calc
          ((fixedPrefix ++ [selected]) ++ source.erase selected).count
                letter =
              (fixedPrefix ++ source).count letter := by
            exact (wholeExpose.count letter).symm
          _ ≤ 2 := limited letter
      have exposedEquivalent :
          EndpointEquivalent
            ((fixedPrefix ++ [selected]) ++ source.erase selected)
            ((fixedPrefix ++ [selected]) ++ targetTail) := by
        have sound := EndpointEquivalent.ofDerives move
        have normalizedEquivalent :
            EndpointEquivalent
              (fixedPrefix ++ [] ++ source)
              (fixedPrefix ++ selected :: targetTail) := by
          simpa using equivalent
        have exposedToTarget :=
          sound.symm.trans normalizedEquivalent
        simpa [List.append_assoc] using exposedToTarget
      have rest :=
        listDerivesCappedAgainst
          targetTail (source.erase selected) (fixedPrefix ++ [selected])
          erasedPermutation exposedLimited exposedEquivalent
      have complete := move.trans <| by
          simpa [List.append_assoc] using rest
      simpa [List.append_assoc] using complete
termination_by
  target _ _ => target.length

/-- Two capped lists with the same multiplicities and exact initial/final
semantics derive one another from the seven laws. -/
theorem listDerivesCapped
    (left right : List Nat)
    (leftLimited : UniqueSeparatorTwoLimited left)
    (counts : ∀ letter, left.count letter = right.count letter)
    (equivalent : EndpointEquivalent left right) :
    ListDerives left right := by
  have permutation : left.Perm right := by
    rw [List.perm_iff_count]
    exact counts
  simpa using
    listDerivesCappedAgainst right left [] permutation
      (by simpa using leftLimited) (by simpa using equivalent)

/-- The exact invariant package supplied by the two lower-order factors. -/
structure CappedEndpointInvariant (identity : Identity Nat) : Prop where
  endpoints :
    EndpointEquivalent identity.lhs.toList identity.rhs.toList
  cappedCounts :
    ∀ letter,
      min (identity.lhs.toList.count letter) 2 =
        min (identity.rhs.toList.count letter) 2

/-- Public semantic entry point for the shared normalizer.  The left regular
band records first occurrences, the right regular band records last
occurrences, and the commutative exponent-three detector records
multiplicities capped at two.  Factor-specific modules can establish these
three detector identities through any complete lower-order presentation. -/
theorem invariantOfDetectorValid
    (identity : Identity Nat)
    (initialValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup)
    (finalValid :
      identity.SatisfiedBy rightRegularBandThreeTable.semigroup)
    (countValid :
      identity.SatisfiedBy commutativeExponentThree.semigroup) :
    CappedEndpointInvariant identity := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro valuation
      have evaluated := initialValid valuation
      simpa only [initialEval_eq_listEval] using evaluated
    · intro valuation
      have evaluated := finalValid valuation
      simpa only [finalEval_eq_listEval] using evaluated
  · exact exponentValid_capped_count_eq identity countValid

/-- Unrestricted completeness of the seven laws from the endpoint/capped-count
invariant. No bounded identity inventory is used. -/
theorem derivesOfInvariant
    (identity : Identity Nat)
    (invariant : CappedEndpointInvariant identity) :
    Derives basis identity.lhs identity.rhs := by
  have leftListDerivation :=
    listDerivesEndpointCap identity.lhs.toList
  have rightListDerivation :=
    listDerivesEndpointCap identity.rhs.toList
  cases identity with
  | mk left right =>
      obtain
        ⟨leftCapHead, leftCapTail, leftCapShape,
          leftCapDerivation⟩ :=
        leftListDerivation.from_cons
      obtain
        ⟨rightCapHead, rightCapTail, rightCapShape,
          rightCapDerivation⟩ :=
        rightListDerivation.from_cons
      let leftCap : Word Nat :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons
          leftCapHead leftCapTail
      let rightCap : Word Nat :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons
          rightCapHead rightCapTail
      have leftCapToList :
          leftCap.toList =
            uniqueSeparatorEndpointCap left.toList := by
        simpa [leftCap,
          SemigroupBasis.CoRoots.S5_107.listWordOfCons,
          Word.toList] using leftCapShape.symm
      have rightCapToList :
          rightCap.toList =
            uniqueSeparatorEndpointCap right.toList := by
        simpa [rightCap,
          SemigroupBasis.CoRoots.S5_107.listWordOfCons,
          Word.toList] using rightCapShape.symm
      have capCounts :
          ∀ letter,
            leftCap.toList.count letter =
              rightCap.toList.count letter := by
        intro letter
        rw [leftCapToList, rightCapToList,
          uniqueSeparatorEndpointCap_count,
          uniqueSeparatorEndpointCap_count]
        simpa [Nat.min_comm] using invariant.cappedCounts letter
      have leftLimited :
          UniqueSeparatorTwoLimited leftCap.toList := by
        rw [leftCapToList]
        exact uniqueSeparatorEndpointCap_twoLimited left.toList
      have capEquivalent :
          EndpointEquivalent leftCap.toList rightCap.toList := by
        rw [leftCapToList, rightCapToList]
        exact
          (EndpointEquivalent.ofDerives leftListDerivation).symm.trans
            (invariant.endpoints.trans
              (EndpointEquivalent.ofDerives rightListDerivation))
      have capListDerivation :=
        listDerivesCapped leftCap.toList rightCap.toList
          leftLimited capCounts capEquivalent
      have capWordDerivation :
          Derives basis leftCap rightCap := by
        have represented :
            ListDerives
              (leftCapHead :: leftCapTail)
              (rightCapHead :: rightCapTail) := by
          simpa [leftCap, rightCap,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.toList] using capListDerivation
        simpa [leftCap, rightCap] using represented.toWord
      exact
        leftCapDerivation.trans
          (capWordDerivation.trans rightCapDerivation.symm)

theorem invariantOfS3_16S5_809Valid
    (identity : Identity Nat)
    (initialValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup)
    (finalValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_809.table.semigroup) :
    CappedEndpointInvariant identity := by
  have finalDerivation :=
    SemigroupBasis.CoRoots.S5_809.representative_basis.2
      identity finalValid
  refine ⟨?_, ?_⟩
  · constructor
    · intro valuation
      have evaluated := initialValid valuation
      simpa only [initialEval_eq_listEval] using evaluated
    · intro valuation
      have evaluated :=
        finalDerivation.sound
          s5_809BasisModelsRightRegularBandThree valuation
      simpa only [finalEval_eq_listEval] using evaluated
  · apply exponentValid_capped_count_eq identity
    exact
      finalDerivation.sound s5_809BasisModelsCommutativeExponentThree

theorem derivesOfS3_16S5_809Valid
    (identity : Identity Nat)
    (initialValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup)
    (finalValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_809.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfInvariant identity
    (invariantOfS3_16S5_809Valid identity initialValid finalValid)

/-- The first unconditional representative: the seven laws are a complete
basis for `Id(S3_16) ∩ Id(S5_809)`. -/
def s3_16S5_809IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_809.table.semigroup
      basis where
  leftModels := modelsS3_16
  rightModels := modelsS5_809
  complete := derivesOfS3_16S5_809Valid

private def detectorToFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- The transposed Cayley table, used only for exhaustive candidate
soundness checks against an opposite factor. -/
private def oppositeFiniteTable (table : FiniteTable) : FiniteTable where
  order := table.order
  mul := fun left right => table.mul right left
  assoc := fun left middle right =>
    (table.assoc right middle left).symm

private theorem oppositeFiniteTable_semigroup (table : FiniteTable) :
    (oppositeFiniteTable table).semigroup =
      table.semigroup.opposite := by
  rfl

theorem modelsS5_802Opposite :
    Models
      SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup.opposite
      basis := by
  rw [← oppositeFiniteTable_semigroup]
  exact
    FiniteCertificate.checkModels_sound
      (oppositeFiniteTable
        SemigroupBasis.Generated.Catalogue.S5_802.table)
      basis detectorToFinThree (by decide)

theorem s5_794OppositeBasisModelsRightRegularBandThree :
    Models rightRegularBandThreeTable.semigroup
      SemigroupBasis.CoRoots.S5_794.oppositeBasis :=
  FiniteCertificate.checkModels_sound
    rightRegularBandThreeTable
    SemigroupBasis.CoRoots.S5_794.oppositeBasis
    SemigroupBasis.CoRoots.S5_794.toFinFour (by decide)

theorem s5_794OppositeBasisModelsCommutativeExponentThree :
    Models commutativeExponentThree.semigroup
      SemigroupBasis.CoRoots.S5_794.oppositeBasis :=
  FiniteCertificate.checkModels_sound
    commutativeExponentThree
    SemigroupBasis.CoRoots.S5_794.oppositeBasis
    SemigroupBasis.CoRoots.S5_794.toFinFour (by decide)

theorem invariantOfS3_16S5_802OppositeValid
    (identity : Identity Nat)
    (initialValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup)
    (finalValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup.opposite) :
    CappedEndpointInvariant identity := by
  have finalDerivation :=
    SemigroupBasis.CoRoots.S5_794Family.S5_802.oppositeBasisFor.2
      identity finalValid
  refine ⟨?_, ?_⟩
  · constructor
    · intro valuation
      have evaluated := initialValid valuation
      simpa only [initialEval_eq_listEval] using evaluated
    · intro valuation
      have evaluated :=
        finalDerivation.sound
          s5_794OppositeBasisModelsRightRegularBandThree valuation
      simpa only [finalEval_eq_listEval] using evaluated
  · apply exponentValid_capped_count_eq identity
    exact
      finalDerivation.sound
        s5_794OppositeBasisModelsCommutativeExponentThree

theorem derivesOfS3_16S5_802OppositeValid
    (identity : Identity Nat)
    (initialValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup)
    (finalValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup.opposite) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfInvariant identity
    (invariantOfS3_16S5_802OppositeValid
      identity initialValid finalValid)

/-- The same seven laws form an unconditional intersection basis for
`S3_16` and the opposite of `S5_802`. -/
def s3_16S5_802OppositeIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup.opposite
      basis where
  leftModels := modelsS3_16
  rightModels := modelsS5_802Opposite
  complete := derivesOfS3_16S5_802OppositeValid

theorem modelsS3_16Opposite :
    Models
      SemigroupBasis.Generated.S3_16.table.semigroup.opposite basis := by
  rw [← oppositeFiniteTable_semigroup]
  exact
    FiniteCertificate.checkModels_sound
      (oppositeFiniteTable SemigroupBasis.Generated.S3_16.table)
      basis detectorToFinThree (by decide)

theorem modelsS4_75 :
    Models SemigroupBasis.Generated.S4_75.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_75.table basis detectorToFinThree
      (by decide)

theorem edmundsBasisModelsS3_16 :
    Models SemigroupBasis.Generated.S3_16.table.semigroup
      edmundsFiveTwoFourBasis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_16.table edmundsFiveTwoFourBasis
      detectorToFinThree (by decide)

theorem edmundsBasisModelsCommutativeExponentThree :
    Models commutativeExponentThree.semigroup
      edmundsFiveTwoFourBasis :=
  FiniteCertificate.checkModels_sound
    commutativeExponentThree edmundsFiveTwoFourBasis
      detectorToFinThree (by decide)

theorem invariantOfS3_16OppositeS4_75Valid
    (identity : Identity Nat)
    (finalValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup.opposite)
    (initialValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_75.table.semigroup) :
    CappedEndpointInvariant identity := by
  have initialDerivation :=
    SemigroupBasis.Generated.S4_75.representative_basis.2
      identity initialValid
  refine ⟨?_, ?_⟩
  · constructor
    · intro valuation
      have evaluated :=
        initialDerivation.sound edmundsBasisModelsS3_16 valuation
      simpa only [initialEval_eq_listEval] using evaluated
    · intro valuation
      have validInDetector :
          identity.SatisfiedBy rightRegularBandThreeTable.semigroup := by
        rw [rightRegularBandThreeTable_semigroup]
        exact finalValid
      have evaluated := validInDetector valuation
      simpa only [finalEval_eq_listEval] using evaluated
  · apply exponentValid_capped_count_eq identity
    exact
      initialDerivation.sound
        edmundsBasisModelsCommutativeExponentThree

theorem derivesOfS3_16OppositeS4_75Valid
    (identity : Identity Nat)
    (finalValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup.opposite)
    (initialValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_75.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfInvariant identity
    (invariantOfS3_16OppositeS4_75Valid
      identity finalValid initialValid)

/-- The dual detector orientation: the opposite of `S3_16` supplies the
last-occurrence invariant, while `S4_75` supplies first occurrences and
capped multiplicities. -/
def s3_16OppositeS4_75IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup.opposite
      SemigroupBasis.Generated.S4_75.table.semigroup
      basis where
  leftModels := modelsS3_16Opposite
  rightModels := modelsS4_75
  complete := derivesOfS3_16OppositeS4_75Valid

end SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw

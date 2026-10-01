import SemigroupBasis.CoRoots.S5_841

namespace SemigroupBasis.CoRoots.S5_841

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## S5_841 list-level quadratic swaps -/

/-- Package the four `L6` laws supplied by the `S5_841` basis for possibly
empty intervening gaps. -/
theorem listDerivesL6
    (x y : Nat) (middle tail : List Nat) :
    S5_107.ListDerives basis
      ([x, y] ++ middle ++ [x] ++ tail ++ [y])
      ([y, x] ++ middle ++ [x] ++ tail ++ [y]) := by
  cases middle with
  | nil =>
      cases tail with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesShortSwap
                (Word.singleton x) (Word.singleton y)
      | cons t ts =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesRightContextSwap
                (Word.singleton x) (Word.singleton y)
                (S5_107.listWordOfCons t ts)
  | cons m ms =>
      cases tail with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesTerminalContextSwap
                (Word.singleton x) (Word.singleton y)
                (S5_107.listWordOfCons m ms)
      | cons t ts =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesLongContextSwap
                (Word.singleton x) (Word.singleton y)
                (S5_107.listWordOfCons m ms)
                (S5_107.listWordOfCons t ts)

/-- Package the four `L8` laws supplied by the `S5_841` basis for possibly
empty intervening gaps. -/
theorem listDerivesL8
    (x y : Nat) (left middle : List Nat) :
    S5_107.ListDerives basis
      ([x] ++ left ++ [y] ++ middle ++ [x, y])
      ([x] ++ left ++ [y] ++ middle ++ [y, x]) := by
  cases left with
  | nil =>
      cases middle with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesAlternatingSquare
                (Word.singleton x) (Word.singleton y)
      | cons m ms =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesShortRotation
                (Word.singleton x) (Word.singleton y)
                (S5_107.listWordOfCons m ms)
  | cons l ls =>
      cases middle with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesTerminalSquare
                (Word.singleton x)
                (S5_107.listWordOfCons l ls)
                (Word.singleton y)
      | cons m ms =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesLongRotation
                (Word.singleton x)
                (S5_107.listWordOfCons l ls)
                (Word.singleton y)
                (S5_107.listWordOfCons m ms)

/-! ## Complete precedence on possibly empty lists -/

private def quadraticPrecedenceStep
    (x y : Nat) (state : PrecedenceState) (letter : Nat) :
    PrecedenceState :=
  if letter = x then
    match state with
    | .neither => .onlyX
    | .onlyX => .onlyX
    | .onlyY | .ordered | .violated => .violated
  else if letter = y then
    match state with
    | .neither => .onlyY
    | .onlyX => .ordered
    | .onlyY => .onlyY
    | .ordered => .ordered
    | .violated => .violated
  else state

private theorem precedenceScanList_eq_quadraticFold
    (letters : List Nat) (x y : Nat) :
    precedenceScanList letters x y =
      letters.foldl (quadraticPrecedenceStep x y) .neither := by
  rfl

private def quadraticPrecedenceCode : PrecedenceState → Fin 5
  | .neither => 1
  | .onlyX => 3
  | .onlyY => 4
  | .ordered => 2
  | .violated => 0

private theorem quadraticPrecedenceCode_injective :
    Function.Injective quadraticPrecedenceCode := by
  intro left right equal
  cases left <;> cases right <;>
    simp [quadraticPrecedenceCode] at equal ⊢

private def quadraticPrecedenceValuation (x y : Nat) : Nat → Fin 5 :=
  fun letter => if letter = x then 3 else if letter = y then 4 else 1

private theorem quadraticPrecedenceStep_code
    {x y : Nat} (different : x ≠ y)
    (state : PrecedenceState) (letter : Nat) :
    publishedM20Mul (quadraticPrecedenceCode state)
        (quadraticPrecedenceValuation x y letter) =
      quadraticPrecedenceCode
        (quadraticPrecedenceStep x y state letter) := by
  cases state <;> by_cases isX : letter = x
  <;> by_cases isY : letter = y
  <;> simp [quadraticPrecedenceValuation, quadraticPrecedenceStep,
    quadraticPrecedenceCode, isX, isY, different, Ne.symm different,
    publishedM20Mul] at *

private theorem quadraticPrecedenceFold_code
    {x y : Nat} (different : x ≠ y) :
    ∀ (letters : List Nat) (state : PrecedenceState),
      letters.foldl
          (fun current letter =>
            publishedM20Mul current
              (quadraticPrecedenceValuation x y letter))
          (quadraticPrecedenceCode state) =
        quadraticPrecedenceCode
          (letters.foldl (quadraticPrecedenceStep x y) state)
  | [], _ => rfl
  | letter :: rest, state => by
      simp only [List.foldl_cons]
      rw [quadraticPrecedenceStep_code different]
      exact quadraticPrecedenceFold_code different rest
        (quadraticPrecedenceStep x y state letter)

private theorem m20ListEval_quadraticPrecedence
    {x y : Nat} (different : x ≠ y) (letters : List Nat) :
    m20ListEval (quadraticPrecedenceValuation x y) letters =
      quadraticPrecedenceCode (precedenceScanList letters x y) := by
  rw [precedenceScanList_eq_quadraticFold]
  unfold m20ListEval
  change
    letters.foldl
        (fun current letter =>
          publishedM20Mul current
            (quadraticPrecedenceValuation x y letter))
        (quadraticPrecedenceCode .neither) =
      quadraticPrecedenceCode
        (letters.foldl (quadraticPrecedenceStep x y) .neither)
  exact quadraticPrecedenceFold_code different letters .neither

/-- Semantic equivalence in `M20` preserves complete precedence on lists.
This is the list-level counterpart of `valid_completePrecedence`. -/
theorem m20ListEquivalent_completePrecedenceList
    {left right : List Nat}
    (equivalent : M20ListEquivalent left right)
    (x y : Nat) :
    CompletePrecedenceList left x y ↔
      CompletePrecedenceList right x y := by
  by_cases different : x ≠ y
  · have evaluated := equivalent (quadraticPrecedenceValuation x y)
    rw [m20ListEval_quadraticPrecedence different,
      m20ListEval_quadraticPrecedence different] at evaluated
    have stateEqual := quadraticPrecedenceCode_injective evaluated
    simp only [CompletePrecedenceList, different, true_and]
    rw [stateEqual]
  · simp [CompletePrecedenceList, different]

private def quadraticPairFree
    (x y : Nat) (letters : List Nat) : Prop :=
  x ∉ letters ∧ y ∉ letters

private theorem quadraticPairFree_symm
    {x y : Nat} {letters : List Nat}
    (free : quadraticPairFree x y letters) :
    quadraticPairFree y x letters :=
  ⟨free.2, free.1⟩

private theorem quadraticPairFree_of_zero_counts
    {x y : Nat} {letters : List Nat}
    (xZero : letters.count x = 0)
    (yZero : letters.count y = 0) :
    quadraticPairFree x y letters :=
  ⟨List.count_eq_zero.mp xZero, List.count_eq_zero.mp yZero⟩

private theorem quadraticPrecedenceFold_pairFree
    (x y : Nat) :
    ∀ (letters : List Nat) (state : PrecedenceState),
      quadraticPairFree x y letters →
      letters.foldl (quadraticPrecedenceStep x y) state = state
  | [], _, _ => rfl
  | letter :: rest, state, free => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact free.1 (List.Mem.head rest)
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact free.2 (List.Mem.head rest)
      have restFree : quadraticPairFree x y rest :=
        ⟨fun member => free.1 (List.Mem.tail letter member),
          fun member => free.2 (List.Mem.tail letter member)⟩
      simp only [List.foldl_cons]
      rw [show quadraticPrecedenceStep x y state letter = state by
        simp [quadraticPrecedenceStep, letterNeX, letterNeY]]
      exact quadraticPrecedenceFold_pairFree x y rest state restFree

private theorem precedenceScan_xxyy
    {x y : Nat} (different : x ≠ y)
    (before left right after : List Nat)
    (beforeFree : quadraticPairFree x y before)
    (leftFree : quadraticPairFree x y left)
    (rightFree : quadraticPairFree x y right)
    (afterFree : quadraticPairFree x y after) :
    precedenceScanList
        (before ++ x :: (left ++ x :: y :: (right ++ y :: after)))
        x y =
      .ordered := by
  rw [precedenceScanList_eq_quadraticFold]
  rw [List.foldl_append]
  rw [quadraticPrecedenceFold_pairFree x y before .neither beforeFree]
  simp only [List.foldl_cons]
  rw [show quadraticPrecedenceStep x y .neither x = .onlyX by
    simp [quadraticPrecedenceStep]]
  rw [List.foldl_append]
  rw [quadraticPrecedenceFold_pairFree x y left .onlyX leftFree]
  simp only [List.foldl_cons]
  rw [show quadraticPrecedenceStep x y .onlyX x = .onlyX by
    simp [quadraticPrecedenceStep]]
  rw [show quadraticPrecedenceStep x y .onlyX y = .ordered by
    simp [quadraticPrecedenceStep, Ne.symm different]]
  rw [List.foldl_append]
  rw [quadraticPrecedenceFold_pairFree x y right .ordered rightFree]
  simp only [List.foldl_cons]
  rw [show quadraticPrecedenceStep x y .ordered y = .ordered by
    simp [quadraticPrecedenceStep, Ne.symm different]]
  exact quadraticPrecedenceFold_pairFree x y after .ordered afterFree

private theorem precedenceScan_xyxy
    {x y : Nat} (different : x ≠ y)
    (before left right after : List Nat)
    (beforeFree : quadraticPairFree x y before)
    (leftFree : quadraticPairFree x y left)
    (rightFree : quadraticPairFree x y right)
    (afterFree : quadraticPairFree x y after) :
    precedenceScanList
        (before ++ x :: (left ++ y :: x :: (right ++ y :: after)))
        x y =
      .violated := by
  rw [precedenceScanList_eq_quadraticFold]
  rw [List.foldl_append]
  rw [quadraticPrecedenceFold_pairFree x y before .neither beforeFree]
  simp only [List.foldl_cons]
  rw [show quadraticPrecedenceStep x y .neither x = .onlyX by
    simp [quadraticPrecedenceStep]]
  rw [List.foldl_append]
  rw [quadraticPrecedenceFold_pairFree x y left .onlyX leftFree]
  simp only [List.foldl_cons]
  rw [show quadraticPrecedenceStep x y .onlyX y = .ordered by
    simp [quadraticPrecedenceStep, Ne.symm different]]
  rw [show quadraticPrecedenceStep x y .ordered x = .violated by
    simp [quadraticPrecedenceStep]]
  rw [List.foldl_append]
  rw [quadraticPrecedenceFold_pairFree x y right .violated rightFree]
  simp only [List.foldl_cons]
  rw [show quadraticPrecedenceStep x y .violated y = .violated by
    simp [quadraticPrecedenceStep, Ne.symm different]]
  exact quadraticPrecedenceFold_pairFree x y after .violated afterFree

private theorem precedenceState_violated_ne_ordered :
    (PrecedenceState.violated : PrecedenceState) ≠ .ordered := by
  decide

/-- The local adjacent field for `S5_841`. The `L6` and `L8` cases are
derived syntactically. In each straddle case the proposed swap reverses a
complete-precedence value, contradicting the `M20ListEquivalent` premise. -/
theorem listDerivesAdjacentQuadraticSwap
    {x y : Nat} {pre post : List Nat}
    (different : x ≠ y)
    (xQuadratic : (pre ++ (x :: y :: post)).count x = 2)
    (yQuadratic : (pre ++ (x :: y :: post)).count y = 2)
    (position : QuadraticSwapPosition x y pre post)
    (equivalent :
      M20ListEquivalent
        (pre ++ (x :: y :: post))
        (pre ++ (y :: x :: post))) :
    S5_107.ListDerives basis
      (pre ++ (x :: y :: post))
      (pre ++ (y :: x :: post)) := by
  cases position with
  | futureXY middle between after postShape =>
      subst post
      simpa [List.append_assoc] using
        (listDerivesL6 x y middle between).context pre after
  | futureYX middle between after postShape =>
      subst post
      simpa [List.append_assoc] using
        (listDerivesL6 y x middle between).symm.context pre after
  | straddleXY before left right after preShape postShape =>
      subst pre
      subst post
      have xCount := xQuadratic
      have yCount := yQuadratic
      simp only [List.count_append, List.count_cons] at xCount yCount
      simp [different, Ne.symm different] at xCount yCount
      have beforeFree : quadraticPairFree x y before :=
        quadraticPairFree_of_zero_counts (by omega) (by omega)
      have leftFree : quadraticPairFree x y left :=
        quadraticPairFree_of_zero_counts (by omega) (by omega)
      have rightFree : quadraticPairFree x y right :=
        quadraticPairFree_of_zero_counts (by omega) (by omega)
      have afterFree : quadraticPairFree x y after :=
        quadraticPairFree_of_zero_counts (by omega) (by omega)
      have sourcePrecedence :
          CompletePrecedenceList
            ((before ++ x :: left) ++
              (x :: y :: (right ++ y :: after))) x y :=
        ⟨different, by
          simpa [List.append_assoc] using
            precedenceScan_xxyy different before left right after
              beforeFree leftFree rightFree afterFree⟩
      have targetNotPrecedence :
          ¬ CompletePrecedenceList
            ((before ++ x :: left) ++
              (y :: x :: (right ++ y :: after))) x y := by
        intro targetPrecedence
        have targetScan :
            precedenceScanList
                ((before ++ x :: left) ++
                  (y :: x :: (right ++ y :: after))) x y =
              .violated := by
          simpa [List.append_assoc] using
            precedenceScan_xyxy different before left right after
              beforeFree leftFree rightFree afterFree
        exact precedenceState_violated_ne_ordered
          (targetScan.symm.trans targetPrecedence.2)
      have preserved :=
        m20ListEquivalent_completePrecedenceList equivalent x y
      exact False.elim
        (targetNotPrecedence (preserved.mp sourcePrecedence))
  | straddleYX before left right after preShape postShape =>
      subst pre
      subst post
      have xCount := xQuadratic
      have yCount := yQuadratic
      simp only [List.count_append, List.count_cons] at xCount yCount
      simp [different, Ne.symm different] at xCount yCount
      have beforeFree : quadraticPairFree x y before :=
        quadraticPairFree_of_zero_counts (by omega) (by omega)
      have leftFree : quadraticPairFree x y left :=
        quadraticPairFree_of_zero_counts (by omega) (by omega)
      have rightFree : quadraticPairFree x y right :=
        quadraticPairFree_of_zero_counts (by omega) (by omega)
      have afterFree : quadraticPairFree x y after :=
        quadraticPairFree_of_zero_counts (by omega) (by omega)
      have beforeFreeYX := quadraticPairFree_symm beforeFree
      have leftFreeYX := quadraticPairFree_symm leftFree
      have rightFreeYX := quadraticPairFree_symm rightFree
      have afterFreeYX := quadraticPairFree_symm afterFree
      have sourceNotPrecedence :
          ¬ CompletePrecedenceList
            ((before ++ y :: left) ++
              (x :: y :: (right ++ x :: after))) y x := by
        intro sourcePrecedence
        have sourceScan :
            precedenceScanList
                ((before ++ y :: left) ++
                  (x :: y :: (right ++ x :: after))) y x =
              .violated := by
          simpa [List.append_assoc] using
            precedenceScan_xyxy (Ne.symm different)
              before left right after
              beforeFreeYX leftFreeYX rightFreeYX afterFreeYX
        exact precedenceState_violated_ne_ordered
          (sourceScan.symm.trans sourcePrecedence.2)
      have targetPrecedence :
          CompletePrecedenceList
            ((before ++ y :: left) ++
              (y :: x :: (right ++ x :: after))) y x :=
        ⟨Ne.symm different, by
          simpa [List.append_assoc] using
            precedenceScan_xxyy (Ne.symm different)
              before left right after
              beforeFreeYX leftFreeYX rightFreeYX afterFreeYX⟩
      have preserved :=
        m20ListEquivalent_completePrecedenceList equivalent y x
      exact False.elim
        (sourceNotPrecedence (preserved.mpr targetPrecedence))
  | pastXY before left middle preShape =>
      subst pre
      simpa [List.append_assoc] using
        (listDerivesL8 x y left middle).context before post
  | pastYX before left middle preShape =>
      subst pre
      simpa [List.append_assoc] using
        (listDerivesL8 y x left middle).symm.context before post

/-- The position witness can be recovered from the exact quadratic counts. -/
theorem listDerivesAdjacentQuadraticSwap_of_counts
    {x y : Nat} {pre post : List Nat}
    (different : x ≠ y)
    (xQuadratic : (pre ++ (x :: y :: post)).count x = 2)
    (yQuadratic : (pre ++ (x :: y :: post)).count y = 2)
    (equivalent :
      M20ListEquivalent
        (pre ++ (x :: y :: post))
        (pre ++ (y :: x :: post))) :
    S5_107.ListDerives basis
      (pre ++ (x :: y :: post))
      (pre ++ (y :: x :: post)) :=
  listDerivesAdjacentQuadraticSwap
    different xQuadratic yQuadratic
    (uniqueSeparatorAdjacentQuadraticPosition_of_counts
      different xQuadratic yQuadratic)
    equivalent

end SemigroupBasis.CoRoots.S5_841

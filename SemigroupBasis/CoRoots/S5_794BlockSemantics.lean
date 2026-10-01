import SemigroupBasis.CoRoots.S5_794BlockPermutation

namespace SemigroupBasis.CoRoots.S5_794

open SemigroupBasis

private theorem m14Mul_leftIdentity (value : Fin 5) :
    publishedM14Mul 4 value = value := by
  decide +revert

private theorem m14Mul_zeroLeft (value : Fin 5) :
    publishedM14Mul 0 value = 0 := by
  decide +revert

private def firstCutValuation (multiple separator : Nat) : Nat → Fin 5 :=
  fun letter =>
    if letter = multiple then 2 else if letter = separator then 3 else 4

private def lastCutValuation (multiple separator : Nat) : Nat → Fin 5 :=
  fun letter =>
    if letter = multiple then 2 else if letter = separator then 1 else 4

private theorem firstFold_two (multiple separator : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            publishedM14Mul current
              (firstCutValuation multiple separator letter)) 2 = 2
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      have step :
          publishedM14Mul 2
              (firstCutValuation multiple separator letter) = 2 := by
        unfold firstCutValuation
        by_cases isMultiple : letter = multiple
        · simp [isMultiple, publishedM14Mul]
        · by_cases isSeparator : letter = separator
          · subst letter
            simp [isMultiple, publishedM14Mul]
          · simp [isMultiple, isSeparator, publishedM14Mul]
      rw [step]
      exact firstFold_two multiple separator rest

private theorem firstFold_three (multiple separator : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            publishedM14Mul current
              (firstCutValuation multiple separator letter)) 3 = 3
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      have step :
          publishedM14Mul 3
              (firstCutValuation multiple separator letter) = 3 := by
        unfold firstCutValuation
        by_cases isMultiple : letter = multiple
        · simp [isMultiple, publishedM14Mul]
        · by_cases isSeparator : letter = separator
          · subst letter
            simp [isMultiple, publishedM14Mul]
          · simp [isMultiple, isSeparator, publishedM14Mul]
      rw [step]
      exact firstFold_three multiple separator rest

private theorem firstPrefixFold
    (multiple separator : Nat) :
    ∀ initial : List Nat,
      separator ∉ initial →
      initial.foldl
          (fun current letter =>
            publishedM14Mul current
              (firstCutValuation multiple separator letter)) 4 =
        if initial.count multiple = 0 then 4 else 2
  | [], _ => rfl
  | letter :: rest, separatorAbsent => by
      have separatorNeLetter : letter ≠ separator := by
        intro equal
        subst letter
        exact separatorAbsent (List.Mem.head rest)
      have separatorAbsentRest : separator ∉ rest :=
        fun member => separatorAbsent (List.Mem.tail letter member)
      by_cases isMultiple : letter = multiple
      · subst letter
        simp only [List.foldl_cons]
        rw [show firstCutValuation multiple separator multiple = 2 by
          simp [firstCutValuation]]
        rw [m14Mul_leftIdentity, firstFold_two]
        simp
      · simp only [List.foldl_cons]
        rw [show firstCutValuation multiple separator letter = 4 by
          simp [firstCutValuation, isMultiple, separatorNeLetter]]
        rw [m14Mul_leftIdentity]
        rw [firstPrefixFold multiple separator rest separatorAbsentRest]
        simp [isMultiple]

private theorem firstCutEval
    {multiple separator : Nat} (different : multiple ≠ separator)
    (before rest : List Nat) (separatorAbsent : separator ∉ before) :
    m14ListEval (firstCutValuation multiple separator)
        (before ++ separator :: rest) =
      if before.count multiple = 0 then 3 else 2 := by
  unfold m14ListEval
  rw [List.foldl_append]
  rw [firstPrefixFold multiple separator before separatorAbsent]
  by_cases zero : before.count multiple = 0
  · simp only [if_pos zero]
    simp only [List.foldl_cons]
    rw [show firstCutValuation multiple separator separator = 3 by
      simp [firstCutValuation, Ne.symm different]]
    rw [m14Mul_leftIdentity]
    exact firstFold_three multiple separator rest
  · simp only [if_neg zero]
    simp only [List.foldl_cons]
    rw [show firstCutValuation multiple separator separator = 3 by
      simp [firstCutValuation, Ne.symm different]]
    rw [show publishedM14Mul 2 3 = 2 by decide]
    exact firstFold_two multiple separator rest

private theorem lastFold_zero (multiple separator : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            publishedM14Mul current
              (lastCutValuation multiple separator letter)) 0 = 0
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [m14Mul_zeroLeft]
      exact lastFold_zero multiple separator rest

private theorem lastRestFold
    (multiple separator : Nat) :
    ∀ rest : List Nat,
      separator ∉ rest →
      rest.foldl
          (fun current letter =>
            publishedM14Mul current
              (lastCutValuation multiple separator letter)) 1 =
        if rest.count multiple = 0 then 1 else 0
  | [], _ => rfl
  | letter :: tail, separatorAbsent => by
      have separatorNeLetter : letter ≠ separator := by
        intro equal
        subst letter
        exact separatorAbsent (List.Mem.head tail)
      have separatorAbsentTail : separator ∉ tail :=
        fun member => separatorAbsent (List.Mem.tail letter member)
      by_cases isMultiple : letter = multiple
      · subst letter
        simp only [List.foldl_cons]
        rw [show lastCutValuation multiple separator multiple = 2 by
          simp [lastCutValuation]]
        rw [show publishedM14Mul 1 2 = 0 by decide]
        rw [lastFold_zero]
        simp
      · simp only [List.foldl_cons]
        rw [show lastCutValuation multiple separator letter = 4 by
          simp [lastCutValuation, isMultiple, separatorNeLetter]]
        rw [show publishedM14Mul 1 4 = 1 by decide]
        rw [lastRestFold multiple separator tail separatorAbsentTail]
        simp [isMultiple]

private theorem lastFold_two (multiple separator : Nat) :
    ∀ letters : List Nat,
      separator ∉ letters →
      letters.foldl
          (fun current letter =>
            publishedM14Mul current
              (lastCutValuation multiple separator letter)) 2 = 2
  | [], _ => rfl
  | letter :: rest, separatorAbsent => by
      have separatorNeLetter : letter ≠ separator := by
        intro equal
        subst letter
        exact separatorAbsent (List.Mem.head rest)
      have separatorAbsentRest : separator ∉ rest :=
        fun member => separatorAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      have step :
          publishedM14Mul 2
              (lastCutValuation multiple separator letter) = 2 := by
        unfold lastCutValuation
        by_cases isMultiple : letter = multiple
        · simp [isMultiple, publishedM14Mul]
        · simp [isMultiple, separatorNeLetter, publishedM14Mul]
      rw [step]
      exact lastFold_two multiple separator rest separatorAbsentRest

private theorem lastPrefixFold
    (multiple separator : Nat) :
    ∀ initial : List Nat,
      separator ∉ initial →
      initial.foldl
          (fun current letter =>
            publishedM14Mul current
              (lastCutValuation multiple separator letter)) 4 =
        if initial.count multiple = 0 then 4 else 2
  | [], _ => rfl
  | letter :: rest, separatorAbsent => by
      have separatorNeLetter : letter ≠ separator := by
        intro equal
        subst letter
        exact separatorAbsent (List.Mem.head rest)
      have separatorAbsentRest : separator ∉ rest :=
        fun member => separatorAbsent (List.Mem.tail letter member)
      by_cases isMultiple : letter = multiple
      · subst letter
        simp only [List.foldl_cons]
        rw [show lastCutValuation multiple separator multiple = 2 by
          simp [lastCutValuation]]
        rw [m14Mul_leftIdentity]
        rw [lastFold_two multiple separator rest separatorAbsentRest]
        simp
      · simp only [List.foldl_cons]
        rw [show lastCutValuation multiple separator letter = 4 by
          simp [lastCutValuation, isMultiple, separatorNeLetter]]
        rw [m14Mul_leftIdentity]
        rw [lastPrefixFold multiple separator rest separatorAbsentRest]
        simp [isMultiple]

private theorem lastCutEval
    {multiple separator : Nat} (different : multiple ≠ separator)
    (before rest : List Nat)
    (separatorAbsentBefore : separator ∉ before)
    (separatorAbsentRest : separator ∉ rest) :
    m14ListEval (lastCutValuation multiple separator)
        (before ++ separator :: rest) =
      if rest.count multiple = 0 then 1 else 0 := by
  unfold m14ListEval
  rw [List.foldl_append]
  rw [lastPrefixFold multiple separator before separatorAbsentBefore]
  by_cases zero : before.count multiple = 0
  · rw [if_pos zero]
    simp only [List.foldl_cons]
    rw [show lastCutValuation multiple separator separator = 1 by
      simp [lastCutValuation, Ne.symm different]]
    rw [m14Mul_leftIdentity]
    exact lastRestFold multiple separator rest separatorAbsentRest
  · rw [if_neg zero]
    simp only [List.foldl_cons]
    rw [show lastCutValuation multiple separator separator = 1 by
      simp [lastCutValuation, Ne.symm different]]
    rw [show publishedM14Mul 2 1 = 1 by decide]
    exact lastRestFold multiple separator rest separatorAbsentRest

/-- For a quadratic letter and a globally linear separator, `M14`
equivalence forces the same number (zero, one, or two) of occurrences before
the separator. -/
theorem prefixCount_eq_of_m14Equivalent
    {leftPrefix leftRest rightPrefix rightRest : List Nat}
    {multiple separator : Nat}
    (leftMultiple :
      (leftPrefix ++ separator :: leftRest).count multiple = 2)
    (rightMultiple :
      (rightPrefix ++ separator :: rightRest).count multiple = 2)
    (leftSeparator :
      (leftPrefix ++ separator :: leftRest).count separator = 1)
    (rightSeparator :
      (rightPrefix ++ separator :: rightRest).count separator = 1)
    (equivalent :
      M14ListEquivalent
        (leftPrefix ++ separator :: leftRest)
        (rightPrefix ++ separator :: rightRest)) :
    leftPrefix.count multiple = rightPrefix.count multiple := by
  have different : multiple ≠ separator := by
    intro equal
    subst multiple
    omega
  have leftSeparatorCounts :
      leftPrefix.count separator + leftRest.count separator = 0 := by
    simp only [List.count_append, List.count_cons_self] at leftSeparator
    omega
  have rightSeparatorCounts :
      rightPrefix.count separator + rightRest.count separator = 0 := by
    simp only [List.count_append, List.count_cons_self] at rightSeparator
    omega
  have leftSeparatorAbsentPrefix : separator ∉ leftPrefix :=
    List.count_eq_zero.mp (by omega)
  have leftSeparatorAbsentRest : separator ∉ leftRest :=
    List.count_eq_zero.mp (by omega)
  have rightSeparatorAbsentPrefix : separator ∉ rightPrefix :=
    List.count_eq_zero.mp (by omega)
  have rightSeparatorAbsentRest : separator ∉ rightRest :=
    List.count_eq_zero.mp (by omega)
  have firstEqual := equivalent (firstCutValuation multiple separator)
  rw [firstCutEval different leftPrefix leftRest
        leftSeparatorAbsentPrefix,
      firstCutEval different rightPrefix rightRest
        rightSeparatorAbsentPrefix] at firstEqual
  have lastEqual := equivalent (lastCutValuation multiple separator)
  rw [lastCutEval different leftPrefix leftRest
        leftSeparatorAbsentPrefix leftSeparatorAbsentRest,
      lastCutEval different rightPrefix rightRest
        rightSeparatorAbsentPrefix rightSeparatorAbsentRest] at lastEqual
  have prefixZero :
      leftPrefix.count multiple = 0 ↔
        rightPrefix.count multiple = 0 := by
    constructor
    · intro leftZero
      apply Decidable.byContradiction
      intro rightNonzero
      rw [if_pos leftZero, if_neg rightNonzero] at firstEqual
      exact (by decide : (3 : Fin 5) ≠ 2) firstEqual
    · intro rightZero
      apply Decidable.byContradiction
      intro leftNonzero
      rw [if_neg leftNonzero, if_pos rightZero] at firstEqual
      exact (by decide : (2 : Fin 5) ≠ 3) firstEqual
  have restZero :
      leftRest.count multiple = 0 ↔
        rightRest.count multiple = 0 := by
    constructor
    · intro leftZero
      apply Decidable.byContradiction
      intro rightNonzero
      rw [if_pos leftZero, if_neg rightNonzero] at lastEqual
      exact (by decide : (1 : Fin 5) ≠ 0) lastEqual
    · intro rightZero
      apply Decidable.byContradiction
      intro leftNonzero
      rw [if_neg leftNonzero, if_pos rightZero] at lastEqual
      exact (by decide : (0 : Fin 5) ≠ 1) lastEqual
  have leftSum :
      leftPrefix.count multiple + leftRest.count multiple = 2 := by
    simpa [List.count_append,
      List.count_cons_of_ne (Ne.symm different)] using leftMultiple
  have rightSum :
      rightPrefix.count multiple + rightRest.count multiple = 2 := by
    simpa [List.count_append,
      List.count_cons_of_ne (Ne.symm different)] using rightMultiple
  by_cases leftPrefixZero : leftPrefix.count multiple = 0
  · have rightPrefixZero := prefixZero.mp leftPrefixZero
    omega
  · have rightPrefixNonzero : rightPrefix.count multiple ≠ 0 :=
      fun rightZero => leftPrefixZero (prefixZero.mpr rightZero)
    by_cases leftRestZero : leftRest.count multiple = 0
    · have rightRestZero := restZero.mp leftRestZero
      omega
    · have rightRestNonzero : rightRest.count multiple ≠ 0 :=
        fun rightZero => leftRestZero (restZero.mpr rightZero)
      omega

end SemigroupBasis.CoRoots.S5_794

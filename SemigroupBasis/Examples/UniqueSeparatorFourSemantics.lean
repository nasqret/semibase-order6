import SemigroupBasis.Examples.UniqueSeparatorFour

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The table with an external identity state, used to evaluate possibly empty
lists. -/
inductive UniqueSeparatorFourState where
  | identity
  | value (element : Fin 4)
  deriving DecidableEq, Repr

/-- Extend the table multiplication by a left identity state. -/
def uniqueSeparatorFourListStep :
    UniqueSeparatorFourState → Fin 4 → UniqueSeparatorFourState
  | .identity, next => .value next
  | .value current, next =>
      .value (uniqueSeparatorFourMul current next)

/-- Evaluate a list from an arbitrary extended state. -/
def uniqueSeparatorFourEvalFrom
    {α : Type} (initial : UniqueSeparatorFourState)
    (valuation : α → Fin 4) (letters : List α) :
    UniqueSeparatorFourState :=
  letters.foldl
    (fun current letter =>
      uniqueSeparatorFourListStep current (valuation letter))
    initial

/-- Evaluate a possibly empty list, starting at the external identity. -/
def uniqueSeparatorFourEvalList
    {α : Type} (valuation : α → Fin 4) (letters : List α) :
    UniqueSeparatorFourState :=
  uniqueSeparatorFourEvalFrom .identity valuation letters

@[simp]
theorem uniqueSeparatorFourEvalFrom_nil
    {α : Type} (initial : UniqueSeparatorFourState)
    (valuation : α → Fin 4) :
    uniqueSeparatorFourEvalFrom initial valuation [] = initial :=
  rfl

@[simp]
theorem uniqueSeparatorFourEvalFrom_cons
    {α : Type} (initial : UniqueSeparatorFourState)
    (valuation : α → Fin 4) (letter : α) (letters : List α) :
    uniqueSeparatorFourEvalFrom initial valuation (letter :: letters) =
      uniqueSeparatorFourEvalFrom
        (uniqueSeparatorFourListStep initial (valuation letter))
        valuation letters :=
  rfl

theorem uniqueSeparatorFourEvalFrom_append
    {α : Type} (initial : UniqueSeparatorFourState)
    (valuation : α → Fin 4) (left right : List α) :
    uniqueSeparatorFourEvalFrom initial valuation (left ++ right) =
      uniqueSeparatorFourEvalFrom
        (uniqueSeparatorFourEvalFrom initial valuation left)
        valuation right := by
  simp [uniqueSeparatorFourEvalFrom, List.foldl_append]

theorem uniqueSeparatorFourEvalFrom_value
    {α : Type} (initial : Fin 4) (valuation : α → Fin 4)
    (letters : List α) :
    uniqueSeparatorFourEvalFrom (.value initial) valuation letters =
      .value
        (letters.foldl
          (fun current letter =>
            uniqueSeparatorFourMul current (valuation letter))
          initial) := by
  induction letters generalizing initial with
  | nil => rfl
  | cons letter letters ih =>
      simp only [uniqueSeparatorFourEvalFrom_cons,
        uniqueSeparatorFourListStep]
      exact ih (uniqueSeparatorFourMul initial (valuation letter))

/-- The list evaluator agrees with the semigroup evaluator on the nonempty
list underlying every word. -/
theorem uniqueSeparatorFourEvalList_toList
    {α : Type} (valuation : α → Fin 4) (word : Word α) :
    uniqueSeparatorFourEvalList valuation word.toList =
      .value (uniqueSeparatorFour.semigroup.eval valuation word) := by
  cases word with
  | mk head tail =>
      simp only [uniqueSeparatorFourEvalList,
        uniqueSeparatorFourEvalFrom_cons, uniqueSeparatorFourListStep,
        Word.toList, Semigroup.eval]
      exact uniqueSeparatorFourEvalFrom_value (valuation head) valuation tail

@[simp]
theorem uniqueSeparatorFourMul_zero_left (next : Fin 4) :
    uniqueSeparatorFourMul 0 next = 0 := by
  decide +revert

@[simp]
theorem uniqueSeparatorFourMul_zero_right (current : Fin 4) :
    uniqueSeparatorFourMul current 0 = 0 := by
  decide +revert

@[simp]
theorem uniqueSeparatorFourMul_one_three :
    uniqueSeparatorFourMul 1 3 = 1 := by
  decide

@[simp]
theorem uniqueSeparatorFourMul_two_one :
    uniqueSeparatorFourMul 2 1 = 1 := by
  decide

@[simp]
theorem uniqueSeparatorFourMul_two_two :
    uniqueSeparatorFourMul 2 2 = 2 := by
  decide

@[simp]
theorem uniqueSeparatorFourMul_three_three :
    uniqueSeparatorFourMul 3 3 = 3 := by
  decide

/-- A tested variable is sent to zero; every other variable is sent to the
right-phase idempotent. -/
def uniqueSeparatorFourSupportValuation
    {α : Type} [DecidableEq α] (tested : α) : α → Fin 4 :=
  fun letter => if letter = tested then 0 else 3

theorem uniqueSeparatorFourEvalFrom_zero
    {α : Type} (valuation : α → Fin 4) (letters : List α) :
    uniqueSeparatorFourEvalFrom (.value 0) valuation letters =
      .value 0 := by
  induction letters with
  | nil => rfl
  | cons letter letters ih =>
      simp only [uniqueSeparatorFourEvalFrom_cons,
        uniqueSeparatorFourListStep, uniqueSeparatorFourMul_zero_left]
      exact ih

theorem uniqueSeparatorFourSupportFold_three
    {α : Type} [DecidableEq α] (tested : α) (letters : List α) :
    uniqueSeparatorFourEvalFrom (.value 3)
        (uniqueSeparatorFourSupportValuation tested) letters =
      if tested ∈ letters then .value 0 else .value 3 := by
  induction letters with
  | nil => simp
  | cons letter letters ih =>
      by_cases hit : letter = tested
      · subst letter
        rw [uniqueSeparatorFourEvalFrom_cons]
        rw [show
          uniqueSeparatorFourSupportValuation tested tested = 0 by
            simp [uniqueSeparatorFourSupportValuation]]
        simp only [uniqueSeparatorFourListStep,
          uniqueSeparatorFourMul_zero_right]
        rw [uniqueSeparatorFourEvalFrom_zero]
        simp
      · have reverseDifferent : tested ≠ letter := Ne.symm hit
        rw [uniqueSeparatorFourEvalFrom_cons]
        rw [show
          uniqueSeparatorFourSupportValuation tested letter = 3 by
            simp [uniqueSeparatorFourSupportValuation, hit]]
        simp only [uniqueSeparatorFourListStep,
          uniqueSeparatorFourMul_three_three]
        rw [ih]
        simp [reverseDifferent]

/-- The support valuation detects occurrence exactly, including the empty-list
case through the external identity state. -/
theorem uniqueSeparatorFourSupportEvalList_eq_zero_iff
    {α : Type} [DecidableEq α] (tested : α) (letters : List α) :
    uniqueSeparatorFourEvalList
        (uniqueSeparatorFourSupportValuation tested) letters =
        .value 0 ↔
      tested ∈ letters := by
  cases letters with
  | nil => simp [uniqueSeparatorFourEvalList]
  | cons letter letters =>
      by_cases hit : letter = tested
      · subst letter
        rw [uniqueSeparatorFourEvalList,
          uniqueSeparatorFourEvalFrom_cons]
        rw [show
          uniqueSeparatorFourSupportValuation tested tested = 0 by
            simp [uniqueSeparatorFourSupportValuation]]
        simp only [uniqueSeparatorFourListStep]
        rw [uniqueSeparatorFourEvalFrom_zero]
        simp
      · have reverseDifferent : tested ≠ letter := Ne.symm hit
        rw [uniqueSeparatorFourEvalList,
          uniqueSeparatorFourEvalFrom_cons]
        rw [show
          uniqueSeparatorFourSupportValuation tested letter = 3 by
            simp [uniqueSeparatorFourSupportValuation, hit]]
        simp only [uniqueSeparatorFourListStep]
        rw [uniqueSeparatorFourSupportFold_three]
        simp [reverseDifferent]

/-- Semigroup evaluation at the support valuation is zero exactly when the
tested variable occurs in the word. -/
theorem uniqueSeparatorFourSupportEval_eq_zero_iff
    {α : Type} [DecidableEq α] (tested : α) (word : Word α) :
    uniqueSeparatorFour.semigroup.eval
        (uniqueSeparatorFourSupportValuation tested) word = (0 : Fin 4) ↔
      tested ∈ word.toList := by
  have detected :=
    uniqueSeparatorFourSupportEvalList_eq_zero_iff tested word.toList
  rw [uniqueSeparatorFourEvalList_toList] at detected
  simpa using detected

/-- The two displayed list supports are disjoint. -/
def UniqueSeparatorFourSupportsDisjoint
    {α : Type} (left right : List α) : Prop :=
  ∀ letter, letter ∈ left → letter ∉ right

/-- Values for a proposed cut: left-support variables are in state `2`, the
separator is `1`, and all remaining variables are in the right phase `3`. -/
def uniqueSeparatorFourSeparatorValuation
    {α : Type} [DecidableEq α] (left : List α) (separator : α) :
    α → Fin 4 :=
  fun letter =>
    if letter = separator then 1
    else if letter ∈ left then 2
    else 3

/-- The separator valuation viewed as the valuation attached to the cut after
`left`. -/
abbrev uniqueSeparatorFourCutValuation
    {α : Type} [DecidableEq α] (left : List α) (separator : α) :
    α → Fin 4 :=
  uniqueSeparatorFourSeparatorValuation left separator

@[simp]
theorem uniqueSeparatorFourSeparatorValuation_separator
    {α : Type} [DecidableEq α] (left : List α) (separator : α) :
    uniqueSeparatorFourSeparatorValuation left separator separator = 1 := by
  simp [uniqueSeparatorFourSeparatorValuation]

theorem uniqueSeparatorFourSeparatorValuation_left
    {α : Type} [DecidableEq α] {left : List α} {separator letter : α}
    (member : letter ∈ left) (different : letter ≠ separator) :
    uniqueSeparatorFourSeparatorValuation left separator letter = 2 := by
  simp [uniqueSeparatorFourSeparatorValuation, different, member]

theorem uniqueSeparatorFourSeparatorValuation_right
    {α : Type} [DecidableEq α] {left right : List α}
    {separator letter : α}
    (disjoint : UniqueSeparatorFourSupportsDisjoint left right)
    (separatorAbsent : separator ∉ right) (member : letter ∈ right) :
    uniqueSeparatorFourSeparatorValuation left separator letter = 3 := by
  have different : letter ≠ separator := by
    intro equality
    subst letter
    exact separatorAbsent member
  have notLeft : letter ∉ left := by
    intro leftMember
    exact disjoint letter leftMember member
  simp [uniqueSeparatorFourSeparatorValuation, different, notLeft]

theorem uniqueSeparatorFourLeftPhaseFoldFromTwo
    {α : Type} [DecidableEq α] {left : List α} {separator : α}
    (separatorAbsent : separator ∉ left) (letters : List α)
    (supported : ∀ letter, letter ∈ letters → letter ∈ left) :
    uniqueSeparatorFourEvalFrom (.value 2)
        (uniqueSeparatorFourSeparatorValuation left separator) letters =
      .value 2 := by
  induction letters with
  | nil => rfl
  | cons letter letters ih =>
      have member : letter ∈ left :=
        supported letter (by simp)
      have different : letter ≠ separator := by
        intro equality
        subst letter
        exact separatorAbsent member
      have tailSupported :
          ∀ value, value ∈ letters → value ∈ left := by
        intro value valueMember
        exact supported value (List.Mem.tail letter valueMember)
      simp only [uniqueSeparatorFourEvalFrom_cons,
        uniqueSeparatorFourSeparatorValuation_left member different,
        uniqueSeparatorFourListStep, uniqueSeparatorFourMul_two_two]
      exact ih tailSupported

/-- Folding the displayed left block from the external identity gives the
identity for an empty block and the left-phase state `2` otherwise. -/
theorem uniqueSeparatorFourLeftPhaseFold
    {α : Type} [DecidableEq α] (left : List α) (separator : α)
    (separatorAbsent : separator ∉ left) :
    uniqueSeparatorFourEvalList
        (uniqueSeparatorFourSeparatorValuation left separator) left =
      if left = [] then .identity else .value 2 := by
  cases left with
  | nil => rfl
  | cons letter letters =>
      have member : letter ∈ letter :: letters := by simp
      have different : letter ≠ separator := by
        intro equality
        subst letter
        exact separatorAbsent member
      simp only [uniqueSeparatorFourEvalList,
        uniqueSeparatorFourEvalFrom_cons,
        uniqueSeparatorFourSeparatorValuation_left member different,
        uniqueSeparatorFourListStep]
      exact uniqueSeparatorFourLeftPhaseFoldFromTwo
        separatorAbsent letters (by
          intro value valueMember
          exact List.Mem.tail letter valueMember)

/-- Once the separator has produced state `1`, the displayed disjoint right
block preserves that state. -/
theorem uniqueSeparatorFourRightPhaseFold
    {α : Type} [DecidableEq α] {left right : List α} {separator : α}
    (disjoint : UniqueSeparatorFourSupportsDisjoint left right)
    (separatorAbsent : separator ∉ right) :
    uniqueSeparatorFourEvalFrom (.value 1)
        (uniqueSeparatorFourSeparatorValuation left separator) right =
      .value 1 := by
  induction right with
  | nil => rfl
  | cons letter letters ih =>
      have member : letter ∈ letter :: letters := by simp
      have value :=
        uniqueSeparatorFourSeparatorValuation_right
          disjoint separatorAbsent member
      have tailDisjoint :
          UniqueSeparatorFourSupportsDisjoint left letters := by
        intro x leftMember rightMember
        exact disjoint x leftMember (List.Mem.tail letter rightMember)
      have tailSeparatorAbsent : separator ∉ letters := by
        intro rightMember
        exact separatorAbsent (List.Mem.tail letter rightMember)
      simp only [uniqueSeparatorFourEvalFrom_cons, value,
        uniqueSeparatorFourListStep, uniqueSeparatorFourMul_one_three]
      exact ih tailDisjoint tailSeparatorAbsent

/-- A cut with an absent separator on both sides and disjoint left/right
supports evaluates exactly to zero-based state `1`. -/
theorem uniqueSeparatorFourSeparatorSplitFold
    {α : Type} [DecidableEq α] (left right : List α) (separator : α)
    (separatorAbsentLeft : separator ∉ left)
    (separatorAbsentRight : separator ∉ right)
    (disjoint : UniqueSeparatorFourSupportsDisjoint left right) :
    uniqueSeparatorFourEvalList
        (uniqueSeparatorFourSeparatorValuation left separator)
        (left ++ separator :: right) =
      .value 1 := by
  rw [uniqueSeparatorFourEvalList,
    uniqueSeparatorFourEvalFrom_append]
  change
    uniqueSeparatorFourEvalFrom
        (uniqueSeparatorFourEvalList
          (uniqueSeparatorFourSeparatorValuation left separator) left)
        (uniqueSeparatorFourSeparatorValuation left separator)
        (separator :: right) =
      .value 1
  rw [uniqueSeparatorFourLeftPhaseFold left separator separatorAbsentLeft]
  by_cases leftEmpty : left = []
  · rw [if_pos leftEmpty]
    simp only [uniqueSeparatorFourEvalFrom_cons,
      uniqueSeparatorFourSeparatorValuation_separator,
      uniqueSeparatorFourListStep]
    exact uniqueSeparatorFourRightPhaseFold
      disjoint separatorAbsentRight
  · simp only [if_neg leftEmpty, uniqueSeparatorFourEvalFrom_cons,
      uniqueSeparatorFourSeparatorValuation_separator,
      uniqueSeparatorFourListStep, uniqueSeparatorFourMul_two_one]
    exact uniqueSeparatorFourRightPhaseFold
      disjoint separatorAbsentRight

/-- Cut-valuation form of `uniqueSeparatorFourSeparatorSplitFold`. -/
theorem uniqueSeparatorFourCutFold
    {α : Type} [DecidableEq α] (left right : List α) (separator : α)
    (separatorAbsentLeft : separator ∉ left)
    (separatorAbsentRight : separator ∉ right)
    (disjoint : UniqueSeparatorFourSupportsDisjoint left right) :
    uniqueSeparatorFourEvalList
        (uniqueSeparatorFourCutValuation left separator)
        (left ++ separator :: right) =
      .value 1 :=
  uniqueSeparatorFourSeparatorSplitFold left right separator
    separatorAbsentLeft separatorAbsentRight disjoint

/-- An actual prefix is compatible with the proposed left support when it
avoids the separator and every one of its letters belongs to that support. -/
def UniqueSeparatorFourLeftCompatible
    {α : Type} (left : List α) (separator : α)
    (actualLeft : List α) : Prop :=
  separator ∉ actualLeft ∧
    ∀ letter, letter ∈ actualLeft → letter ∈ left

/-- An actual suffix is compatible with the proposed left support when it
avoids the separator and none of its letters belongs to that support. -/
def UniqueSeparatorFourRightCompatible
    {α : Type} (left : List α) (separator : α)
    (actualRight : List α) : Prop :=
  separator ∉ actualRight ∧
    ∀ letter, letter ∈ actualRight → letter ∉ left

@[simp]
theorem uniqueSeparatorFourMul_one_one :
    uniqueSeparatorFourMul 1 1 = 0 := by
  decide

@[simp]
theorem uniqueSeparatorFourMul_one_two :
    uniqueSeparatorFourMul 1 2 = 0 := by
  decide

@[simp]
theorem uniqueSeparatorFourMul_two_three :
    uniqueSeparatorFourMul 2 3 = 0 := by
  decide

@[simp]
theorem uniqueSeparatorFourMul_three_one :
    uniqueSeparatorFourMul 3 1 = 0 := by
  decide

@[simp]
theorem uniqueSeparatorFourMul_three_two :
    uniqueSeparatorFourMul 3 2 = 0 := by
  decide

/-- Exact characterization of the right phase: state `1` survives precisely
through letters outside the proposed left support and distinct from the
separator. -/
theorem uniqueSeparatorFourRightPhaseFold_eq_one_iff
    {α : Type} [DecidableEq α] (left : List α) (separator : α)
    (letters : List α) :
    uniqueSeparatorFourEvalFrom (.value 1)
        (uniqueSeparatorFourSeparatorValuation left separator) letters =
        .value 1 ↔
      UniqueSeparatorFourRightCompatible left separator letters := by
  induction letters with
  | nil =>
      simp [UniqueSeparatorFourRightCompatible]
  | cons letter letters ih =>
      by_cases separatorHit : letter = separator
      · subst letter
        rw [uniqueSeparatorFourEvalFrom_cons]
        rw [uniqueSeparatorFourSeparatorValuation_separator]
        simp only [uniqueSeparatorFourListStep,
          uniqueSeparatorFourMul_one_one]
        rw [uniqueSeparatorFourEvalFrom_zero]
        simp [UniqueSeparatorFourRightCompatible]
      · by_cases leftHit : letter ∈ left
        · rw [uniqueSeparatorFourEvalFrom_cons]
          rw [show
            uniqueSeparatorFourSeparatorValuation
                left separator letter = 2 by
              simp [uniqueSeparatorFourSeparatorValuation,
                separatorHit, leftHit]]
          simp only [uniqueSeparatorFourListStep,
            uniqueSeparatorFourMul_one_two]
          rw [uniqueSeparatorFourEvalFrom_zero]
          simp [UniqueSeparatorFourRightCompatible, leftHit]
        · rw [uniqueSeparatorFourEvalFrom_cons]
          simp only [uniqueSeparatorFourSeparatorValuation,
            if_neg separatorHit, if_neg leftHit,
            uniqueSeparatorFourListStep,
            uniqueSeparatorFourMul_one_three]
          rw [ih]
          simp [UniqueSeparatorFourRightCompatible,
            Ne.symm separatorHit, leftHit]

/-- Starting in the right-phase state `3` can never produce state `1`. -/
theorem uniqueSeparatorFourRightStart_ne_one
    {α : Type} [DecidableEq α] (left : List α) (separator : α)
    (letters : List α) :
    uniqueSeparatorFourEvalFrom (.value 3)
        (uniqueSeparatorFourSeparatorValuation left separator) letters ≠
      .value 1 := by
  induction letters with
  | nil => simp
  | cons letter letters ih =>
      by_cases separatorHit : letter = separator
      · subst letter
        rw [uniqueSeparatorFourEvalFrom_cons]
        rw [uniqueSeparatorFourSeparatorValuation_separator]
        simp only [uniqueSeparatorFourListStep,
          uniqueSeparatorFourMul_three_one]
        rw [uniqueSeparatorFourEvalFrom_zero]
        simp
      · by_cases leftHit : letter ∈ left
        · rw [uniqueSeparatorFourEvalFrom_cons]
          rw [show
            uniqueSeparatorFourSeparatorValuation
                left separator letter = 2 by
              simp [uniqueSeparatorFourSeparatorValuation,
                separatorHit, leftHit]]
          simp only [uniqueSeparatorFourListStep,
            uniqueSeparatorFourMul_three_two]
          rw [uniqueSeparatorFourEvalFrom_zero]
          simp
        · rw [uniqueSeparatorFourEvalFrom_cons]
          simp only [uniqueSeparatorFourSeparatorValuation,
            if_neg separatorHit, if_neg leftHit,
            uniqueSeparatorFourListStep,
            uniqueSeparatorFourMul_three_three]
          exact ih

/-- Every state-`1` result reached from the left phase has a unique-phase
shape: a compatible left block, one separator, and a compatible right block. -/
theorem uniqueSeparatorFourLeftSearchFold_exists_cut
    {α : Type} [DecidableEq α] (left : List α) (separator : α)
    (letters : List α)
    (evaluated :
      uniqueSeparatorFourEvalFrom (.value 2)
          (uniqueSeparatorFourSeparatorValuation left separator) letters =
        .value 1) :
    ∃ actualLeft actualRight,
      letters = actualLeft ++ separator :: actualRight ∧
        UniqueSeparatorFourLeftCompatible
          left separator actualLeft ∧
        UniqueSeparatorFourRightCompatible
          left separator actualRight := by
  induction letters with
  | nil =>
      simp at evaluated
  | cons letter letters ih =>
      by_cases separatorHit : letter = separator
      · subst letter
        rw [uniqueSeparatorFourEvalFrom_cons] at evaluated
        simp only [uniqueSeparatorFourSeparatorValuation_separator,
          uniqueSeparatorFourListStep,
          uniqueSeparatorFourMul_two_one] at evaluated
        have rightCompatible :=
          (uniqueSeparatorFourRightPhaseFold_eq_one_iff
            left separator letters).mp evaluated
        exact
          ⟨[], letters, by simp,
            by simp [UniqueSeparatorFourLeftCompatible],
            rightCompatible⟩
      · by_cases leftHit : letter ∈ left
        · rw [uniqueSeparatorFourEvalFrom_cons] at evaluated
          rw [show
            uniqueSeparatorFourSeparatorValuation
                left separator letter = 2 by
              simp [uniqueSeparatorFourSeparatorValuation,
                separatorHit, leftHit]] at evaluated
          simp only [uniqueSeparatorFourListStep,
            uniqueSeparatorFourMul_two_two] at evaluated
          obtain
            ⟨actualLeft, actualRight, split,
              leftCompatible, rightCompatible⟩ :=
            ih evaluated
          refine
            ⟨letter :: actualLeft, actualRight, ?_, ?_,
              rightCompatible⟩
          · simp [split]
          · constructor
            · simp [Ne.symm separatorHit, leftCompatible.1]
            · intro value member
              simp only [List.mem_cons] at member
              rcases member with equality | tailMember
              · subst value
                exact leftHit
              · exact leftCompatible.2 value tailMember
        · rw [uniqueSeparatorFourEvalFrom_cons] at evaluated
          rw [show
            uniqueSeparatorFourSeparatorValuation
                left separator letter = 3 by
              simp [uniqueSeparatorFourSeparatorValuation,
                separatorHit, leftHit]] at evaluated
          simp only [uniqueSeparatorFourListStep,
            uniqueSeparatorFourMul_two_three] at evaluated
          rw [uniqueSeparatorFourEvalFrom_zero] at evaluated
          simp at evaluated

/-- A compatible nonempty prefix preserves the left-phase state `2` when
evaluation already starts in that state. -/
theorem uniqueSeparatorFourCompatibleLeftPhaseFoldFromTwo
    {α : Type} [DecidableEq α] (left : List α) (separator : α)
    (letters : List α)
    (compatible :
      UniqueSeparatorFourLeftCompatible left separator letters) :
    uniqueSeparatorFourEvalFrom (.value 2)
        (uniqueSeparatorFourSeparatorValuation left separator) letters =
      .value 2 := by
  induction letters with
  | nil => rfl
  | cons letter letters ih =>
      have member : letter ∈ left :=
        compatible.2 letter (by simp)
      have different : letter ≠ separator := by
        intro equality
        subst letter
        exact compatible.1 (by simp)
      have tailCompatible :
          UniqueSeparatorFourLeftCompatible left separator letters := by
        constructor
        · intro separatorMember
          exact compatible.1
            (List.Mem.tail letter separatorMember)
        · intro value valueMember
          exact compatible.2 value
            (List.Mem.tail letter valueMember)
      simp only [uniqueSeparatorFourEvalFrom_cons,
        uniqueSeparatorFourSeparatorValuation_left member different,
        uniqueSeparatorFourListStep,
        uniqueSeparatorFourMul_two_two]
      exact ih tailCompatible

/-- A compatible actual left block evaluates to the left-phase state `2`
unless it is empty, in which case the external identity remains. -/
theorem uniqueSeparatorFourCompatibleLeftPhaseFold
    {α : Type} [DecidableEq α] (left : List α) (separator : α)
    (actualLeft : List α)
    (compatible :
      UniqueSeparatorFourLeftCompatible left separator actualLeft) :
    uniqueSeparatorFourEvalList
        (uniqueSeparatorFourSeparatorValuation left separator)
        actualLeft =
      if actualLeft = [] then .identity else .value 2 := by
  cases actualLeft with
  | nil => rfl
  | cons letter letters =>
      have member : letter ∈ left :=
        compatible.2 letter (by simp)
      have different : letter ≠ separator := by
        intro equality
        subst letter
        exact compatible.1 (by simp)
      simp only [uniqueSeparatorFourEvalList,
        uniqueSeparatorFourEvalFrom_cons,
        uniqueSeparatorFourSeparatorValuation_left member different,
        uniqueSeparatorFourListStep]
      exact uniqueSeparatorFourCompatibleLeftPhaseFoldFromTwo
        left separator letters (by
          constructor
          · intro separatorMember
            exact compatible.1
              (List.Mem.tail letter separatorMember)
          · intro value valueMember
            exact compatible.2 value
              (List.Mem.tail letter valueMember))

/-- Every compatible left/separator/right split evaluates to state `1`, even
when the actual left support is only a subset of the proposed support. -/
theorem uniqueSeparatorFourCompatibleSeparatorSplitFold
    {α : Type} [DecidableEq α] (left : List α) (separator : α)
    (actualLeft actualRight : List α)
    (leftCompatible :
      UniqueSeparatorFourLeftCompatible left separator actualLeft)
    (rightCompatible :
      UniqueSeparatorFourRightCompatible left separator actualRight) :
    uniqueSeparatorFourEvalList
        (uniqueSeparatorFourSeparatorValuation left separator)
        (actualLeft ++ separator :: actualRight) =
      .value 1 := by
  rw [uniqueSeparatorFourEvalList,
    uniqueSeparatorFourEvalFrom_append]
  change
    uniqueSeparatorFourEvalFrom
        (uniqueSeparatorFourEvalList
          (uniqueSeparatorFourSeparatorValuation left separator)
          actualLeft)
        (uniqueSeparatorFourSeparatorValuation left separator)
        (separator :: actualRight) =
      .value 1
  rw [uniqueSeparatorFourCompatibleLeftPhaseFold
    left separator actualLeft leftCompatible]
  by_cases leftEmpty : actualLeft = []
  · rw [if_pos leftEmpty]
    simp only [uniqueSeparatorFourEvalFrom_cons,
      uniqueSeparatorFourSeparatorValuation_separator,
      uniqueSeparatorFourListStep]
    exact
      (uniqueSeparatorFourRightPhaseFold_eq_one_iff
        left separator actualRight).mpr rightCompatible
  · rw [if_neg leftEmpty]
    simp only [uniqueSeparatorFourEvalFrom_cons,
      uniqueSeparatorFourSeparatorValuation_separator,
      uniqueSeparatorFourListStep,
      uniqueSeparatorFourMul_two_one]
    exact
      (uniqueSeparatorFourRightPhaseFold_eq_one_iff
        left separator actualRight).mpr rightCompatible

/-- Exact phase-shape characterization of evaluation at state `1`. -/
theorem uniqueSeparatorFourSeparatorEvalList_eq_one_iff_exists_cut
    {α : Type} [DecidableEq α] (left : List α) (separator : α)
    (letters : List α) :
    uniqueSeparatorFourEvalList
        (uniqueSeparatorFourSeparatorValuation left separator) letters =
        .value 1 ↔
      ∃ actualLeft actualRight,
        letters = actualLeft ++ separator :: actualRight ∧
          UniqueSeparatorFourLeftCompatible
            left separator actualLeft ∧
          UniqueSeparatorFourRightCompatible
            left separator actualRight := by
  constructor
  · intro evaluated
    cases letters with
    | nil =>
        simp [uniqueSeparatorFourEvalList] at evaluated
    | cons letter letters =>
        by_cases separatorHit : letter = separator
        · subst letter
          rw [uniqueSeparatorFourEvalList,
            uniqueSeparatorFourEvalFrom_cons] at evaluated
          simp only [uniqueSeparatorFourSeparatorValuation_separator,
            uniqueSeparatorFourListStep] at evaluated
          have rightCompatible :=
            (uniqueSeparatorFourRightPhaseFold_eq_one_iff
              left separator letters).mp evaluated
          exact
            ⟨[], letters, by simp,
              by simp [UniqueSeparatorFourLeftCompatible],
              rightCompatible⟩
        · by_cases leftHit : letter ∈ left
          · rw [uniqueSeparatorFourEvalList,
              uniqueSeparatorFourEvalFrom_cons] at evaluated
            rw [show
              uniqueSeparatorFourSeparatorValuation
                  left separator letter = 2 by
                simp [uniqueSeparatorFourSeparatorValuation,
                  separatorHit, leftHit]] at evaluated
            simp only [uniqueSeparatorFourListStep] at evaluated
            obtain
              ⟨actualLeft, actualRight, split,
                leftCompatible, rightCompatible⟩ :=
              uniqueSeparatorFourLeftSearchFold_exists_cut
                left separator letters evaluated
            refine
              ⟨letter :: actualLeft, actualRight, ?_, ?_,
                rightCompatible⟩
            · simp [split]
            · constructor
              · simp [Ne.symm separatorHit, leftCompatible.1]
              · intro value member
                simp only [List.mem_cons] at member
                rcases member with equality | tailMember
                · subst value
                  exact leftHit
                · exact leftCompatible.2 value tailMember
          · rw [uniqueSeparatorFourEvalList,
              uniqueSeparatorFourEvalFrom_cons] at evaluated
            rw [show
              uniqueSeparatorFourSeparatorValuation
                  left separator letter = 3 by
                simp [uniqueSeparatorFourSeparatorValuation,
                  separatorHit, leftHit]] at evaluated
            simp only [uniqueSeparatorFourListStep] at evaluated
            exact False.elim <|
              uniqueSeparatorFourRightStart_ne_one
                left separator letters evaluated
  · rintro
      ⟨actualLeft, actualRight, rfl,
        leftCompatible, rightCompatible⟩
    exact uniqueSeparatorFourCompatibleSeparatorSplitFold
      left separator actualLeft actualRight
      leftCompatible rightCompatible

/-- Exact completeness-oriented characterization.  Evaluation is state `1`
iff there is exactly one separator and its actual prefix/suffix obey the
proposed support cut; the actual supports are consequently disjoint. -/
theorem uniqueSeparatorFourSeparatorEvalList_eq_one_iff_exact_cut
    {α : Type} [DecidableEq α] (left : List α) (separator : α)
    (letters : List α) :
    uniqueSeparatorFourEvalList
        (uniqueSeparatorFourSeparatorValuation left separator) letters =
        .value 1 ↔
      letters.count separator = 1 ∧
        ∃ actualLeft actualRight,
          letters = actualLeft ++ separator :: actualRight ∧
            UniqueSeparatorFourLeftCompatible
              left separator actualLeft ∧
            UniqueSeparatorFourRightCompatible
              left separator actualRight ∧
            UniqueSeparatorFourSupportsDisjoint
              actualLeft actualRight := by
  constructor
  · intro evaluated
    obtain
      ⟨actualLeft, actualRight, split,
        leftCompatible, rightCompatible⟩ :=
      (uniqueSeparatorFourSeparatorEvalList_eq_one_iff_exists_cut
        left separator letters).mp evaluated
    have countOne : letters.count separator = 1 := by
      rw [split, List.count_append, List.count_cons_self]
      rw [List.count_eq_zero.mpr leftCompatible.1,
        List.count_eq_zero.mpr rightCompatible.1]
    have disjoint :
        UniqueSeparatorFourSupportsDisjoint actualLeft actualRight := by
      intro letter leftMember rightMember
      exact rightCompatible.2 letter rightMember
        (leftCompatible.2 letter leftMember)
    exact
      ⟨countOne, actualLeft, actualRight, split,
        leftCompatible, rightCompatible, disjoint⟩
  · rintro
      ⟨_, actualLeft, actualRight, split,
        leftCompatible, rightCompatible, _⟩
    exact
      (uniqueSeparatorFourSeparatorEvalList_eq_one_iff_exists_cut
        left separator letters).mpr
          ⟨actualLeft, actualRight, split,
            leftCompatible, rightCompatible⟩

/-- Word-level form of the exact cut characterization. -/
theorem uniqueSeparatorFourSeparatorEval_eq_one_iff_exact_cut
    {α : Type} [DecidableEq α] (left : List α) (separator : α)
    (word : Word α) :
    uniqueSeparatorFour.semigroup.eval
        (uniqueSeparatorFourSeparatorValuation left separator) word =
        (1 : Fin 4) ↔
      word.toList.count separator = 1 ∧
        ∃ actualLeft actualRight,
          word.toList = actualLeft ++ separator :: actualRight ∧
            UniqueSeparatorFourLeftCompatible
              left separator actualLeft ∧
            UniqueSeparatorFourRightCompatible
              left separator actualRight ∧
            UniqueSeparatorFourSupportsDisjoint
              actualLeft actualRight := by
  have exactList :=
    uniqueSeparatorFourSeparatorEvalList_eq_one_iff_exact_cut
      left separator word.toList
  rw [uniqueSeparatorFourEvalList_toList] at exactList
  simpa using exactList

end SemigroupBasis.Examples

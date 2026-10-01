import SemigroupBasis.Examples.ConnectedComponentFour
import SemigroupBasis.Examples.ConnectedComponentFourComponents

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Extend `S4_70` multiplication by an external identity, so that semantic
detectors can also be evaluated on empty list factors. -/
def connectedComponentFourListStep :
    Option (Fin 4) → Fin 4 → Option (Fin 4)
  | none, next => some next
  | some current, next => some (connectedComponentFourMul current next)

/-- Evaluate a list from an arbitrary extended state. -/
def connectedComponentFourEvalFrom
    {α : Type} (initial : Option (Fin 4))
    (valuation : α → Fin 4) (letters : List α) :
    Option (Fin 4) :=
  letters.foldl
    (fun current letter =>
      connectedComponentFourListStep current (valuation letter))
    initial

/-- Evaluate a possibly empty list, starting at the external identity. -/
def connectedComponentFourEvalList
    {α : Type} (valuation : α → Fin 4) (letters : List α) :
    Option (Fin 4) :=
  connectedComponentFourEvalFrom none valuation letters

@[simp]
theorem connectedComponentFourEvalFrom_nil
    {α : Type} (initial : Option (Fin 4))
    (valuation : α → Fin 4) :
    connectedComponentFourEvalFrom initial valuation [] = initial :=
  rfl

@[simp]
theorem connectedComponentFourEvalFrom_cons
    {α : Type} (initial : Option (Fin 4))
    (valuation : α → Fin 4) (letter : α) (letters : List α) :
    connectedComponentFourEvalFrom initial valuation (letter :: letters) =
      connectedComponentFourEvalFrom
        (connectedComponentFourListStep initial (valuation letter))
        valuation letters :=
  rfl

theorem connectedComponentFourEvalFrom_append
    {α : Type} (initial : Option (Fin 4))
    (valuation : α → Fin 4) (left right : List α) :
    connectedComponentFourEvalFrom initial valuation (left ++ right) =
      connectedComponentFourEvalFrom
        (connectedComponentFourEvalFrom initial valuation left)
        valuation right := by
  simp [connectedComponentFourEvalFrom, List.foldl_append]

theorem connectedComponentFourEvalFrom_some
    {α : Type} (initial : Fin 4) (valuation : α → Fin 4)
    (letters : List α) :
    connectedComponentFourEvalFrom (some initial) valuation letters =
      some
        (letters.foldl
          (fun current letter =>
            connectedComponentFourMul current (valuation letter))
          initial) := by
  induction letters generalizing initial with
  | nil => rfl
  | cons letter letters ih =>
      simp only [connectedComponentFourEvalFrom_cons,
        connectedComponentFourListStep]
      exact ih (connectedComponentFourMul initial (valuation letter))

/-- The list evaluator agrees with semigroup evaluation on the nonempty list
underlying a word. -/
theorem connectedComponentFourEvalList_toList
    {α : Type} (valuation : α → Fin 4) (word : Word α) :
    connectedComponentFourEvalList valuation word.toList =
      some (connectedComponentFour.semigroup.eval valuation word) := by
  cases word with
  | mk head tail =>
      simp only [connectedComponentFourEvalList,
        connectedComponentFourEvalFrom_cons,
        connectedComponentFourListStep, Word.toList, Semigroup.eval]
      exact connectedComponentFourEvalFrom_some
        (valuation head) valuation tail

@[simp]
theorem connectedComponentFourMul_zero_left (next : Fin 4) :
    connectedComponentFourMul 0 next = 0 := by
  decide +revert

@[simp]
theorem connectedComponentFourMul_zero_right (current : Fin 4) :
    connectedComponentFourMul current 0 = 0 := by
  decide +revert

@[simp]
theorem connectedComponentFourMul_one_one :
    connectedComponentFourMul 1 1 = 0 := by
  decide

@[simp]
theorem connectedComponentFourMul_one_two :
    connectedComponentFourMul 1 2 = 0 := by
  decide

@[simp]
theorem connectedComponentFourMul_one_three :
    connectedComponentFourMul 1 3 = 1 := by
  decide

@[simp]
theorem connectedComponentFourMul_two_one :
    connectedComponentFourMul 2 1 = 1 := by
  decide

@[simp]
theorem connectedComponentFourMul_two_two :
    connectedComponentFourMul 2 2 = 2 := by
  decide

@[simp]
theorem connectedComponentFourMul_two_three :
    connectedComponentFourMul 2 3 = 1 := by
  decide

@[simp]
theorem connectedComponentFourMul_three_one :
    connectedComponentFourMul 3 1 = 0 := by
  decide

@[simp]
theorem connectedComponentFourMul_three_two :
    connectedComponentFourMul 3 2 = 0 := by
  decide

@[simp]
theorem connectedComponentFourMul_three_three :
    connectedComponentFourMul 3 3 = 3 := by
  decide

theorem connectedComponentFourEvalFrom_zero
    {α : Type} (valuation : α → Fin 4) (letters : List α) :
    connectedComponentFourEvalFrom (some 0) valuation letters =
      some 0 := by
  induction letters with
  | nil => rfl
  | cons letter letters ih =>
      simp only [connectedComponentFourEvalFrom_cons,
        connectedComponentFourListStep,
        connectedComponentFourMul_zero_left]
      exact ih

/-- Send one tested variable to zero and every other variable to the
right-phase idempotent. -/
def connectedComponentFourSupportValuation
    {α : Type} [DecidableEq α] (tested : α) : α → Fin 4 :=
  fun letter => if letter = tested then 0 else 3

theorem connectedComponentFourSupportFold_three
    {α : Type} [DecidableEq α] (tested : α) (letters : List α) :
    connectedComponentFourEvalFrom (some 3)
        (connectedComponentFourSupportValuation tested) letters =
      if tested ∈ letters then some 0 else some 3 := by
  induction letters with
  | nil => simp
  | cons letter letters ih =>
      by_cases hit : letter = tested
      · subst letter
        rw [connectedComponentFourEvalFrom_cons]
        rw [show
          connectedComponentFourSupportValuation tested tested = 0 by
            simp [connectedComponentFourSupportValuation]]
        simp only [connectedComponentFourListStep,
          connectedComponentFourMul_zero_right]
        rw [connectedComponentFourEvalFrom_zero]
        simp
      · have reverseDifferent : tested ≠ letter := Ne.symm hit
        rw [connectedComponentFourEvalFrom_cons]
        rw [show
          connectedComponentFourSupportValuation tested letter = 3 by
            simp [connectedComponentFourSupportValuation, hit]]
        simp only [connectedComponentFourListStep,
          connectedComponentFourMul_three_three]
        rw [ih]
        simp [reverseDifferent]

/-- The support valuation detects occurrence exactly, including the empty-list
case through the external identity state. -/
theorem connectedComponentFourSupportEvalList_eq_zero_iff
    {α : Type} [DecidableEq α] (tested : α) (letters : List α) :
    connectedComponentFourEvalList
        (connectedComponentFourSupportValuation tested) letters =
        some 0 ↔
      tested ∈ letters := by
  cases letters with
  | nil => simp [connectedComponentFourEvalList]
  | cons letter letters =>
      by_cases hit : letter = tested
      · subst letter
        rw [connectedComponentFourEvalList,
          connectedComponentFourEvalFrom_cons]
        rw [show
          connectedComponentFourSupportValuation tested tested = 0 by
            simp [connectedComponentFourSupportValuation]]
        simp only [connectedComponentFourListStep]
        rw [connectedComponentFourEvalFrom_zero]
        simp
      · have reverseDifferent : tested ≠ letter := Ne.symm hit
        rw [connectedComponentFourEvalList,
          connectedComponentFourEvalFrom_cons]
        rw [show
          connectedComponentFourSupportValuation tested letter = 3 by
            simp [connectedComponentFourSupportValuation, hit]]
        simp only [connectedComponentFourListStep]
        rw [connectedComponentFourSupportFold_three]
        simp [reverseDifferent]

/-- Semigroup evaluation at the support valuation is zero exactly when the
tested variable occurs in the word. -/
theorem connectedComponentFourSupportEval_eq_zero_iff
    {α : Type} [DecidableEq α] (tested : α) (word : Word α) :
    connectedComponentFour.semigroup.eval
        (connectedComponentFourSupportValuation tested) word =
        (0 : Fin 4) ↔
      tested ∈ word.toList := by
  have detected :=
    connectedComponentFourSupportEvalList_eq_zero_iff tested word.toList
  rw [connectedComponentFourEvalList_toList] at detected
  simpa using detected

/-- Equal term functions in `S4_70` have equal support. -/
theorem connectedComponentFourEqualEval_support_iff
    {α : Type} [DecidableEq α] (left right : Word α)
    (equalEval :
      ∀ valuation : α → Fin 4,
        connectedComponentFour.semigroup.eval valuation left =
          connectedComponentFour.semigroup.eval valuation right)
    (tested : α) :
    tested ∈ left.toList ↔ tested ∈ right.toList := by
  have evaluated :=
    equalEval (connectedComponentFourSupportValuation tested)
  constructor
  · intro member
    have leftZero :
        connectedComponentFour.semigroup.eval
            (connectedComponentFourSupportValuation tested) left =
          (0 : Fin 4) :=
      (connectedComponentFourSupportEval_eq_zero_iff tested left).2 member
    have rightZero :
        connectedComponentFour.semigroup.eval
            (connectedComponentFourSupportValuation tested) right =
          (0 : Fin 4) :=
      evaluated.symm.trans leftZero
    exact
      (connectedComponentFourSupportEval_eq_zero_iff tested right).1
        rightZero
  · intro member
    have rightZero :
        connectedComponentFour.semigroup.eval
            (connectedComponentFourSupportValuation tested) right =
          (0 : Fin 4) :=
      (connectedComponentFourSupportEval_eq_zero_iff tested right).2 member
    have leftZero :
        connectedComponentFour.semigroup.eval
            (connectedComponentFourSupportValuation tested) left =
          (0 : Fin 4) :=
      evaluated.trans rightZero
    exact
      (connectedComponentFourSupportEval_eq_zero_iff tested left).1
        leftZero

/-- Every identity valid in `S4_70` preserves support. -/
theorem connectedComponentFourValid_support_iff
    {α : Type} [DecidableEq α] (identity : Identity α)
    (valid : identity.SatisfiedBy connectedComponentFour.semigroup)
    (tested : α) :
    tested ∈ identity.lhs.toList ↔ tested ∈ identity.rhs.toList :=
  connectedComponentFourEqualEval_support_iff
    identity.lhs identity.rhs valid tested

/-- The semantic form of a support-disjoint cut: a nonempty left phase uses
only variables from the proposed prefix union, and a nonempty right phase
uses none of them. -/
def connectedComponentFourPrefixUnionCutCompatible
    {α : Type} (prefixSupport letters : List α) : Prop :=
  ∃ actualLeft actualRight,
    letters = actualLeft ++ actualRight ∧
      actualLeft ≠ [] ∧
      actualRight ≠ [] ∧
      (∀ letter, letter ∈ actualLeft → letter ∈ prefixSupport) ∧
      (∀ letter, letter ∈ actualRight → letter ∉ prefixSupport)

/-- An exact support-disjoint prefix cut. The displayed left factor has
exactly `prefixSupport` as its support. -/
def connectedComponentFourPrefixUnionCut
    {α : Type} (prefixSupport letters : List α) : Prop :=
  ∃ actualLeft actualRight,
    letters = actualLeft ++ actualRight ∧
      actualLeft ≠ [] ∧
      actualRight ≠ [] ∧
      (∀ letter, letter ∈ actualLeft ↔ letter ∈ prefixSupport) ∧
      (∀ letter, letter ∈ actualLeft → letter ∉ actualRight)

/-- Variables in the proposed prefix union are assigned state `2`; all other
variables are assigned state `3`. Their product is zero-based state `1`. -/
def connectedComponentFourPrefixUnionValuation
    {α : Type} [DecidableEq α] (prefixSupport : List α) :
    α → Fin 4 :=
  fun letter => if letter ∈ prefixSupport then 2 else 3

@[simp]
theorem connectedComponentFourPrefixUnionValuation_mem
    {α : Type} [DecidableEq α] {prefixSupport : List α} {letter : α}
    (member : letter ∈ prefixSupport) :
    connectedComponentFourPrefixUnionValuation prefixSupport letter = 2 := by
  simp [connectedComponentFourPrefixUnionValuation, member]

@[simp]
theorem connectedComponentFourPrefixUnionValuation_not_mem
    {α : Type} [DecidableEq α] {prefixSupport : List α} {letter : α}
    (notMember : letter ∉ prefixSupport) :
    connectedComponentFourPrefixUnionValuation prefixSupport letter = 3 := by
  simp [connectedComponentFourPrefixUnionValuation, notMember]

theorem connectedComponentFourPrefixLeftFoldFromTwo
    {α : Type} [DecidableEq α] (prefixSupport letters : List α)
    (supported :
      ∀ letter, letter ∈ letters → letter ∈ prefixSupport) :
    connectedComponentFourEvalFrom (some 2)
        (connectedComponentFourPrefixUnionValuation prefixSupport) letters =
      some 2 := by
  induction letters with
  | nil => rfl
  | cons letter letters ih =>
      have member : letter ∈ prefixSupport :=
        supported letter (by simp)
      have tailSupported :
          ∀ value, value ∈ letters → value ∈ prefixSupport := by
        intro value valueMember
        exact supported value (List.Mem.tail letter valueMember)
      simp only [connectedComponentFourEvalFrom_cons,
        connectedComponentFourPrefixUnionValuation_mem member,
        connectedComponentFourListStep,
        connectedComponentFourMul_two_two]
      exact ih tailSupported

theorem connectedComponentFourPrefixLeftFold
    {α : Type} [DecidableEq α] (prefixSupport letters : List α)
    (nonempty : letters ≠ [])
    (supported :
      ∀ letter, letter ∈ letters → letter ∈ prefixSupport) :
    connectedComponentFourEvalList
        (connectedComponentFourPrefixUnionValuation prefixSupport) letters =
      some 2 := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons letter letters =>
      have member : letter ∈ prefixSupport :=
        supported letter (by simp)
      simp only [connectedComponentFourEvalList,
        connectedComponentFourEvalFrom_cons,
        connectedComponentFourPrefixUnionValuation_mem member,
        connectedComponentFourListStep]
      exact connectedComponentFourPrefixLeftFoldFromTwo
        prefixSupport letters (by
          intro value valueMember
          exact supported value (List.Mem.tail letter valueMember))

/-- Once state `1` has been reached, it survives exactly through the
state-`3` right phase. -/
theorem connectedComponentFourPrefixRightFold_eq_one_iff
    {α : Type} [DecidableEq α] (prefixSupport letters : List α) :
    connectedComponentFourEvalFrom (some 1)
        (connectedComponentFourPrefixUnionValuation prefixSupport) letters =
        some 1 ↔
      ∀ letter, letter ∈ letters → letter ∉ prefixSupport := by
  induction letters with
  | nil => simp
  | cons letter letters ih =>
      by_cases member : letter ∈ prefixSupport
      · rw [connectedComponentFourEvalFrom_cons]
        rw [connectedComponentFourPrefixUnionValuation_mem member]
        simp only [connectedComponentFourListStep,
          connectedComponentFourMul_one_two]
        rw [connectedComponentFourEvalFrom_zero]
        simp [member]
      · rw [connectedComponentFourEvalFrom_cons]
        rw [connectedComponentFourPrefixUnionValuation_not_mem member]
        simp only [connectedComponentFourListStep,
          connectedComponentFourMul_one_three]
        rw [ih]
        simp [member]

/-- Starting in state `3` can never produce state `1` under a `2/3`
prefix-union valuation. -/
theorem connectedComponentFourPrefixOutsideStart_ne_one
    {α : Type} [DecidableEq α] (prefixSupport letters : List α) :
    connectedComponentFourEvalFrom (some 3)
        (connectedComponentFourPrefixUnionValuation prefixSupport) letters ≠
      some 1 := by
  induction letters with
  | nil => simp
  | cons letter letters ih =>
      by_cases member : letter ∈ prefixSupport
      · rw [connectedComponentFourEvalFrom_cons]
        rw [connectedComponentFourPrefixUnionValuation_mem member]
        simp only [connectedComponentFourListStep,
          connectedComponentFourMul_three_two]
        rw [connectedComponentFourEvalFrom_zero]
        simp
      · rw [connectedComponentFourEvalFrom_cons]
        rw [connectedComponentFourPrefixUnionValuation_not_mem member]
        simp only [connectedComponentFourListStep,
          connectedComponentFourMul_three_three]
        exact ih

theorem connectedComponentFourPrefixRightFoldFromTwo
    {α : Type} [DecidableEq α] (prefixSupport letters : List α)
    (nonempty : letters ≠ [])
    (unsupported :
      ∀ letter, letter ∈ letters → letter ∉ prefixSupport) :
    connectedComponentFourEvalFrom (some 2)
        (connectedComponentFourPrefixUnionValuation prefixSupport) letters =
      some 1 := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons letter letters =>
      have notMember : letter ∉ prefixSupport :=
        unsupported letter (by simp)
      simp only [connectedComponentFourEvalFrom_cons,
        connectedComponentFourPrefixUnionValuation_not_mem notMember,
        connectedComponentFourListStep,
        connectedComponentFourMul_two_three]
      exact
        (connectedComponentFourPrefixRightFold_eq_one_iff
          prefixSupport letters).2 (by
            intro value valueMember
            exact unsupported value
              (List.Mem.tail letter valueMember))

/-- Search from the left phase: a state-`1` result has a (possibly empty)
remaining left block followed by a nonempty right block. -/
theorem connectedComponentFourPrefixLeftSearch_exists_cut
    {α : Type} [DecidableEq α] (prefixSupport letters : List α)
    (evaluated :
      connectedComponentFourEvalFrom (some 2)
          (connectedComponentFourPrefixUnionValuation prefixSupport)
          letters =
        some 1) :
    ∃ actualLeft actualRight,
      letters = actualLeft ++ actualRight ∧
        (∀ letter, letter ∈ actualLeft → letter ∈ prefixSupport) ∧
        actualRight ≠ [] ∧
        (∀ letter, letter ∈ actualRight → letter ∉ prefixSupport) := by
  induction letters with
  | nil =>
      simp at evaluated
  | cons letter letters ih =>
      by_cases member : letter ∈ prefixSupport
      · rw [connectedComponentFourEvalFrom_cons] at evaluated
        rw [connectedComponentFourPrefixUnionValuation_mem member] at evaluated
        simp only [connectedComponentFourListStep,
          connectedComponentFourMul_two_two] at evaluated
        obtain
          ⟨actualLeft, actualRight, split, leftSupported,
            rightNonempty, rightUnsupported⟩ :=
          ih evaluated
        refine
          ⟨letter :: actualLeft, actualRight, ?_, ?_,
            rightNonempty, rightUnsupported⟩
        · simp [split]
        · intro value valueMember
          simp only [List.mem_cons] at valueMember
          rcases valueMember with equality | tailMember
          · subst value
            exact member
          · exact leftSupported value tailMember
      · rw [connectedComponentFourEvalFrom_cons] at evaluated
        rw [connectedComponentFourPrefixUnionValuation_not_mem member]
          at evaluated
        simp only [connectedComponentFourListStep,
          connectedComponentFourMul_two_three] at evaluated
        have rightUnsupported :=
          (connectedComponentFourPrefixRightFold_eq_one_iff
            prefixSupport letters).1 evaluated
        exact
          ⟨[], letter :: letters, by simp, by simp, by simp,
            by
              intro value valueMember
              simp only [List.mem_cons] at valueMember
              rcases valueMember with equality | tailMember
              · subst value
                exact member
              · exact rightUnsupported value tailMember⟩

/-- Exact phase characterization of the `2/3` prefix-union valuation. -/
theorem connectedComponentFourPrefixUnionEvalList_eq_one_iff_compatible
    {α : Type} [DecidableEq α] (prefixSupport letters : List α) :
    connectedComponentFourEvalList
        (connectedComponentFourPrefixUnionValuation prefixSupport) letters =
        some 1 ↔
      connectedComponentFourPrefixUnionCutCompatible
        prefixSupport letters := by
  constructor
  · intro evaluated
    cases letters with
    | nil =>
        simp [connectedComponentFourEvalList] at evaluated
    | cons letter letters =>
        by_cases member : letter ∈ prefixSupport
        · rw [connectedComponentFourEvalList,
            connectedComponentFourEvalFrom_cons] at evaluated
          rw [connectedComponentFourPrefixUnionValuation_mem member]
            at evaluated
          simp only [connectedComponentFourListStep] at evaluated
          obtain
            ⟨actualLeft, actualRight, split, leftSupported,
              rightNonempty, rightUnsupported⟩ :=
            connectedComponentFourPrefixLeftSearch_exists_cut
              prefixSupport letters evaluated
          refine
            ⟨letter :: actualLeft, actualRight, ?_, by simp,
              rightNonempty, ?_, rightUnsupported⟩
          · simp [split]
          · intro value valueMember
            simp only [List.mem_cons] at valueMember
            rcases valueMember with equality | tailMember
            · subst value
              exact member
            · exact leftSupported value tailMember
        · rw [connectedComponentFourEvalList,
            connectedComponentFourEvalFrom_cons] at evaluated
          rw [connectedComponentFourPrefixUnionValuation_not_mem member]
            at evaluated
          simp only [connectedComponentFourListStep] at evaluated
          exact False.elim <|
            connectedComponentFourPrefixOutsideStart_ne_one
              prefixSupport letters evaluated
  · rintro
      ⟨actualLeft, actualRight, rfl, leftNonempty,
        rightNonempty, leftSupported, rightUnsupported⟩
    rw [connectedComponentFourEvalList,
      connectedComponentFourEvalFrom_append]
    change
      connectedComponentFourEvalFrom
          (connectedComponentFourEvalList
            (connectedComponentFourPrefixUnionValuation prefixSupport)
            actualLeft)
          (connectedComponentFourPrefixUnionValuation prefixSupport)
          actualRight =
        some 1
    rw [connectedComponentFourPrefixLeftFold
      prefixSupport actualLeft leftNonempty leftSupported]
    exact connectedComponentFourPrefixRightFoldFromTwo
      prefixSupport actualRight rightNonempty rightUnsupported

/-- With the necessary coverage hypothesis, state `1` detects the exact
support of the left factor and a support-disjoint cut. -/
theorem connectedComponentFourPrefixUnionEvalList_eq_one_iff
    {α : Type} [DecidableEq α] (prefixSupport letters : List α)
    (covered :
      ∀ letter, letter ∈ prefixSupport → letter ∈ letters) :
    connectedComponentFourEvalList
        (connectedComponentFourPrefixUnionValuation prefixSupport) letters =
        some 1 ↔
      connectedComponentFourPrefixUnionCut prefixSupport letters := by
  rw [connectedComponentFourPrefixUnionEvalList_eq_one_iff_compatible]
  constructor
  · rintro
      ⟨actualLeft, actualRight, split, leftNonempty,
        rightNonempty, leftSupported, rightUnsupported⟩
    have leftExact :
        ∀ letter, letter ∈ actualLeft ↔ letter ∈ prefixSupport := by
      intro letter
      constructor
      · exact leftSupported letter
      · intro supportMember
        have letterMember : letter ∈ letters :=
          covered letter supportMember
        rw [split] at letterMember
        rcases List.mem_append.mp letterMember with
          leftMember | rightMember
        · exact leftMember
        · exact False.elim <|
            rightUnsupported letter rightMember supportMember
    have disjoint :
        ∀ letter, letter ∈ actualLeft → letter ∉ actualRight := by
      intro letter leftMember rightMember
      exact rightUnsupported letter rightMember
        ((leftExact letter).1 leftMember)
    exact
      ⟨actualLeft, actualRight, split, leftNonempty, rightNonempty,
        leftExact, disjoint⟩
  · rintro
      ⟨actualLeft, actualRight, split, leftNonempty,
        rightNonempty, leftExact, disjoint⟩
    refine
      ⟨actualLeft, actualRight, split, leftNonempty, rightNonempty,
        fun letter member => (leftExact letter).1 member, ?_⟩
    intro letter rightMember supportMember
    exact disjoint letter ((leftExact letter).2 supportMember) rightMember

/-- Word-level exact prefix-union cut detector. -/
theorem connectedComponentFourPrefixUnionEval_eq_one_iff
    {α : Type} [DecidableEq α] (prefixSupport : List α)
    (word : Word α)
    (covered :
      ∀ letter, letter ∈ prefixSupport → letter ∈ word.toList) :
    connectedComponentFour.semigroup.eval
        (connectedComponentFourPrefixUnionValuation prefixSupport) word =
        (1 : Fin 4) ↔
      connectedComponentFourPrefixUnionCut prefixSupport word.toList := by
  have detected :=
    connectedComponentFourPrefixUnionEvalList_eq_one_iff
      prefixSupport word.toList covered
  rw [connectedComponentFourEvalList_toList] at detected
  simpa using detected

/-- Equal `S4_70` term functions preserve every exact prefix-union cut. -/
theorem connectedComponentFourEqualEval_prefixUnionCut_iff
    {α : Type} [DecidableEq α] (source target : Word α)
    (equalEval :
      ∀ valuation : α → Fin 4,
        connectedComponentFour.semigroup.eval valuation source =
          connectedComponentFour.semigroup.eval valuation target)
    (prefixSupport : List α)
    (covered :
      ∀ letter, letter ∈ prefixSupport → letter ∈ source.toList) :
    connectedComponentFourPrefixUnionCut
        prefixSupport source.toList ↔
      connectedComponentFourPrefixUnionCut
        prefixSupport target.toList := by
  have targetCovered :
      ∀ letter, letter ∈ prefixSupport → letter ∈ target.toList := by
    intro letter supportMember
    exact
      (connectedComponentFourEqualEval_support_iff
        source target equalEval letter).1
        (covered letter supportMember)
  have sourceDetected :=
    connectedComponentFourPrefixUnionEval_eq_one_iff
      prefixSupport source covered
  have targetDetected :=
    connectedComponentFourPrefixUnionEval_eq_one_iff
      prefixSupport target targetCovered
  constructor
  · intro sourceCut
    have sourceOne := sourceDetected.2 sourceCut
    have targetOne :=
      (equalEval
        (connectedComponentFourPrefixUnionValuation
          prefixSupport)).symm.trans sourceOne
    exact targetDetected.1 targetOne
  · intro targetCut
    have targetOne := targetDetected.2 targetCut
    have sourceOne :=
      (equalEval
        (connectedComponentFourPrefixUnionValuation
          prefixSupport)).trans targetOne
    exact sourceDetected.1 sourceOne

/-- The suffix condition after a tested unary component: the tested variable
does not recur, and no variable from the preceding prefix union occurs. -/
def connectedComponentFourUnaryRightCompatible
    {α : Type} (prefixSupport : List α) (tested : α)
    (letters : List α) : Prop :=
  tested ∉ letters ∧
    ∀ letter, letter ∈ letters → letter ∉ prefixSupport

/-- A boundary occurrence of `tested`, preceded only by prefix-union
variables and followed by variables outside both the prefix union and the
tested unary support. -/
def connectedComponentFourUnaryCutCompatible
    {α : Type} (prefixSupport : List α) (tested : α)
    (letters : List α) : Prop :=
  ∃ actualLeft actualRight,
    letters = actualLeft ++ tested :: actualRight ∧
      (∀ letter, letter ∈ actualLeft → letter ∈ prefixSupport) ∧
      connectedComponentFourUnaryRightCompatible
        prefixSupport tested actualRight

/-- Exact unary-component signature after a proposed prefix union. -/
def connectedComponentFourUnaryCut
    {α : Type} (prefixSupport : List α) (tested : α)
    (letters : List α) : Prop :=
  ∃ actualLeft actualRight,
    letters = actualLeft ++ tested :: actualRight ∧
      (∀ letter, letter ∈ actualLeft ↔ letter ∈ prefixSupport) ∧
      tested ∉ actualRight ∧
      (∀ letter, letter ∈ actualLeft → letter ∉ actualRight)

/-- Unary boundary valuation: preceding component supports use state `2`, the
tested variable uses state `1`, and later supports use state `3`. A second
tested occurrence kills state `1`. -/
def connectedComponentFourUnaryValuation
    {α : Type} [DecidableEq α] (prefixSupport : List α)
    (tested : α) : α → Fin 4 :=
  fun letter =>
    if letter = tested then 1
    else if letter ∈ prefixSupport then 2
    else 3

@[simp]
theorem connectedComponentFourUnaryValuation_tested
    {α : Type} [DecidableEq α] (prefixSupport : List α)
    (tested : α) :
    connectedComponentFourUnaryValuation prefixSupport tested tested = 1 := by
  simp [connectedComponentFourUnaryValuation]

@[simp]
theorem connectedComponentFourUnaryValuation_prefix
    {α : Type} [DecidableEq α] {prefixSupport : List α}
    {tested letter : α}
    (different : letter ≠ tested)
    (member : letter ∈ prefixSupport) :
    connectedComponentFourUnaryValuation prefixSupport tested letter = 2 := by
  simp [connectedComponentFourUnaryValuation, different, member]

@[simp]
theorem connectedComponentFourUnaryValuation_suffix
    {α : Type} [DecidableEq α] {prefixSupport : List α}
    {tested letter : α}
    (different : letter ≠ tested)
    (notMember : letter ∉ prefixSupport) :
    connectedComponentFourUnaryValuation prefixSupport tested letter = 3 := by
  simp [connectedComponentFourUnaryValuation, different, notMember]

theorem connectedComponentFourUnaryLeftFoldFromTwo
    {α : Type} [DecidableEq α] (prefixSupport : List α)
    (tested : α) (letters : List α)
    (testedNotPrefix : tested ∉ prefixSupport)
    (supported :
      ∀ letter, letter ∈ letters → letter ∈ prefixSupport) :
    connectedComponentFourEvalFrom (some 2)
        (connectedComponentFourUnaryValuation prefixSupport tested)
        letters =
      some 2 := by
  induction letters with
  | nil => rfl
  | cons letter letters ih =>
      have member : letter ∈ prefixSupport :=
        supported letter (by simp)
      have different : letter ≠ tested := by
        intro equality
        subst letter
        exact testedNotPrefix member
      have tailSupported :
          ∀ value, value ∈ letters → value ∈ prefixSupport := by
        intro value valueMember
        exact supported value (List.Mem.tail letter valueMember)
      simp only [connectedComponentFourEvalFrom_cons,
        connectedComponentFourUnaryValuation_prefix different member,
        connectedComponentFourListStep,
        connectedComponentFourMul_two_two]
      exact ih tailSupported

theorem connectedComponentFourUnaryLeftFold
    {α : Type} [DecidableEq α] (prefixSupport : List α)
    (tested : α) (letters : List α)
    (testedNotPrefix : tested ∉ prefixSupport)
    (nonempty : letters ≠ [])
    (supported :
      ∀ letter, letter ∈ letters → letter ∈ prefixSupport) :
    connectedComponentFourEvalList
        (connectedComponentFourUnaryValuation prefixSupport tested)
        letters =
      some 2 := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons letter letters =>
      have member : letter ∈ prefixSupport :=
        supported letter (by simp)
      have different : letter ≠ tested := by
        intro equality
        subst letter
        exact testedNotPrefix member
      simp only [connectedComponentFourEvalList,
        connectedComponentFourEvalFrom_cons,
        connectedComponentFourUnaryValuation_prefix different member,
        connectedComponentFourListStep]
      exact connectedComponentFourUnaryLeftFoldFromTwo
        prefixSupport tested letters testedNotPrefix (by
          intro value valueMember
          exact supported value (List.Mem.tail letter valueMember))

/-- State `1` survives the unary suffix exactly while neither the tested
variable nor a prefix-union variable occurs. -/
theorem connectedComponentFourUnaryRightFold_eq_one_iff
    {α : Type} [DecidableEq α] (prefixSupport : List α)
    (tested : α) (letters : List α) :
    connectedComponentFourEvalFrom (some 1)
        (connectedComponentFourUnaryValuation prefixSupport tested)
        letters =
        some 1 ↔
      connectedComponentFourUnaryRightCompatible
        prefixSupport tested letters := by
  induction letters with
  | nil =>
      simp [connectedComponentFourUnaryRightCompatible]
  | cons letter letters ih =>
      by_cases testedHit : letter = tested
      · subst letter
        rw [connectedComponentFourEvalFrom_cons]
        rw [connectedComponentFourUnaryValuation_tested]
        simp only [connectedComponentFourListStep,
          connectedComponentFourMul_one_one]
        rw [connectedComponentFourEvalFrom_zero]
        simp [connectedComponentFourUnaryRightCompatible]
      · by_cases prefixHit : letter ∈ prefixSupport
        · rw [connectedComponentFourEvalFrom_cons]
          rw [connectedComponentFourUnaryValuation_prefix
            testedHit prefixHit]
          simp only [connectedComponentFourListStep,
            connectedComponentFourMul_one_two]
          rw [connectedComponentFourEvalFrom_zero]
          simp [connectedComponentFourUnaryRightCompatible,
            prefixHit]
        · rw [connectedComponentFourEvalFrom_cons]
          rw [connectedComponentFourUnaryValuation_suffix
            testedHit prefixHit]
          simp only [connectedComponentFourListStep,
            connectedComponentFourMul_one_three]
          rw [ih]
          simp [connectedComponentFourUnaryRightCompatible,
            Ne.symm testedHit, prefixHit]

/-- Starting in state `3` can never recover state `1` under a unary boundary
valuation. -/
theorem connectedComponentFourUnaryOutsideStart_ne_one
    {α : Type} [DecidableEq α] (prefixSupport : List α)
    (tested : α) (letters : List α) :
    connectedComponentFourEvalFrom (some 3)
        (connectedComponentFourUnaryValuation prefixSupport tested)
        letters ≠
      some 1 := by
  induction letters with
  | nil => simp
  | cons letter letters ih =>
      by_cases testedHit : letter = tested
      · subst letter
        rw [connectedComponentFourEvalFrom_cons]
        rw [connectedComponentFourUnaryValuation_tested]
        simp only [connectedComponentFourListStep,
          connectedComponentFourMul_three_one]
        rw [connectedComponentFourEvalFrom_zero]
        simp
      · by_cases prefixHit : letter ∈ prefixSupport
        · rw [connectedComponentFourEvalFrom_cons]
          rw [connectedComponentFourUnaryValuation_prefix
            testedHit prefixHit]
          simp only [connectedComponentFourListStep,
            connectedComponentFourMul_three_two]
          rw [connectedComponentFourEvalFrom_zero]
          simp
        · rw [connectedComponentFourEvalFrom_cons]
          rw [connectedComponentFourUnaryValuation_suffix
            testedHit prefixHit]
          simp only [connectedComponentFourListStep,
            connectedComponentFourMul_three_three]
          exact ih

/-- Search from the unary left phase. The occurrence hypothesis rules out the
ordinary `2 * 3 = 1` cut and forces the transition to be the tested state
`1`. -/
theorem connectedComponentFourUnaryLeftSearch_exists_cut
    {α : Type} [DecidableEq α] (prefixSupport : List α)
    (tested : α) (letters : List α)
    (testedOccurs : tested ∈ letters)
    (evaluated :
      connectedComponentFourEvalFrom (some 2)
          (connectedComponentFourUnaryValuation prefixSupport tested)
          letters =
        some 1) :
    ∃ actualLeft actualRight,
      letters = actualLeft ++ tested :: actualRight ∧
        (∀ letter, letter ∈ actualLeft → letter ∈ prefixSupport) ∧
        connectedComponentFourUnaryRightCompatible
          prefixSupport tested actualRight := by
  induction letters with
  | nil =>
      simp at testedOccurs
  | cons letter letters ih =>
      by_cases testedHit : letter = tested
      · subst letter
        rw [connectedComponentFourEvalFrom_cons] at evaluated
        rw [connectedComponentFourUnaryValuation_tested] at evaluated
        simp only [connectedComponentFourListStep,
          connectedComponentFourMul_two_one] at evaluated
        have rightCompatible :=
          (connectedComponentFourUnaryRightFold_eq_one_iff
            prefixSupport tested letters).1 evaluated
        exact ⟨[], letters, by simp, by simp, rightCompatible⟩
      · by_cases prefixHit : letter ∈ prefixSupport
        · have testedInTail : tested ∈ letters := by
            simpa [testedHit, Ne.symm testedHit] using testedOccurs
          rw [connectedComponentFourEvalFrom_cons] at evaluated
          rw [connectedComponentFourUnaryValuation_prefix
            testedHit prefixHit] at evaluated
          simp only [connectedComponentFourListStep,
            connectedComponentFourMul_two_two] at evaluated
          obtain
            ⟨actualLeft, actualRight, split,
              leftSupported, rightCompatible⟩ :=
            ih testedInTail evaluated
          refine
            ⟨letter :: actualLeft, actualRight, ?_, ?_,
              rightCompatible⟩
          · simp [split]
          · intro value valueMember
            simp only [List.mem_cons] at valueMember
            rcases valueMember with equality | tailMember
            · subst value
              exact prefixHit
            · exact leftSupported value tailMember
        · have testedInTail : tested ∈ letters := by
            simpa [testedHit, Ne.symm testedHit] using testedOccurs
          rw [connectedComponentFourEvalFrom_cons] at evaluated
          rw [connectedComponentFourUnaryValuation_suffix
            testedHit prefixHit] at evaluated
          simp only [connectedComponentFourListStep,
            connectedComponentFourMul_two_three] at evaluated
          have rightCompatible :=
            (connectedComponentFourUnaryRightFold_eq_one_iff
              prefixSupport tested letters).1 evaluated
          exact False.elim (rightCompatible.1 testedInTail)

/-- Exact phase characterization of the unary boundary valuation, assuming
the tested variable occurs somewhere in the word. -/
theorem connectedComponentFourUnaryEvalList_eq_one_iff_compatible
    {α : Type} [DecidableEq α] (prefixSupport : List α)
    (tested : α) (letters : List α)
    (testedNotPrefix : tested ∉ prefixSupport)
    (testedOccurs : tested ∈ letters) :
    connectedComponentFourEvalList
        (connectedComponentFourUnaryValuation prefixSupport tested)
        letters =
        some 1 ↔
      connectedComponentFourUnaryCutCompatible
        prefixSupport tested letters := by
  constructor
  · intro evaluated
    cases letters with
    | nil =>
        simp at testedOccurs
    | cons letter letters =>
        by_cases testedHit : letter = tested
        · subst letter
          rw [connectedComponentFourEvalList,
            connectedComponentFourEvalFrom_cons] at evaluated
          rw [connectedComponentFourUnaryValuation_tested] at evaluated
          simp only [connectedComponentFourListStep] at evaluated
          have rightCompatible :=
            (connectedComponentFourUnaryRightFold_eq_one_iff
              prefixSupport tested letters).1 evaluated
          exact ⟨[], letters, by simp, by simp, rightCompatible⟩
        · by_cases prefixHit : letter ∈ prefixSupport
          · have testedInTail : tested ∈ letters := by
              simpa [testedHit, Ne.symm testedHit] using testedOccurs
            rw [connectedComponentFourEvalList,
              connectedComponentFourEvalFrom_cons] at evaluated
            rw [connectedComponentFourUnaryValuation_prefix
              testedHit prefixHit] at evaluated
            simp only [connectedComponentFourListStep] at evaluated
            obtain
              ⟨actualLeft, actualRight, split,
                leftSupported, rightCompatible⟩ :=
              connectedComponentFourUnaryLeftSearch_exists_cut
                prefixSupport tested letters testedInTail evaluated
            refine
              ⟨letter :: actualLeft, actualRight, ?_, ?_,
                rightCompatible⟩
            · simp [split]
            · intro value valueMember
              simp only [List.mem_cons] at valueMember
              rcases valueMember with equality | tailMember
              · subst value
                exact prefixHit
              · exact leftSupported value tailMember
          · rw [connectedComponentFourEvalList,
              connectedComponentFourEvalFrom_cons] at evaluated
            rw [connectedComponentFourUnaryValuation_suffix
              testedHit prefixHit] at evaluated
            simp only [connectedComponentFourListStep] at evaluated
            exact False.elim <|
              connectedComponentFourUnaryOutsideStart_ne_one
                prefixSupport tested letters evaluated
  · rintro
      ⟨actualLeft, actualRight, rfl,
        leftSupported, rightCompatible⟩
    rw [connectedComponentFourEvalList,
      connectedComponentFourEvalFrom_append]
    change
      connectedComponentFourEvalFrom
          (connectedComponentFourEvalList
            (connectedComponentFourUnaryValuation prefixSupport tested)
            actualLeft)
          (connectedComponentFourUnaryValuation prefixSupport tested)
          (tested :: actualRight) =
        some 1
    by_cases leftEmpty : actualLeft = []
    · subst actualLeft
      simp only [connectedComponentFourEvalList,
        connectedComponentFourEvalFrom_nil,
        connectedComponentFourEvalFrom_cons,
        connectedComponentFourUnaryValuation_tested,
        connectedComponentFourListStep]
      exact
        (connectedComponentFourUnaryRightFold_eq_one_iff
          prefixSupport tested actualRight).2 rightCompatible
    · rw [connectedComponentFourUnaryLeftFold
        prefixSupport tested actualLeft testedNotPrefix
        leftEmpty leftSupported]
      simp only [connectedComponentFourEvalFrom_cons,
        connectedComponentFourUnaryValuation_tested,
        connectedComponentFourListStep,
        connectedComponentFourMul_two_one]
      exact
        (connectedComponentFourUnaryRightFold_eq_one_iff
          prefixSupport tested actualRight).2 rightCompatible

/-- With prefix coverage, state `1` detects an exact unary component after
the exact displayed prefix union. -/
theorem connectedComponentFourUnaryEvalList_eq_one_iff
    {α : Type} [DecidableEq α] (prefixSupport : List α)
    (tested : α) (letters : List α)
    (testedNotPrefix : tested ∉ prefixSupport)
    (testedOccurs : tested ∈ letters)
    (covered :
      ∀ letter, letter ∈ prefixSupport → letter ∈ letters) :
    connectedComponentFourEvalList
        (connectedComponentFourUnaryValuation prefixSupport tested)
        letters =
        some 1 ↔
      connectedComponentFourUnaryCut
        prefixSupport tested letters := by
  rw [connectedComponentFourUnaryEvalList_eq_one_iff_compatible
    prefixSupport tested letters testedNotPrefix testedOccurs]
  constructor
  · rintro
      ⟨actualLeft, actualRight, split,
        leftSupported, rightCompatible⟩
    have leftExact :
        ∀ letter, letter ∈ actualLeft ↔ letter ∈ prefixSupport := by
      intro letter
      constructor
      · exact leftSupported letter
      · intro supportMember
        have letterMember : letter ∈ letters :=
          covered letter supportMember
        rw [split] at letterMember
        rcases List.mem_append.mp letterMember with
          leftMember | suffixMember
        · exact leftMember
        · rcases List.mem_cons.mp suffixMember with
            testedEquality | rightMember
          · subst letter
            exact False.elim (testedNotPrefix supportMember)
          · exact False.elim <|
              rightCompatible.2 letter rightMember supportMember
    have disjoint :
        ∀ letter, letter ∈ actualLeft → letter ∉ actualRight := by
      intro letter leftMember rightMember
      exact rightCompatible.2 letter rightMember
        ((leftExact letter).1 leftMember)
    exact
      ⟨actualLeft, actualRight, split, leftExact,
        rightCompatible.1, disjoint⟩
  · rintro
      ⟨actualLeft, actualRight, split, leftExact,
        testedAbsent, disjoint⟩
    refine
      ⟨actualLeft, actualRight, split,
        fun letter member => (leftExact letter).1 member,
        testedAbsent, ?_⟩
    intro letter rightMember supportMember
    exact disjoint letter ((leftExact letter).2 supportMember) rightMember

/-- Word-level exact unary-component detector. -/
theorem connectedComponentFourUnaryEval_eq_one_iff
    {α : Type} [DecidableEq α] (prefixSupport : List α)
    (tested : α) (word : Word α)
    (testedNotPrefix : tested ∉ prefixSupport)
    (testedOccurs : tested ∈ word.toList)
    (covered :
      ∀ letter, letter ∈ prefixSupport → letter ∈ word.toList) :
    connectedComponentFour.semigroup.eval
        (connectedComponentFourUnaryValuation prefixSupport tested) word =
        (1 : Fin 4) ↔
      connectedComponentFourUnaryCut
        prefixSupport tested word.toList := by
  have detected :=
    connectedComponentFourUnaryEvalList_eq_one_iff
      prefixSupport tested word.toList testedNotPrefix
      testedOccurs covered
  rw [connectedComponentFourEvalList_toList] at detected
  simpa using detected

/-- List-evaluator form of the unary `x` detector. -/
@[simp]
theorem connectedComponentFourUnaryEvalList_singleton
    {α : Type} [DecidableEq α] (prefixSupport : List α)
    (tested : α) :
    connectedComponentFourEvalList
        (connectedComponentFourUnaryValuation prefixSupport tested)
        [tested] =
      some 1 := by
  simp [connectedComponentFourEvalList,
    connectedComponentFourEvalFrom,
    connectedComponentFourListStep,
    connectedComponentFourUnaryValuation]

/-- List-evaluator form of the unary `x²` detector. -/
@[simp]
theorem connectedComponentFourUnaryEvalList_square
    {α : Type} [DecidableEq α] (prefixSupport : List α)
    (tested : α) :
    connectedComponentFourEvalList
        (connectedComponentFourUnaryValuation prefixSupport tested)
        [tested, tested] =
      some 0 := by
  simp [connectedComponentFourEvalList,
    connectedComponentFourEvalFrom,
    connectedComponentFourListStep,
    connectedComponentFourUnaryValuation,
    connectedComponentFourMul]

/-- The unary valuation sends the one-letter word `x` to state `1`. -/
@[simp]
theorem connectedComponentFourUnaryEval_singleton
    {α : Type} [DecidableEq α] (prefixSupport : List α)
    (tested : α) :
    connectedComponentFour.semigroup.eval
        (connectedComponentFourUnaryValuation prefixSupport tested)
        (Word.singleton tested) =
      (1 : Fin 4) := by
  simp [connectedComponentFourUnaryValuation]

/-- The same valuation sends `x²` to zero, exposing the unary
`x`-versus-`x²` distinction. -/
@[simp]
theorem connectedComponentFourUnaryEval_square
    {α : Type} [DecidableEq α] (prefixSupport : List α)
    (tested : α) :
    connectedComponentFour.semigroup.eval
        (connectedComponentFourUnaryValuation prefixSupport tested)
        (Word.singleton tested ++ Word.singleton tested) =
      (0 : Fin 4) := by
  rw [Semigroup.eval_append]
  rw [Semigroup.eval_singleton]
  rw [connectedComponentFourUnaryValuation_tested]
  change connectedComponentFourMul 1 1 = 0
  exact connectedComponentFourMul_one_one

/-- Equal `S4_70` term functions preserve every exact unary-component cut. -/
theorem connectedComponentFourEqualEval_unaryCut_iff
    {α : Type} [DecidableEq α] (source target : Word α)
    (equalEval :
      ∀ valuation : α → Fin 4,
        connectedComponentFour.semigroup.eval valuation source =
          connectedComponentFour.semigroup.eval valuation target)
    (prefixSupport : List α) (tested : α)
    (testedNotPrefix : tested ∉ prefixSupport)
    (testedOccurs : tested ∈ source.toList)
    (covered :
      ∀ letter, letter ∈ prefixSupport → letter ∈ source.toList) :
    connectedComponentFourUnaryCut
        prefixSupport tested source.toList ↔
      connectedComponentFourUnaryCut
        prefixSupport tested target.toList := by
  have targetTestedOccurs : tested ∈ target.toList :=
    (connectedComponentFourEqualEval_support_iff
      source target equalEval tested).1 testedOccurs
  have targetCovered :
      ∀ letter, letter ∈ prefixSupport → letter ∈ target.toList := by
    intro letter supportMember
    exact
      (connectedComponentFourEqualEval_support_iff
        source target equalEval letter).1
        (covered letter supportMember)
  have sourceDetected :=
    connectedComponentFourUnaryEval_eq_one_iff
      prefixSupport tested source testedNotPrefix testedOccurs covered
  have targetDetected :=
    connectedComponentFourUnaryEval_eq_one_iff
      prefixSupport tested target testedNotPrefix
      targetTestedOccurs targetCovered
  constructor
  · intro sourceCut
    have sourceOne := sourceDetected.2 sourceCut
    have targetOne :=
      (equalEval
        (connectedComponentFourUnaryValuation
          prefixSupport tested)).symm.trans sourceOne
    exact targetDetected.1 targetOne
  · intro targetCut
    have targetOne := targetDetected.2 targetCut
    have sourceOne :=
      (equalEval
        (connectedComponentFourUnaryValuation
          prefixSupport tested)).trans targetOne
    exact sourceDetected.1 sourceOne

/-- The union of the displayed supports in an ordered signature list. -/
def connectedComponentFourSignatureSupport
    (signatures : List connectedComponentSignature) : List Nat :=
  signatures.flatMap connectedComponentSignature.support

/-- Structural hypotheses satisfied by the signature list of every word. -/
def connectedComponentFourCanonicalSignatures
    (signatures : List connectedComponentSignature) : Prop :=
  (∀ signature, signature ∈ signatures →
    connectedComponentSignatureValid signature) ∧
  signatures.Pairwise
    (fun left right =>
      ConnectedComponentSupportsDisjoint left.support right.support)

theorem connectedComponentFourRenderSignatures_append
    (left right : List connectedComponentSignature) :
    connectedComponentRenderSignatures (left ++ right) =
      connectedComponentRenderSignatures left ++
        connectedComponentRenderSignatures right := by
  simp [connectedComponentRenderSignatures, List.flatMap_append]

theorem connectedComponentFourSignatureSupport_append
    (left right : List connectedComponentSignature) :
    connectedComponentFourSignatureSupport (left ++ right) =
      connectedComponentFourSignatureSupport left ++
        connectedComponentFourSignatureSupport right := by
  simp [connectedComponentFourSignatureSupport, List.flatMap_append]

theorem connectedComponentFourRenderSignatures_mem_iff
    {signatures : List connectedComponentSignature}
    (valid :
      ∀ signature, signature ∈ signatures →
        connectedComponentSignatureValid signature)
    (tested : Nat) :
    tested ∈ connectedComponentRenderSignatures signatures ↔
      tested ∈ connectedComponentFourSignatureSupport signatures := by
  simp only [connectedComponentRenderSignatures,
    connectedComponentFourSignatureSupport, List.mem_flatMap]
  constructor
  · rintro ⟨signature, signatureMember, testedMember⟩
    exact
      ⟨signature, signatureMember,
        (connectedComponentRenderSignature_mem_iff
          (valid signature signatureMember).1 tested).1 testedMember⟩
  · rintro ⟨signature, signatureMember, testedMember⟩
    exact
      ⟨signature, signatureMember,
        (connectedComponentRenderSignature_mem_iff
          (valid signature signatureMember).1 tested).2 testedMember⟩

theorem connectedComponentFourSignaturesWord_canonical
    (word : Word Nat) :
    connectedComponentFourCanonicalSignatures
      (connectedComponentSignaturesWord word) := by
  let components := connectedComponentDecomposeWord word
  have nonempty :=
    connectedComponentDecomposeWord_nonempty_components word
  have pairwise :=
    connectedComponentDecomposeWord_pairwiseDisjoint word
  constructor
  · intro signature signatureMember
    rw [connectedComponentSignaturesWord,
      connectedComponentSignaturesList] at signatureMember
    rcases List.mem_map.mp signatureMember with
      ⟨component, componentMember, rfl⟩
    exact connectedComponentSignatureOfList_valid
      (nonempty component componentMember)
  · rw [connectedComponentSignaturesWord,
      connectedComponentSignaturesList, List.pairwise_map]
    apply pairwise.imp
    intro left right disjoint
    intro letter leftMember rightMember
    apply disjoint letter
    · rw [connectedComponentSignatureOfList_support,
        connectedComponentSortedSupport_mem_iff] at leftMember
      exact leftMember
    · rw [connectedComponentSignatureOfList_support,
        connectedComponentSortedSupport_mem_iff] at rightMember
      exact rightMember

private theorem connectedComponentFourSortedNodup_eq_of_mem_iff
    {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·))
    (rightSorted : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (sameSupport : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          have := (sameSupport head).2 (by simp)
          contradiction
  | cons leftHead leftTail ih =>
      cases right with
      | nil =>
          have := (sameSupport leftHead).1 (by simp)
          contradiction
      | cons rightHead rightTail =>
          have leftHeadInRight :=
            (sameSupport leftHead).1 (by simp)
          have rightHeadInLeft :=
            (sameSupport rightHead).2 (by simp)
          have rightHeadLeLeftHead : rightHead ≤ leftHead := by
            by_cases equal : leftHead = rightHead
            · omega
            · have tailMember : leftHead ∈ rightTail := by
                simpa [equal] using leftHeadInRight
              exact List.rel_of_pairwise_cons rightSorted tailMember
          have leftHeadLeRightHead : leftHead ≤ rightHead := by
            by_cases equal : rightHead = leftHead
            · omega
            · have tailMember : rightHead ∈ leftTail := by
                simpa [equal] using rightHeadInLeft
              exact List.rel_of_pairwise_cons leftSorted tailMember
          have headsEqual : leftHead = rightHead := by omega
          subst rightHead
          congr 1
          apply ih leftSorted.tail rightSorted.tail
            leftNodup.tail rightNodup.tail
          intro letter
          by_cases equal : letter = leftHead
          · subst letter
            have leftAbsent : leftHead ∉ leftTail := by
              simpa using (List.nodup_cons.mp leftNodup).1
            have rightAbsent : leftHead ∉ rightTail := by
              simpa using (List.nodup_cons.mp rightNodup).1
            simp [leftAbsent, rightAbsent]
          · simpa [equal] using sameSupport letter

end SemigroupBasis.Examples

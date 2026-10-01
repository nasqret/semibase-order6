import SemigroupBasis.CoRoots.S5_254

namespace SemigroupBasis.CoRoots.S5_254

open SemigroupBasis

/-! ## List evaluation for the monoid-shaped table -/

inductive M18ListState where
  | identity
  | value (element : Fin 5)
deriving DecidableEq, Repr

def m18ListStep : M18ListState → Fin 5 → M18ListState
  | .identity, next => .value next
  | .value current, next =>
      .value (Generated.Catalogue.S5_254.mul current next)

def m18EvalFrom
    {α : Type} (initial : M18ListState)
    (valuation : α → Fin 5) (letters : List α) : M18ListState :=
  letters.foldl
    (fun current letter => m18ListStep current (valuation letter))
    initial

def m18EvalList
    {α : Type} (valuation : α → Fin 5)
    (letters : List α) : M18ListState :=
  m18EvalFrom .identity valuation letters

@[simp]
theorem m18EvalFrom_nil
    {α : Type} (initial : M18ListState)
    (valuation : α → Fin 5) :
    m18EvalFrom initial valuation [] = initial :=
  rfl

@[simp]
theorem m18EvalFrom_cons
    {α : Type} (initial : M18ListState)
    (valuation : α → Fin 5) (letter : α) (letters : List α) :
    m18EvalFrom initial valuation (letter :: letters) =
      m18EvalFrom (m18ListStep initial (valuation letter))
        valuation letters :=
  rfl

theorem m18EvalFrom_append
    {α : Type} (initial : M18ListState)
    (valuation : α → Fin 5) (left right : List α) :
    m18EvalFrom initial valuation (left ++ right) =
      m18EvalFrom (m18EvalFrom initial valuation left)
        valuation right := by
  simp [m18EvalFrom, List.foldl_append]

theorem m18EvalFrom_value
    {α : Type} (initial : Fin 5) (valuation : α → Fin 5)
    (letters : List α) :
    m18EvalFrom (.value initial) valuation letters =
      .value
        (letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_254.mul current (valuation letter))
          initial) := by
  induction letters generalizing initial with
  | nil => rfl
  | cons letter letters induction =>
      simp only [m18EvalFrom_cons, m18ListStep]
      exact induction
        (Generated.Catalogue.S5_254.mul initial (valuation letter))

theorem m18EvalFrom_congr
    {α : Type} (initial : M18ListState)
    (first second : α → Fin 5) :
    ∀ letters : List α,
      (∀ letter, letter ∈ letters → first letter = second letter) →
      m18EvalFrom initial first letters =
        m18EvalFrom initial second letters
  | [], _ => rfl
  | letter :: letters, agree => by
      rw [m18EvalFrom_cons, m18EvalFrom_cons,
        agree letter (by simp)]
      exact m18EvalFrom_congr _ first second letters (by
        intro tested member
        exact agree tested (List.Mem.tail letter member))

theorem m18EvalList_toList
    {α : Type} (valuation : α → Fin 5) (word : Word α) :
    m18EvalList valuation word.toList =
      .value (table.semigroup.eval valuation word) := by
  cases word with
  | mk head tail =>
      simp only [m18EvalList, m18EvalFrom_cons, m18ListStep,
        Word.toList, Semigroup.eval]
      exact m18EvalFrom_value (valuation head) valuation tail

private theorem m18EvalList_eq_from_three_of_ne_nil
    {α : Type} (valuation : α → Fin 5)
    (leftIdentity : ∀ letter,
      Generated.Catalogue.S5_254.mul 3 (valuation letter) =
        valuation letter) {letters : List α} (nonempty : letters ≠ []) :
    m18EvalList valuation letters =
      m18EvalFrom (.value 3) valuation letters := by
  obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  simp [m18EvalList, m18ListStep, leftIdentity]

/-! ## Concrete multiplication facts -/

@[simp] theorem m18Mul_zero_left (next : Fin 5) :
    Generated.Catalogue.S5_254.mul 0 next = 0 := by decide +revert

@[simp] theorem m18Mul_zero_right (current : Fin 5) :
    Generated.Catalogue.S5_254.mul current 0 = 0 := by decide +revert

@[simp] theorem m18Mul_three_one :
    Generated.Catalogue.S5_254.mul 3 1 = 1 := by decide
@[simp] theorem m18Mul_three_two :
    Generated.Catalogue.S5_254.mul 3 2 = 2 := by decide
@[simp] theorem m18Mul_three_three :
    Generated.Catalogue.S5_254.mul 3 3 = 3 := by decide
@[simp] theorem m18Mul_three_four :
    Generated.Catalogue.S5_254.mul 3 4 = 4 := by decide
@[simp] theorem m18Mul_four_one :
    Generated.Catalogue.S5_254.mul 4 1 = 2 := by decide
@[simp] theorem m18Mul_four_two :
    Generated.Catalogue.S5_254.mul 4 2 = 1 := by decide
@[simp] theorem m18Mul_four_three :
    Generated.Catalogue.S5_254.mul 4 3 = 4 := by decide
@[simp] theorem m18Mul_four_four :
    Generated.Catalogue.S5_254.mul 4 4 = 3 := by decide
@[simp] theorem m18Mul_one_one :
    Generated.Catalogue.S5_254.mul 1 1 = 0 := by decide
@[simp] theorem m18Mul_one_two :
    Generated.Catalogue.S5_254.mul 1 2 = 0 := by decide
@[simp] theorem m18Mul_one_three :
    Generated.Catalogue.S5_254.mul 1 3 = 1 := by decide
@[simp] theorem m18Mul_one_four :
    Generated.Catalogue.S5_254.mul 1 4 = 1 := by decide
@[simp] theorem m18Mul_two_one :
    Generated.Catalogue.S5_254.mul 2 1 = 0 := by decide
@[simp] theorem m18Mul_two_two :
    Generated.Catalogue.S5_254.mul 2 2 = 0 := by decide
@[simp] theorem m18Mul_two_three :
    Generated.Catalogue.S5_254.mul 2 3 = 2 := by decide
@[simp] theorem m18Mul_two_four :
    Generated.Catalogue.S5_254.mul 2 4 = 2 := by decide

/-! ## Support detection -/

def m18SupportValuation
    {α : Type} [DecidableEq α] (tested : α) : α → Fin 5 :=
  fun letter => if letter = tested then 0 else 3

private theorem m18EvalFrom_zero
    {α : Type} (valuation : α → Fin 5) (letters : List α) :
    m18EvalFrom (.value 0) valuation letters = .value 0 := by
  induction letters with
  | nil => rfl
  | cons letter letters induction =>
      simp only [m18EvalFrom_cons, m18ListStep, m18Mul_zero_left]
      exact induction

private theorem m18SupportFoldThree
    {α : Type} [DecidableEq α] (tested : α) (letters : List α) :
    m18EvalFrom (.value 3)
        (m18SupportValuation tested) letters =
      if tested ∈ letters then .value 0 else .value 3 := by
  induction letters with
  | nil => simp
  | cons letter letters induction =>
      by_cases hit : letter = tested
      · subst letter
        rw [m18EvalFrom_cons]
        simp only [m18SupportValuation, if_pos, m18ListStep,
          m18Mul_zero_right]
        rw [m18EvalFrom_zero]
        simp
      · have reverseDifferent : tested ≠ letter := Ne.symm hit
        rw [m18EvalFrom_cons]
        simp only [m18SupportValuation, if_neg hit, m18ListStep,
          m18Mul_three_three]
        rw [induction]
        simp [reverseDifferent]

theorem m18SupportEval_eq_zero_iff
    {α : Type} [DecidableEq α] (tested : α) (word : Word α) :
    table.semigroup.eval (m18SupportValuation tested) word = (0 : Fin 5) ↔
      tested ∈ word.toList := by
  have leftIdentity : ∀ letter,
      Generated.Catalogue.S5_254.mul 3
          (m18SupportValuation tested letter) =
        m18SupportValuation tested letter := by
    intro letter
    by_cases hit : letter = tested <;>
      simp [m18SupportValuation, hit]
  have nonempty : word.toList ≠ [] := by cases word <;> simp [Word.toList]
  have stateEq :=
    (m18EvalList_eq_from_three_of_ne_nil
      (m18SupportValuation tested) leftIdentity nonempty).trans
        (m18SupportFoldThree tested word.toList)
  rw [m18EvalList_toList] at stateEq
  by_cases member : tested ∈ word.toList
  · simp [member] at stateEq
    exact ⟨fun _ => member, fun _ => stateEq⟩
  · simp [member] at stateEq
    constructor
    · intro zero
      rw [zero] at stateEq
      simp at stateEq
    · exact False.elim ∘ member

/-! ## Total parity detection -/

def m18ParityValuation
    {α : Type} [DecidableEq α] (tested : α) : α → Fin 5 :=
  fun letter => if letter = tested then 4 else 3

private theorem m18ParityFold
    {α : Type} [DecidableEq α] (tested : α) :
    ∀ letters : List α,
      (m18EvalFrom (.value 3) (m18ParityValuation tested) letters =
        .value (if letters.count tested % 2 = 0 then 3 else 4)) ∧
      (m18EvalFrom (.value 4) (m18ParityValuation tested) letters =
        .value (if letters.count tested % 2 = 0 then 4 else 3))
  | [] => by simp
  | letter :: letters => by
      obtain ⟨fromThree, fromFour⟩ := m18ParityFold tested letters
      by_cases hit : letter = tested
      · subst letter
        by_cases even : letters.count tested % 2 = 0
        · have toggled : (letters.count tested + 1) % 2 = 1 := by omega
          simp [m18ListStep, m18ParityValuation, fromThree, fromFour,
            even, toggled]
        · have odd : letters.count tested % 2 = 1 := by omega
          have toggled : (letters.count tested + 1) % 2 = 0 := by omega
          simp [m18ListStep, m18ParityValuation, fromThree, fromFour,
            odd, toggled]
      · simp [m18ListStep, m18ParityValuation, hit, fromThree, fromFour]

private theorem m18ParityEvalList_of_ne_nil
    {α : Type} [DecidableEq α] (tested : α)
    {letters : List α} (nonempty : letters ≠ []) :
    m18EvalList (m18ParityValuation tested) letters =
      .value (if letters.count tested % 2 = 0 then 3 else 4) := by
  have leftIdentity : ∀ letter,
      Generated.Catalogue.S5_254.mul 3
          (m18ParityValuation tested letter) =
        m18ParityValuation tested letter := by
    intro letter
    by_cases hit : letter = tested <;>
      simp [m18ParityValuation, hit]
  exact
    (m18EvalList_eq_from_three_of_ne_nil
      (m18ParityValuation tested) leftIdentity nonempty).trans
        (m18ParityFold tested letters).1

theorem m18ParityEval
    {α : Type} [DecidableEq α] (tested : α) (word : Word α) :
    table.semigroup.eval (m18ParityValuation tested) word =
      if word.toList.count tested % 2 = 0 then
        (3 : Fin 5)
      else 4 := by
  have nonempty : word.toList ≠ [] := by cases word <;> simp [Word.toList]
  have stateEq := m18ParityEvalList_of_ne_nil tested nonempty
  rw [m18EvalList_toList] at stateEq
  injection stateEq

/-! ## Global simplicity detection -/

def m18SimpleValuation
    {α : Type} [DecidableEq α] (tested : α) : α → Fin 5 :=
  fun letter => if letter = tested then 1 else 3

def m18SimpleClassify (count : Nat) : Fin 5 :=
  if count = 0 then 3 else if count = 1 then 1 else 0

private theorem m18SimpleClassify_succ (count : Nat) :
    m18SimpleClassify (count + 1) =
      if count = 0 then 1 else 0 := by
  by_cases zero : count = 0
  · subst count
    simp [m18SimpleClassify]
  · simp [m18SimpleClassify, zero]

private theorem m18SimpleFold
    {α : Type} [DecidableEq α] (tested : α) :
    ∀ letters : List α,
      (m18EvalFrom (.value 3) (m18SimpleValuation tested) letters =
        .value (m18SimpleClassify (letters.count tested))) ∧
      (m18EvalFrom (.value 1) (m18SimpleValuation tested) letters =
        .value (if letters.count tested = 0 then 1 else 0)) ∧
      (m18EvalFrom (.value 0) (m18SimpleValuation tested) letters =
        .value 0)
  | [] => by simp [m18SimpleClassify]
  | letter :: letters => by
      obtain ⟨fromThree, fromOne, fromZero⟩ :=
        m18SimpleFold tested letters
      by_cases hit : letter = tested
      · subst letter
        simp [m18ListStep, m18SimpleValuation, fromThree, fromOne, fromZero,
          m18SimpleClassify_succ]
      · simp [m18ListStep, m18SimpleValuation, hit, fromThree, fromOne,
          fromZero]

theorem m18SimpleEval
    {α : Type} [DecidableEq α] (tested : α) (word : Word α) :
    table.semigroup.eval (m18SimpleValuation tested) word =
      m18SimpleClassify (word.toList.count tested) := by
  have leftIdentity : ∀ letter,
      Generated.Catalogue.S5_254.mul 3
          (m18SimpleValuation tested letter) =
        m18SimpleValuation tested letter := by
    intro letter
    by_cases hit : letter = tested <;>
      simp [m18SimpleValuation, hit]
  have nonempty : word.toList ≠ [] := by cases word <;> simp [Word.toList]
  have stateEq :=
    (m18EvalList_eq_from_three_of_ne_nil
      (m18SimpleValuation tested) leftIdentity nonempty).trans
        (m18SimpleFold tested word.toList).1
  rw [m18EvalList_toList] at stateEq
  injection stateEq

theorem m18SimpleEval_eq_one_iff
    {α : Type} [DecidableEq α] (tested : α) (word : Word α) :
    table.semigroup.eval (m18SimpleValuation tested) word = (1 : Fin 5) ↔
      word.toList.count tested = 1 := by
  rw [m18SimpleEval]
  by_cases zero : word.toList.count tested = 0
  · simp [m18SimpleClassify, zero]
  · by_cases one : word.toList.count tested = 1
    · simp [m18SimpleClassify, one]
    · simp [m18SimpleClassify, zero, one]

/-! ## Prefix parity before a globally simple separator -/

def m18PrefixParityValuation
    {α : Type} [DecidableEq α]
    (separator tested : α) : α → Fin 5 :=
  fun letter =>
    if letter = separator then 1
    else if letter = tested then 4
    else 3

private theorem m18RadicalParityFold
    {α : Type} [DecidableEq α] (tested : α) :
    ∀ letters : List α,
      (m18EvalFrom (.value 1) (m18ParityValuation tested) letters =
        .value 1) ∧
      (m18EvalFrom (.value 2) (m18ParityValuation tested) letters =
        .value 2)
  | [] => by simp
  | letter :: letters => by
      obtain ⟨fromOne, fromTwo⟩ :=
        m18RadicalParityFold tested letters
      by_cases hit : letter = tested <;>
        simp [m18ListStep, m18ParityValuation, hit, fromOne, fromTwo]

private theorem separator_absent_left
    {α : Type} [DecidableEq α]
    {letters prefixWords suffix : List α} {separator : α}
    (shape : letters = prefixWords ++ separator :: suffix)
    (simple : letters.count separator = 1) :
    separator ∉ prefixWords := by
  intro member
  have positive : 0 < prefixWords.count separator :=
    List.count_pos_iff.mpr member
  rw [shape, List.count_append, List.count_cons_self] at simple
  omega

private theorem separator_absent_right
    {α : Type} [DecidableEq α]
    {letters prefixWords suffix : List α} {separator : α}
    (shape : letters = prefixWords ++ separator :: suffix)
    (simple : letters.count separator = 1) :
    separator ∉ suffix := by
  intro member
  have positive : 0 < suffix.count separator :=
    List.count_pos_iff.mpr member
  rw [shape, List.count_append, List.count_cons_self] at simple
  omega

private theorem m18PrefixParityEval_of_split
    {α : Type} [DecidableEq α]
    (word : Word α) (separator tested : α)
    (prefixWords suffix : List α)
    (shape : word.toList = prefixWords ++ separator :: suffix)
    (simple : word.toList.count separator = 1)
    (different : tested ≠ separator) :
    table.semigroup.eval
        (m18PrefixParityValuation separator tested) word =
      if prefixWords.count tested % 2 = 0 then
        (1 : Fin 5)
      else 2 := by
  have separatorNotPrefix := separator_absent_left shape simple
  have separatorNotSuffix := separator_absent_right shape simple
  have prefixAgree : ∀ letter, letter ∈ prefixWords →
      m18PrefixParityValuation separator tested letter =
        m18ParityValuation tested letter := by
    intro letter member
    have notSeparator : letter ≠ separator := by
      intro equal
      subst letter
      exact separatorNotPrefix member
    simp [m18PrefixParityValuation, m18ParityValuation,
      notSeparator, different]
  have suffixAgree : ∀ letter, letter ∈ suffix →
      m18PrefixParityValuation separator tested letter =
        m18ParityValuation tested letter := by
    intro letter member
    have notSeparator : letter ≠ separator := by
      intro equal
      subst letter
      exact separatorNotSuffix member
    simp [m18PrefixParityValuation, m18ParityValuation,
      notSeparator, different]
  have prefixState :
      m18EvalList (m18PrefixParityValuation separator tested) prefixWords =
        m18EvalList (m18ParityValuation tested) prefixWords := by
    exact m18EvalFrom_congr .identity _ _ prefixWords prefixAgree
  have throughSeparator :
      m18EvalFrom
          (m18EvalList (m18PrefixParityValuation separator tested) prefixWords)
          (m18PrefixParityValuation separator tested) [separator] =
        .value (if prefixWords.count tested % 2 = 0 then 1 else 2) := by
    rw [prefixState]
    cases prefixWords with
    | nil =>
        simp [m18EvalList, m18ListStep, m18PrefixParityValuation]
    | cons head tail =>
        have prefixNonempty : head :: tail ≠ [] := by simp
        rw [m18ParityEvalList_of_ne_nil tested prefixNonempty]
        by_cases even : (head :: tail).count tested % 2 = 0
        · simp [m18ListStep, m18PrefixParityValuation, even]
        · have odd : (head :: tail).count tested % 2 = 1 := by omega
          simp [m18ListStep, m18PrefixParityValuation, even, odd]
  have suffixFromOne :
      m18EvalFrom (.value 1)
          (m18PrefixParityValuation separator tested) suffix =
        .value 1 := by
    rw [m18EvalFrom_congr (.value 1) _ _ suffix suffixAgree]
    exact (m18RadicalParityFold tested suffix).1
  have suffixFromTwo :
      m18EvalFrom (.value 2)
          (m18PrefixParityValuation separator tested) suffix =
        .value 2 := by
    rw [m18EvalFrom_congr (.value 2) _ _ suffix suffixAgree]
    exact (m18RadicalParityFold tested suffix).2
  have listState :
      m18EvalList
          (m18PrefixParityValuation separator tested) word.toList =
        .value (if prefixWords.count tested % 2 = 0 then 1 else 2) := by
    rw [shape]
    change
      m18EvalFrom .identity
          (m18PrefixParityValuation separator tested)
          (prefixWords ++ ([separator] ++ suffix)) = _
    rw [m18EvalFrom_append, m18EvalFrom_append]
    change
      m18EvalFrom
          (m18EvalFrom
            (m18EvalList
              (m18PrefixParityValuation separator tested) prefixWords)
            (m18PrefixParityValuation separator tested) [separator])
          (m18PrefixParityValuation separator tested) suffix = _
    rw [throughSeparator]
    by_cases even : prefixWords.count tested % 2 = 0
    · simp [even, suffixFromOne]
    · simp [even, suffixFromTwo]
  rw [m18EvalList_toList] at listState
  injection listState

private theorem prefixParityBefore_self_iff
    {word : Word Nat} {separator parity : Nat}
    (simple : GloballySimple word separator) :
    PrefixParityBefore word separator separator parity ↔ parity = 0 := by
  constructor
  · rintro ⟨prefixWords, suffix, shape, prefixParity⟩
    have absent := separator_absent_left shape simple
    have zero : prefixWords.count separator = 0 :=
      List.count_eq_zero.mpr absent
    simpa [zero] using prefixParity.symm
  · intro parityZero
    have member : separator ∈ word.toList :=
      List.count_pos_iff.mp (by rw [simple]; decide)
    obtain ⟨prefixWords, suffix, shape⟩ := List.mem_iff_append.mp member
    have absent := separator_absent_left shape simple
    refine ⟨prefixWords, suffix, shape, ?_⟩
    rw [List.count_eq_zero.mpr absent, parityZero]

/-! ## Signature necessity -/

theorem sameM18Signature_of_equalEval
    (left right : Word Nat)
    (equalEval : ∀ valuation : Nat → Fin 5,
      table.semigroup.eval valuation left =
        table.semigroup.eval valuation right) :
    SameM18Signature left right := by
  have support : SameSupport left right := by
    intro tested
    have evaluated := equalEval (m18SupportValuation tested)
    rw [← m18SupportEval_eq_zero_iff tested left,
      ← m18SupportEval_eq_zero_iff tested right]
    exact ⟨fun zero => evaluated ▸ zero,
      fun zero => evaluated.symm ▸ zero⟩
  have totalParity : SameTotalParity left right := by
    intro tested
    have evaluated := equalEval (m18ParityValuation tested)
    rw [m18ParityEval, m18ParityEval] at evaluated
    have leftBound := Nat.mod_lt (left.toList.count tested) (by decide : 0 < 2)
    have rightBound := Nat.mod_lt (right.toList.count tested) (by decide : 0 < 2)
    by_cases leftEven : left.toList.count tested % 2 = 0
    · have rightEven : right.toList.count tested % 2 = 0 := by
        apply Decidable.byContradiction
        intro notEven
        have rightOdd : right.toList.count tested % 2 = 1 := by omega
        simp [leftEven, rightOdd] at evaluated
      omega
    · have leftOdd : left.toList.count tested % 2 = 1 := by omega
      have rightOdd : right.toList.count tested % 2 = 1 := by
        apply Decidable.byContradiction
        intro notOdd
        have rightEven : right.toList.count tested % 2 = 0 := by omega
        simp [leftOdd, rightEven] at evaluated
      omega
  have globallySimple : SameGloballySimpleVariables left right := by
    intro tested
    change
      left.toList.count tested = 1 ↔
        right.toList.count tested = 1
    have evaluated := equalEval (m18SimpleValuation tested)
    rw [← m18SimpleEval_eq_one_iff tested left,
      ← m18SimpleEval_eq_one_iff tested right]
    exact ⟨fun one => evaluated ▸ one,
      fun one => evaluated.symm ▸ one⟩
  have prefixParity :
      SamePrefixParityBeforeSimpleSeparators left right := by
    intro separator leftSimple rightSimple tested parity
    by_cases sameLetter : tested = separator
    · subst tested
      rw [prefixParityBefore_self_iff leftSimple,
        prefixParityBefore_self_iff rightSimple]
    · constructor
      · rintro ⟨leftPrefix, leftSuffix, leftShape, leftParity⟩
        have rightMember : separator ∈ right.toList :=
          List.count_pos_iff.mp (by rw [rightSimple]; decide)
        obtain ⟨rightPrefix, rightSuffix, rightShape⟩ :=
          List.mem_iff_append.mp rightMember
        have evaluated :=
          equalEval (m18PrefixParityValuation separator tested)
        rw [m18PrefixParityEval_of_split left separator tested
              leftPrefix leftSuffix leftShape leftSimple sameLetter,
            m18PrefixParityEval_of_split right separator tested
              rightPrefix rightSuffix rightShape rightSimple sameLetter]
          at evaluated
        have leftBound :=
          Nat.mod_lt (leftPrefix.count tested) (by decide : 0 < 2)
        have rightBound :=
          Nat.mod_lt (rightPrefix.count tested) (by decide : 0 < 2)
        have parityEq :
            rightPrefix.count tested % 2 =
              leftPrefix.count tested % 2 := by
          by_cases leftEven : leftPrefix.count tested % 2 = 0
          · have rightEven : rightPrefix.count tested % 2 = 0 := by
              apply Decidable.byContradiction
              intro notEven
              have rightOdd : rightPrefix.count tested % 2 = 1 := by omega
              simp [leftEven, rightOdd] at evaluated
            omega
          · have leftOdd : leftPrefix.count tested % 2 = 1 := by omega
            have rightOdd : rightPrefix.count tested % 2 = 1 := by
              apply Decidable.byContradiction
              intro notOdd
              have rightEven : rightPrefix.count tested % 2 = 0 := by omega
              simp [leftOdd, rightEven] at evaluated
            omega
        exact ⟨rightPrefix, rightSuffix, rightShape,
          parityEq.trans leftParity⟩
      · rintro ⟨rightPrefix, rightSuffix, rightShape, rightParity⟩
        have leftMember : separator ∈ left.toList :=
          List.count_pos_iff.mp (by rw [leftSimple]; decide)
        obtain ⟨leftPrefix, leftSuffix, leftShape⟩ :=
          List.mem_iff_append.mp leftMember
        have evaluated :=
          equalEval (m18PrefixParityValuation separator tested)
        rw [m18PrefixParityEval_of_split left separator tested
              leftPrefix leftSuffix leftShape leftSimple sameLetter,
            m18PrefixParityEval_of_split right separator tested
              rightPrefix rightSuffix rightShape rightSimple sameLetter]
          at evaluated
        have leftBound :=
          Nat.mod_lt (leftPrefix.count tested) (by decide : 0 < 2)
        have rightBound :=
          Nat.mod_lt (rightPrefix.count tested) (by decide : 0 < 2)
        have parityEq :
            leftPrefix.count tested % 2 =
              rightPrefix.count tested % 2 := by
          by_cases leftEven : leftPrefix.count tested % 2 = 0
          · have rightEven : rightPrefix.count tested % 2 = 0 := by
              apply Decidable.byContradiction
              intro notEven
              have rightOdd : rightPrefix.count tested % 2 = 1 := by omega
              simp [leftEven, rightOdd] at evaluated
            omega
          · have leftOdd : leftPrefix.count tested % 2 = 1 := by omega
            have rightOdd : rightPrefix.count tested % 2 = 1 := by
              apply Decidable.byContradiction
              intro notOdd
              have rightEven : rightPrefix.count tested % 2 = 0 := by omega
              simp [leftOdd, rightEven] at evaluated
            omega
        exact ⟨leftPrefix, leftSuffix, leftShape,
          parityEq.trans rightParity⟩
  exact ⟨support, totalParity, globallySimple, prefixParity⟩

/-- Every concrete-table-valid identity has the full M18 signature. -/
theorem sameM18Signature_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameM18Signature identity.lhs identity.rhs :=
  sameM18Signature_of_equalEval identity.lhs identity.rhs valid

end SemigroupBasis.CoRoots.S5_254

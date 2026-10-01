import SemigroupBasis.Nonfinite.LeeL.SourceWords
import SemigroupBasis.TransferPower

namespace SemigroupBasis.Examples.LeeL

open SemigroupBasis

namespace OrderedSplit

/-- The four-element quotient `A₀`, ordered as `0, ed, d, e`. -/
def a0Mul (left right : Fin 4) : Fin 4 :=
  if left = 0 then 0
  else if left = 1 then
    if right = 2 then 1 else 0
  else if left = 2 then
    if right = 2 then 2 else 0
  else
    if right = 1 then 1
    else if right = 2 then 1
    else if right = 3 then 3
    else 0

def a0 : Semigroup (Fin 4) where
  mul := a0Mul
  assoc := by decide

/-- Quotient map that identifies `0`, `a`, and `b`. -/
def quotientMap (value : Fin 6) : Fin 4 :=
  if value = 0 then 0
  else if value = 1 then 0
  else if value = 2 then 0
  else if value = 3 then 1
  else if value = 4 then 2
  else 3

def quotientSection (value : Fin 4) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 3
  else if value = 2 then 4
  else 5

def quotient : SplitSurjection table.semigroup a0 where
  toFun := quotientMap
  map_mul := by decide
  preimage := quotientSection
  right_inverse := by decide

theorem a0_in_variety {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy a0 :=
  quotient.pushforwardIdentity identity valid

/-- The concrete idempotent-separability condition used to cancel the two
pieces after the `A₀` quotient has located the cut. -/
def IdempotentSeparable : Prop :=
  ∀ x y : Fin 6, x ≠ y →
    (∃ leftIdempotent : Fin 6,
      mul leftIdempotent leftIdempotent = leftIdempotent ∧
      mul leftIdempotent x ≠ mul leftIdempotent y) ∧
    (∃ rightIdempotent : Fin 6,
      mul rightIdempotent rightIdempotent = rightIdempotent ∧
      mul x rightIdempotent ≠ mul y rightIdempotent)

private def leftSeparator (x y : Fin 6) : Fin 6 :=
  if mul 4 x ≠ mul 4 y then 4 else 5

private def rightSeparator (x y : Fin 6) : Fin 6 :=
  if mul x 4 ≠ mul y 4 then 4 else 5

private theorem leftSeparator_spec (x y : Fin 6) (different : x ≠ y) :
    mul (leftSeparator x y) (leftSeparator x y) = leftSeparator x y ∧
      mul (leftSeparator x y) x ≠ mul (leftSeparator x y) y := by
  revert x y
  decide

private theorem rightSeparator_spec (x y : Fin 6) (different : x ≠ y) :
    mul (rightSeparator x y) (rightSeparator x y) = rightSeparator x y ∧
      mul x (rightSeparator x y) ≠ mul y (rightSeparator x y) := by
  revert x y
  decide

theorem table_idempotentSeparable : IdempotentSeparable := by
  intro x y different
  exact
    ⟨⟨leftSeparator x y, leftSeparator_spec x y different⟩,
      ⟨rightSeparator x y, rightSeparator_spec x y different⟩⟩

private def colorValue (leftColor : Bool) : Fin 4 :=
  if leftColor then 3 else 2

private def colorRun (initial : Fin 4) : List Bool → Fin 4
  | [] => initial
  | color :: rest => colorRun (a0Mul initial (colorValue color)) rest

private def colorEval : List Bool → Fin 4
  | [] => 0
  | color :: rest => colorRun (colorValue color) rest

@[simp] private theorem colorRun_zero_ne_one (colors : List Bool) :
    colorRun 0 colors ≠ 1 := by
  induction colors with
  | nil => decide
  | cons color rest ih =>
      cases color <;> simpa [colorRun, colorValue, a0Mul] using ih

private theorem colorRun_one_eq_one_iff (colors : List Bool) :
    colorRun 1 colors = 1 ↔ ∀ color ∈ colors, color = false := by
  induction colors with
  | nil => simp [colorRun]
  | cons color rest ih =>
      cases color <;>
        simp [colorRun, colorValue, a0Mul, ih, colorRun_zero_ne_one]

private theorem colorRun_two_ne_one (colors : List Bool) :
    colorRun 2 colors ≠ 1 := by
  induction colors with
  | nil => decide
  | cons color rest ih =>
      cases color <;>
        simp [colorRun, colorValue, a0Mul, ih, colorRun_zero_ne_one]

private theorem eq_replicate_false_of_all_false
    (colors : List Bool)
    (allFalse : ∀ color ∈ colors, color = false) :
    colors = List.replicate colors.length false := by
  induction colors with
  | nil => rfl
  | cons color rest ih =>
      have colorFalse := allFalse color (List.Mem.head rest)
      subst color
      have restFalse : ∀ value ∈ rest, value = false := by
        intro value member
        exact allFalse value (List.Mem.tail false member)
      change false :: rest =
        List.replicate (Nat.succ rest.length) false
      rw [List.replicate_succ]
      exact congrArg (List.cons false) (ih restFalse)

private theorem colorRun_three_shape (colors : List Bool) :
    colorRun 3 colors = 1 ↔
      ∃ leftCount rightCount,
        colors =
          List.replicate leftCount true ++
            List.replicate (rightCount + 1) false := by
  induction colors with
  | nil =>
      simp [colorRun]
  | cons color rest ih =>
      cases color
      · simp only [colorRun]
        change colorRun 1 rest = 1 ↔ _
        constructor
        · intro allFalse
          refine ⟨0, rest.length, ?_⟩
          simp only [List.replicate_zero, List.nil_append]
          have restShape :=
            eq_replicate_false_of_all_false rest
              ((colorRun_one_eq_one_iff rest).mp allFalse)
          rw [restShape]
          simp [List.replicate_succ]
        · rintro ⟨leftCount, rightCount, shape⟩
          have leftCountZero : leftCount = 0 := by
            cases leftCount with
            | zero => rfl
            | succ leftCount =>
                change false :: rest =
                  true ::
                    (List.replicate leftCount true ++
                      List.replicate (rightCount + 1) false) at shape
                exact Bool.noConfusion (List.cons.inj shape).1
          subst leftCount
          simp only [List.replicate_zero, List.nil_append] at shape
          apply (colorRun_one_eq_one_iff rest).mpr
          have restShape : rest = List.replicate rightCount false := by
            have tails := congrArg List.tail shape
            simpa [List.replicate_succ, Nat.add_comm] using tails
          intro value member
          rw [restShape] at member
          simp at member
          exact member.2
      · simp only [colorRun]
        change colorRun 3 rest = 1 ↔ _
        rw [ih]
        constructor
        · rintro ⟨leftCount, rightCount, shape⟩
          exact ⟨leftCount + 1, rightCount, by
            simp [shape, List.replicate_succ]⟩
        · rintro ⟨leftCount, rightCount, shape⟩
          cases leftCount with
          | zero =>
              change true :: rest =
                false :: List.replicate rightCount false at shape
              exact Bool.noConfusion (List.cons.inj shape).1
          | succ leftCount =>
              have tails := congrArg List.tail shape
              refine ⟨leftCount, rightCount, ?_⟩
              simpa [List.replicate_succ] using tails

private theorem colorEval_shape {colors : List Bool}
    (evaluates : colorEval colors = 1) :
    ∃ leftCount rightCount,
      1 ≤ leftCount ∧
      1 ≤ rightCount ∧
      colors =
        List.replicate leftCount true ++
          List.replicate rightCount false := by
  cases colors with
  | nil => simp [colorEval] at evaluates
  | cons color rest =>
      cases color
      · simp [colorEval, colorValue, colorRun_two_ne_one] at evaluates
      · have shape := (colorRun_three_shape rest).mp (by
          simpa [colorEval, colorValue] using evaluates)
        rcases shape with ⟨leftCount, rightCount, shape⟩
        exact ⟨leftCount + 1, rightCount + 1, by omega, by omega, by
          simp [shape, List.replicate_succ]⟩

private theorem eval_colorValue (color : Nat → Bool) (word : Word Nat) :
    a0.eval (fun letter => colorValue (color letter)) word =
      colorEval (word.toList.map color) := by
  have runMap :
      ∀ (initial : Fin 4) (letters : List Nat),
        colorRun initial (letters.map color) =
          letters.foldl
            (fun current letter =>
              a0Mul current (colorValue (color letter)))
            initial := by
    intro initial letters
    induction letters generalizing initial with
    | nil => rfl
    | cons letter rest ih =>
        simp only [List.map_cons, colorRun, List.foldl_cons]
        exact ih _
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval, Word.toList, List.map_cons, colorEval]
      exact (runMap (colorValue (color head)) tail).symm

private theorem eval_constant_idempotent
    (idempotent : Fin 6)
    (idempotent_mul : mul idempotent idempotent = idempotent)
    (word : Word Nat) :
    table.semigroup.eval (fun _ => idempotent) word = idempotent := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      induction tail with
      | nil => rfl
      | cons next rest ih =>
          simp only [List.foldl_cons]
          rw [show table.semigroup.mul idempotent idempotent = idempotent by
            exact idempotent_mul]
          exact ih

private theorem eval_eq_of_agree_on_word
    {first second : Nat → Fin 6} {word : Word Nat}
    (agree : ∀ letter, letter ∈ word.toList → first letter = second letter) :
    table.semigroup.eval first word = table.semigroup.eval second word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval, Word.toList] at *
      have headAgree : first head = second head :=
        agree head (List.Mem.head tail)
      have tailAgree :
          ∀ letter ∈ tail, first letter = second letter := by
        intro letter member
        exact agree letter (List.Mem.tail head member)
      have foldAgree :
          ∀ (letters : List Nat) (leftInitial rightInitial : Fin 6),
            leftInitial = rightInitial →
            (∀ letter ∈ letters, first letter = second letter) →
            letters.foldl
                (fun current letter =>
                  table.semigroup.mul current (first letter))
                leftInitial =
              letters.foldl
                (fun current letter =>
                  table.semigroup.mul current (second letter))
                rightInitial := by
        intro letters
        induction letters with
        | nil =>
            intro leftInitial rightInitial initialEq _
            exact initialEq
        | cons letter rest ih =>
            intro leftInitial rightInitial initialEq valuesAgree
            simp only [List.foldl_cons]
            apply ih
            · rw [initialEq, valuesAgree letter (List.Mem.head rest)]
            · intro value member
              exact valuesAgree value (List.Mem.tail letter member)
      exact foldAgree tail (first head) (second head) headAgree tailAgree

/-- The ordered-splitting property required by Zhang--Luo Lemma 3. -/
def Property : Prop :=
  ∀ (identity : Identity Nat) (left right : Word Nat),
    identity.SatisfiedBy table.semigroup →
    identity.lhs = left ++ right →
    SourceWords.Disjoint left right →
    ∃ left' right' : Word Nat,
      identity.rhs = left' ++ right' ∧
      SourceWords.Disjoint left' right' ∧
      SourceWords.SameContent left left' ∧
      SourceWords.SameContent right right' ∧
      (Identity.mk left left').SatisfiedBy table.semigroup ∧
      (Identity.mk right right').SatisfiedBy table.semigroup

private theorem eval_a0_constant
    (value : Fin 4)
    (idempotent : a0Mul value value = value)
    (word : Word Nat) :
    a0.eval (fun _ => value) word = value := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      induction tail with
      | nil => rfl
      | cons next rest ih =>
          simp only [List.foldl_cons]
          rw [show a0.mul value value = value by exact idempotent]
          exact ih

private theorem eval_a0_eq_of_agree
    {first second : Nat → Fin 4} {word : Word Nat}
    (agree : ∀ letter, letter ∈ word.toList → first letter = second letter) :
    a0.eval first word = a0.eval second word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval, Word.toList] at *
      have headAgree : first head = second head :=
        agree head (List.Mem.head tail)
      have tailAgree :
          ∀ letter ∈ tail, first letter = second letter := by
        intro letter member
        exact agree letter (List.Mem.tail head member)
      have foldAgree :
          ∀ (letters : List Nat) (leftInitial rightInitial : Fin 4),
            leftInitial = rightInitial →
            (∀ letter ∈ letters, first letter = second letter) →
            letters.foldl
                (fun current letter => a0.mul current (first letter))
                leftInitial =
              letters.foldl
                (fun current letter => a0.mul current (second letter))
                rightInitial := by
        intro letters
        induction letters with
        | nil =>
            intro leftInitial rightInitial initialEq _
            exact initialEq
        | cons letter rest ih =>
            intro leftInitial rightInitial initialEq valuesAgree
            simp only [List.foldl_cons]
            apply ih
            · rw [initialEq, valuesAgree letter (List.Mem.head rest)]
            · intro value member
              exact valuesAgree value (List.Mem.tail letter member)
      exact foldAgree tail (first head) (second head) headAgree tailAgree

private theorem component_left_valid
    {identity : Identity Nat} {left right left' right' : Word Nat}
    (valid : identity.SatisfiedBy table.semigroup)
    (leftSplit : identity.lhs = left ++ right)
    (rightSplit : identity.rhs = left' ++ right')
    (disjoint : SourceWords.Disjoint left right)
    (leftContent : SourceWords.SameContent left left')
  (rightContent : SourceWords.SameContent right right') :
    (Identity.mk left left').SatisfiedBy table.semigroup := by
  intro valuation
  by_cases same :
      table.semigroup.eval valuation left =
        table.semigroup.eval valuation left'
  · exact same
  have different :
      table.semigroup.eval valuation left ≠
        table.semigroup.eval valuation left' := same
  rcases table_idempotentSeparable
      (table.semigroup.eval valuation left)
      (table.semigroup.eval valuation left') different with
    ⟨_, ⟨rightIdempotent, rightIdempotent_mul, separates⟩⟩
  let combined : Nat → Fin 6 := fun letter =>
    if letter ∈ left.toList then valuation letter else rightIdempotent
  have evalLeft :
      table.semigroup.eval combined left =
        table.semigroup.eval valuation left :=
    eval_eq_of_agree_on_word (by
      intro letter member
      simp [combined, member])
  have evalLeft' :
      table.semigroup.eval combined left' =
        table.semigroup.eval valuation left' :=
    eval_eq_of_agree_on_word (by
      intro letter member
      have inLeft := (leftContent letter).mpr member
      simp [combined, inLeft])
  have evalRight :
      table.semigroup.eval combined right = rightIdempotent := by
    rw [eval_eq_of_agree_on_word
      (second := fun _ => rightIdempotent) (by
        intro letter member
        have notLeft :=
          SourceWords.disjoint_symm disjoint letter member
        simp [combined, notLeft])]
    exact eval_constant_idempotent rightIdempotent
      rightIdempotent_mul right
  have evalRight' :
      table.semigroup.eval combined right' = rightIdempotent := by
    rw [eval_eq_of_agree_on_word
      (second := fun _ => rightIdempotent) (by
        intro letter member
        have inRight := (rightContent letter).mpr member
        have notLeft := SourceWords.disjoint_symm disjoint letter
          inRight
        simp [combined, notLeft])]
    exact eval_constant_idempotent rightIdempotent
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
    (disjoint : SourceWords.Disjoint left right)
    (leftContent : SourceWords.SameContent left left')
  (rightContent : SourceWords.SameContent right right') :
    (Identity.mk right right').SatisfiedBy table.semigroup := by
  intro valuation
  by_cases same :
      table.semigroup.eval valuation right =
        table.semigroup.eval valuation right'
  · exact same
  have different :
      table.semigroup.eval valuation right ≠
        table.semigroup.eval valuation right' := same
  rcases table_idempotentSeparable
      (table.semigroup.eval valuation right)
      (table.semigroup.eval valuation right') different with
    ⟨⟨leftIdempotent, leftIdempotent_mul, separates⟩, _⟩
  let combined : Nat → Fin 6 := fun letter =>
    if letter ∈ right.toList then valuation letter else leftIdempotent
  have evalRight :
      table.semigroup.eval combined right =
        table.semigroup.eval valuation right :=
    eval_eq_of_agree_on_word (by
      intro letter member
      simp [combined, member])
  have evalRight' :
      table.semigroup.eval combined right' =
        table.semigroup.eval valuation right' :=
    eval_eq_of_agree_on_word (by
      intro letter member
      have inRight := (rightContent letter).mpr member
      simp [combined, inRight])
  have evalLeft :
      table.semigroup.eval combined left = leftIdempotent := by
    rw [eval_eq_of_agree_on_word
      (second := fun _ => leftIdempotent) (by
        intro letter member
        have notRight := disjoint letter member
        simp [combined, notRight])]
    exact eval_constant_idempotent leftIdempotent
      leftIdempotent_mul left
  have evalLeft' :
      table.semigroup.eval combined left' = leftIdempotent := by
    rw [eval_eq_of_agree_on_word
      (second := fun _ => leftIdempotent) (by
        intro letter member
        have inLeft := (leftContent letter).mpr member
        have notRight := disjoint letter inLeft
        simp [combined, notRight])]
    exact eval_constant_idempotent leftIdempotent
      leftIdempotent_mul left'
  have wholeEquality := valid combined
  rw [leftSplit, rightSplit, Semigroup.eval_append,
    Semigroup.eval_append, evalLeft, evalLeft', evalRight,
    evalRight'] at wholeEquality
  exact (separates wholeEquality).elim

/-- Zhang--Luo Lemma 2 for Lee's semigroup, reconstructed from the concrete
`A₀` quotient and the concrete idempotent separators above. -/
theorem property : Property := by
  intro identity left right valid leftSplit disjoint
  let color : Nat → Bool := fun letter => decide (letter ∈ left.toList)
  let valuation : Nat → Fin 4 := fun letter => colorValue (color letter)
  have leftEval :
      a0.eval valuation left = 3 := by
    rw [eval_a0_eq_of_agree (second := fun _ => 3) (by
      intro letter member
      simp [valuation, color, colorValue, member])]
    exact eval_a0_constant 3 (by decide) left
  have rightEval :
      a0.eval valuation right = 2 := by
    rw [eval_a0_eq_of_agree (second := fun _ => 2) (by
      intro letter member
      have notLeft := SourceWords.disjoint_symm disjoint letter member
      simp [valuation, color, colorValue, notLeft])]
    exact eval_a0_constant 2 (by decide) right
  have lhsEval : a0.eval valuation identity.lhs = 1 := by
    rw [leftSplit, Semigroup.eval_append, leftEval, rightEval]
    decide
  have rhsEval : a0.eval valuation identity.rhs = 1 := by
    have identityEquality := a0_in_variety valid valuation
    exact identityEquality.symm.trans lhsEval
  have colorEvaluation :
      colorEval (identity.rhs.toList.map color) = 1 := by
    rw [← eval_colorValue color identity.rhs]
    exact rhsEval
  rcases colorEval_shape colorEvaluation with
    ⟨leftCount, rightCount, leftPositive, rightPositive, colorShape⟩
  have lengthEq :
      identity.rhs.toList.length = leftCount + rightCount := by
    have lengths := congrArg List.length colorShape
    simpa using lengths
  let leftLetters := identity.rhs.toList.take leftCount
  let rightLetters := identity.rhs.toList.drop leftCount
  have leftMap :
      leftLetters.map color = List.replicate leftCount true := by
    have prefixes := congrArg (List.take leftCount) colorShape
    simpa [leftLetters] using prefixes
  have rightMap :
      rightLetters.map color = List.replicate rightCount false := by
    have suffixes := congrArg (List.drop leftCount) colorShape
    simpa [rightLetters] using suffixes
  have leftColor :
      ∀ letter, letter ∈ leftLetters → color letter = true := by
    intro letter member
    have mapped :
        color letter ∈ leftLetters.map color :=
      List.mem_map.mpr ⟨letter, member, rfl⟩
    rw [leftMap] at mapped
    simp only [List.mem_replicate] at mapped
    exact mapped.2
  have rightColor :
      ∀ letter, letter ∈ rightLetters → color letter = false := by
    intro letter member
    have mapped :
        color letter ∈ rightLetters.map color :=
      List.mem_map.mpr ⟨letter, member, rfl⟩
    rw [rightMap] at mapped
    simp only [List.mem_replicate] at mapped
    exact mapped.2
  have rhsLettersSplit :
      identity.rhs.toList = leftLetters ++ rightLetters := by
    exact (List.take_append_drop leftCount identity.rhs.toList).symm
  have leftContentList :
      ∀ letter, letter ∈ left.toList ↔ letter ∈ leftLetters := by
    intro letter
    constructor
    · intro inLeft
      have inLhs : letter ∈ identity.lhs.toList := by
        rw [leftSplit, Word.toList_append]
        exact List.mem_append.mpr (Or.inl inLeft)
      have inRhs := (valid_identity_sameContent valid letter).mp inLhs
      rw [rhsLettersSplit] at inRhs
      rcases List.mem_append.mp inRhs with inLeftLetters | inRightLetters
      · exact inLeftLetters
      · have isFalse := rightColor letter inRightLetters
        have isTrue : color letter = true := by
          simp [color, inLeft]
        have impossible : true = false := isTrue.symm.trans isFalse
        cases impossible
    · intro inLeftLetters
      have isTrue := leftColor letter inLeftLetters
      by_cases inLeft : letter ∈ left.toList
      · exact inLeft
      · have isFalse : color letter = false := by
          simp [color, inLeft]
        have impossible : true = false := isTrue.symm.trans isFalse
        cases impossible
  have rightContentList :
      ∀ letter, letter ∈ right.toList ↔ letter ∈ rightLetters := by
    intro letter
    constructor
    · intro inRight
      have inLhs : letter ∈ identity.lhs.toList := by
        rw [leftSplit, Word.toList_append]
        exact List.mem_append.mpr (Or.inr inRight)
      have inRhs := (valid_identity_sameContent valid letter).mp inLhs
      rw [rhsLettersSplit] at inRhs
      rcases List.mem_append.mp inRhs with inLeftLetters | inRightLetters
      · have isTrue := leftColor letter inLeftLetters
        have notLeft := SourceWords.disjoint_symm disjoint letter inRight
        have isFalse : color letter = false := by
          simp [color, notLeft]
        have impossible : true = false := isTrue.symm.trans isFalse
        cases impossible
      · exact inRightLetters
    · intro inRightLetters
      have isFalse := rightColor letter inRightLetters
      have inRhs : letter ∈ identity.rhs.toList := by
        rw [rhsLettersSplit]
        exact List.mem_append.mpr (Or.inr inRightLetters)
      have inLhs := (valid_identity_sameContent valid letter).mpr inRhs
      rw [leftSplit, Word.toList_append] at inLhs
      rcases List.mem_append.mp inLhs with inLeft | inRight
      · have isTrue : color letter = true := by
          simp [color, inLeft]
        have impossible : true = false := isTrue.symm.trans isFalse
        cases impossible
      · exact inRight
  have leftLettersNonempty : leftLetters ≠ [] := by
    intro empty
    have leftLength :
        leftLetters.length = leftCount := by
      simp [leftLetters, lengthEq]
    rw [empty] at leftLength
    simp at leftLength
    omega
  have rightLettersNonempty : rightLetters ≠ [] := by
    intro empty
    have rightLength :
        rightLetters.length = rightCount := by
      simp [rightLetters, lengthEq]
    rw [empty] at rightLength
    simp at rightLength
    omega
  cases leftLettersEq : leftLetters with
  | nil => exact (leftLettersNonempty leftLettersEq).elim
  | cons leftHead leftTail =>
      cases rightLettersEq : rightLetters with
      | nil => exact (rightLettersNonempty rightLettersEq).elim
      | cons rightHead rightTail =>
          let left' : Word Nat := ⟨leftHead, leftTail⟩
          let right' : Word Nat := ⟨rightHead, rightTail⟩
          have rightSplit : identity.rhs = left' ++ right' := by
            apply Word.toList_injective
            change identity.rhs.toList =
              (leftHead :: leftTail) ++ (rightHead :: rightTail)
            rw [← leftLettersEq, ← rightLettersEq]
            exact rhsLettersSplit
          have leftContent : SourceWords.SameContent left left' := by
            intro letter
            change letter ∈ left.toList ↔ letter ∈ leftHead :: leftTail
            rw [← leftLettersEq]
            exact leftContentList letter
          have rightContent : SourceWords.SameContent right right' := by
            intro letter
            change letter ∈ right.toList ↔ letter ∈ rightHead :: rightTail
            rw [← rightLettersEq]
            exact rightContentList letter
          have rightDisjoint : SourceWords.Disjoint left' right' := by
            intro letter inLeftPrime inRightPrime
            have inLeftLetters : letter ∈ leftLetters := by
              rw [leftLettersEq]
              exact inLeftPrime
            have inRightLetters : letter ∈ rightLetters := by
              rw [rightLettersEq]
              exact inRightPrime
            have isTrue := leftColor letter inLeftLetters
            have isFalse := rightColor letter inRightLetters
            have impossible : true = false := isTrue.symm.trans isFalse
            cases impossible
          exact
            ⟨left', right', rightSplit, rightDisjoint, leftContent,
              rightContent,
              component_left_valid valid leftSplit rightSplit disjoint
                leftContent rightContent,
              component_right_valid valid leftSplit rightSplit disjoint
                leftContent rightContent⟩

end OrderedSplit

end SemigroupBasis.Examples.LeeL

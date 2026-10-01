import SemigroupBasis.CoRoots.S5_213Syntax
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.Generated.CatalogueOrder5Part04

namespace SemigroupBasis.CoRoots.S5_213Invariant

open SemigroupBasis
open SemigroupBasis.CoRoots

private def s5_213ListEval
    (valuation : Nat → Fin 5) (letters : List Nat) : Fin 5 :=
  letters.foldl
    (fun value letter =>
      Generated.Catalogue.S5_213.table.mul value (valuation letter))
    4

private def s5_498ListEval
    (valuation : Nat → Fin 5) (letters : List Nat) : Fin 5 :=
  letters.foldl
    (fun value letter =>
      Generated.Catalogue.S5_498.table.mul value (valuation letter))
    4

theorem s5_213_element_five_identity (value : Fin 5) :
    Generated.Catalogue.S5_213.table.mul (4 : Fin 5) value = value ∧
      Generated.Catalogue.S5_213.table.mul value (4 : Fin 5) = value := by
  constructor <;> apply Fin.ext <;> revert value <;> decide

theorem s5_498_element_five_identity (value : Fin 5) :
    Generated.Catalogue.S5_498.table.mul (4 : Fin 5) value = value ∧
      Generated.Catalogue.S5_498.table.mul value (4 : Fin 5) = value := by
  constructor <;> apply Fin.ext <;> revert value <;> decide

theorem s5_213_element_four_power_codes :
    Generated.Catalogue.S5_213.table.mul (3 : Fin 5) (3 : Fin 5) =
        (1 : Fin 5) ∧
      Generated.Catalogue.S5_213.table.mul (1 : Fin 5) (3 : Fin 5) =
        (0 : Fin 5) ∧
      Generated.Catalogue.S5_213.table.mul (0 : Fin 5) (3 : Fin 5) =
        (0 : Fin 5) := by
  decide

theorem s5_498_element_four_power_codes :
    Generated.Catalogue.S5_498.table.mul (3 : Fin 5) (3 : Fin 5) =
        (1 : Fin 5) ∧
      Generated.Catalogue.S5_498.table.mul (1 : Fin 5) (3 : Fin 5) =
        (0 : Fin 5) ∧
      Generated.Catalogue.S5_498.table.mul (0 : Fin 5) (3 : Fin 5) =
        (0 : Fin 5) := by
  decide

theorem s5_213_singleton_order_separator :
    Generated.Catalogue.S5_213.table.mul (3 : Fin 5) (2 : Fin 5) =
        (1 : Fin 5) ∧
      Generated.Catalogue.S5_213.table.mul (2 : Fin 5) (3 : Fin 5) =
        (0 : Fin 5) := by
  decide

theorem s5_498_singleton_order_separator :
    Generated.Catalogue.S5_498.table.mul (3 : Fin 5) (2 : Fin 5) =
        (1 : Fin 5) ∧
      Generated.Catalogue.S5_498.table.mul (2 : Fin 5) (3 : Fin 5) =
        (0 : Fin 5) := by
  decide

private theorem s5_213_eval_eq_listEval
    (valuation : Nat → Fin 5) (word : Word Nat) :
    Generated.Catalogue.S5_213.table.semigroup.eval valuation word =
      s5_213ListEval valuation word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun value letter =>
              Generated.Catalogue.S5_213.table.mul value
                (valuation letter))
            (valuation head) =
          tail.foldl
            (fun value letter =>
              Generated.Catalogue.S5_213.table.mul value
                (valuation letter))
            (Generated.Catalogue.S5_213.table.mul
              (4 : Fin 5) (valuation head))
      rw [(s5_213_element_five_identity (valuation head)).1]

private theorem s5_498_eval_eq_listEval
    (valuation : Nat → Fin 5) (word : Word Nat) :
    Generated.Catalogue.S5_498.table.semigroup.eval valuation word =
      s5_498ListEval valuation word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun value letter =>
              Generated.Catalogue.S5_498.table.mul value
                (valuation letter))
            (valuation head) =
          tail.foldl
            (fun value letter =>
              Generated.Catalogue.S5_498.table.mul value
                (valuation letter))
            (Generated.Catalogue.S5_498.table.mul
              (4 : Fin 5) (valuation head))
      rw [(s5_498_element_five_identity (valuation head)).1]

private def multiplicityValuation
    (selected : Nat) : Nat → Fin 5 :=
  fun letter => if letter = selected then 3 else 4

private def multiplicityCode (count : Nat) : Fin 5 :=
  if count = 0 then 4
  else if count = 1 then 3
  else if count = 2 then 1
  else 0

private theorem s5_213_multiplicityCode_selected (count : Nat) :
    Generated.Catalogue.S5_213.table.mul
        (multiplicityCode count) (3 : Fin 5) =
      multiplicityCode (count + 1) := by
  by_cases zero : count = 0
  · subst count
    decide
  · by_cases one : count = 1
    · subst count
      decide
    · by_cases two : count = 2
      · subst count
        decide
      · have successorZero : count + 1 ≠ 0 := by omega
        have successorOne : count + 1 ≠ 1 := by omega
        have successorTwo : count + 1 ≠ 2 := by omega
        simp [multiplicityCode, zero, one, two, successorZero,
          successorOne, successorTwo,
          Generated.Catalogue.S5_213.table,
          Generated.Catalogue.S5_213.mul]

private theorem s5_498_multiplicityCode_selected (count : Nat) :
    Generated.Catalogue.S5_498.table.mul
        (multiplicityCode count) (3 : Fin 5) =
      multiplicityCode (count + 1) := by
  by_cases zero : count = 0
  · subst count
    decide
  · by_cases one : count = 1
    · subst count
      decide
    · by_cases two : count = 2
      · subst count
        decide
      · have successorZero : count + 1 ≠ 0 := by omega
        have successorOne : count + 1 ≠ 1 := by omega
        have successorTwo : count + 1 ≠ 2 := by omega
        simp [multiplicityCode, zero, one, two, successorZero,
          successorOne, successorTwo,
          Generated.Catalogue.S5_498.table,
          Generated.Catalogue.S5_498.mul]

private theorem s5_213_multiplicityFold
    (selected : Nat) :
    ∀ (letters : List Nat) (initialCount : Nat),
      letters.foldl
          (fun value letter =>
            Generated.Catalogue.S5_213.table.mul value
              (multiplicityValuation selected letter))
          (multiplicityCode initialCount) =
        multiplicityCode
          (initialCount + letters.count selected)
  | [], _ => by simp
  | letter :: rest, initialCount => by
      simp only [List.foldl_cons]
      by_cases equal : letter = selected
      · subst letter
        rw [show multiplicityValuation selected selected = (3 : Fin 5) by
          simp [multiplicityValuation]]
        rw [s5_213_multiplicityCode_selected]
        rw [s5_213_multiplicityFold selected rest (initialCount + 1)]
        congr 1
        simp
        omega
      · rw [show multiplicityValuation selected letter = (4 : Fin 5) by
          simp [multiplicityValuation, equal]]
        rw [(s5_213_element_five_identity
          (multiplicityCode initialCount)).2]
        rw [s5_213_multiplicityFold selected rest initialCount]
        simp [equal]

private theorem s5_498_multiplicityFold
    (selected : Nat) :
    ∀ (letters : List Nat) (initialCount : Nat),
      letters.foldl
          (fun value letter =>
            Generated.Catalogue.S5_498.table.mul value
              (multiplicityValuation selected letter))
          (multiplicityCode initialCount) =
        multiplicityCode
          (initialCount + letters.count selected)
  | [], _ => by simp
  | letter :: rest, initialCount => by
      simp only [List.foldl_cons]
      by_cases equal : letter = selected
      · subst letter
        rw [show multiplicityValuation selected selected = (3 : Fin 5) by
          simp [multiplicityValuation]]
        rw [s5_498_multiplicityCode_selected]
        rw [s5_498_multiplicityFold selected rest (initialCount + 1)]
        congr 1
        simp
        omega
      · rw [show multiplicityValuation selected letter = (4 : Fin 5) by
          simp [multiplicityValuation, equal]]
        rw [(s5_498_element_five_identity
          (multiplicityCode initialCount)).2]
        rw [s5_498_multiplicityFold selected rest initialCount]
        simp [equal]

private theorem s5_213_eval_multiplicity
    (word : Word Nat) (selected : Nat) :
    Generated.Catalogue.S5_213.table.semigroup.eval
        (multiplicityValuation selected) word =
      multiplicityCode (word.toList.count selected) := by
  rw [s5_213_eval_eq_listEval]
  unfold s5_213ListEval
  simpa [multiplicityCode] using
    s5_213_multiplicityFold selected word.toList 0

private theorem s5_498_eval_multiplicity
    (word : Word Nat) (selected : Nat) :
    Generated.Catalogue.S5_498.table.semigroup.eval
        (multiplicityValuation selected) word =
      multiplicityCode (word.toList.count selected) := by
  rw [s5_498_eval_eq_listEval]
  unfold s5_498ListEval
  simpa [multiplicityCode] using
    s5_498_multiplicityFold selected word.toList 0

private theorem multiplicityCode_reflects_cap
    {leftCount rightCount : Nat}
    (equal :
      multiplicityCode leftCount =
        multiplicityCode rightCount) :
    Nat.min 3 leftCount = Nat.min 3 rightCount := by
  by_cases leftZero : leftCount = 0
  · subst leftCount
    by_cases rightZero : rightCount = 0
    · subst rightCount
      rfl
    · by_cases rightOne : rightCount = 1
      · subst rightCount
        simp [multiplicityCode] at equal
      · by_cases rightTwo : rightCount = 2
        · subst rightCount
          simp [multiplicityCode] at equal
        · simp [multiplicityCode, rightZero, rightOne, rightTwo] at equal
  · by_cases leftOne : leftCount = 1
    · subst leftCount
      by_cases rightZero : rightCount = 0
      · subst rightCount
        simp [multiplicityCode] at equal
      · by_cases rightOne : rightCount = 1
        · subst rightCount
          rfl
        · by_cases rightTwo : rightCount = 2
          · subst rightCount
            simp [multiplicityCode] at equal
          · simp [multiplicityCode, rightZero, rightOne, rightTwo] at equal
    · by_cases leftTwo : leftCount = 2
      · subst leftCount
        by_cases rightZero : rightCount = 0
        · subst rightCount
          simp [multiplicityCode] at equal
        · by_cases rightOne : rightCount = 1
          · subst rightCount
            simp [multiplicityCode] at equal
          · by_cases rightTwo : rightCount = 2
            · subst rightCount
              rfl
            · simp [multiplicityCode, rightZero, rightOne, rightTwo] at equal
      · by_cases rightZero : rightCount = 0
        · subst rightCount
          simp [multiplicityCode, leftZero, leftOne, leftTwo] at equal
        · by_cases rightOne : rightCount = 1
          · subst rightCount
            simp [multiplicityCode, leftZero, leftOne, leftTwo] at equal
          · by_cases rightTwo : rightCount = 2
            · subst rightCount
              simp [multiplicityCode, leftZero, leftOne, leftTwo] at equal
            · simp only [Nat.min_def]
              split <;> split <;> omega

theorem s5_213_valid_cappedMultiplicity
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_213.table.semigroup)
    (letter : Nat) :
    S5_213Syntax.cappedMultiplicity identity.lhs letter =
      S5_213Syntax.cappedMultiplicity identity.rhs letter := by
  have evaluated := valid (multiplicityValuation letter)
  rw [s5_213_eval_multiplicity,
    s5_213_eval_multiplicity] at evaluated
  exact multiplicityCode_reflects_cap evaluated

theorem s5_498_valid_cappedMultiplicity
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_498.table.semigroup)
    (letter : Nat) :
    S5_213Syntax.cappedMultiplicity identity.lhs letter =
      S5_213Syntax.cappedMultiplicity identity.rhs letter := by
  have evaluated := valid (multiplicityValuation letter)
  rw [s5_498_eval_multiplicity,
    s5_498_eval_multiplicity] at evaluated
  exact multiplicityCode_reflects_cap evaluated

private def pairSymbolValue : S5_213Syntax.PairSymbol → Fin 5
  | .other => 4
  | .x => 3
  | .y => 2

private def pairValuation (x y : Nat) : Nat → Fin 5 :=
  fun letter =>
    pairSymbolValue (S5_213Syntax.pairSymbol x y letter)

private def s5_213PairStateValue :
    S5_213Syntax.PairState → Fin 5
  | .empty => 4
  | .x1 => 3
  | .x2 => 1
  | .x3 => 0
  | .y1 => 2
  | .y2 => 0
  | .y3 => 0
  | .xy => 1
  | .yx => 0
  | .x1y2 | .x1y3 | .x2y1 | .x3y1
  | .x2y2 | .x2y3 | .x3y2 | .x3y3 => 0

private def s5_498PairStateValue :
    S5_213Syntax.PairState → Fin 5
  | .empty => 4
  | .x1 => 3
  | .x2 => 1
  | .x3 => 0
  | .y1 => 2
  | .y2 => 1
  | .y3 => 0
  | .xy => 1
  | .yx => 0
  | .x1y2 | .x1y3 | .x2y1 | .x3y1
  | .x2y2 | .x2y3 | .x3y2 | .x3y3 => 0

private theorem s5_213_pairStep_value
    (state : S5_213Syntax.PairState)
    (symbol : S5_213Syntax.PairSymbol) :
    Generated.Catalogue.S5_213.table.mul
        (s5_213PairStateValue state) (pairSymbolValue symbol) =
      s5_213PairStateValue (S5_213Syntax.pairStep state symbol) := by
  cases state <;> cases symbol <;> decide

private theorem s5_498_pairStep_value
    (state : S5_213Syntax.PairState)
    (symbol : S5_213Syntax.PairSymbol) :
    Generated.Catalogue.S5_498.table.mul
        (s5_498PairStateValue state) (pairSymbolValue symbol) =
      s5_498PairStateValue (S5_213Syntax.pairStep state symbol) := by
  cases state <;> cases symbol <;> decide

private theorem pairStep_xCount
    (state : S5_213Syntax.PairState)
    (symbol : S5_213Syntax.PairSymbol) :
    (S5_213Syntax.pairStep state symbol).xCount =
      Nat.min 3
        (state.xCount + if symbol = .x then 1 else 0) := by
  cases state <;> cases symbol <;> decide

private theorem pairStep_yCount
    (state : S5_213Syntax.PairState)
    (symbol : S5_213Syntax.PairSymbol) :
    (S5_213Syntax.pairStep state symbol).yCount =
      Nat.min 3
        (state.yCount + if symbol = .y then 1 else 0) := by
  cases state <;> cases symbol <;> decide

private theorem pairState_xCount_le_three
    (state : S5_213Syntax.PairState) :
    state.xCount ≤ 3 := by
  cases state <;> decide

private theorem pairState_yCount_le_three
    (state : S5_213Syntax.PairState) :
    state.yCount ≤ 3 := by
  cases state <;> decide

private theorem cap_three_cap_add (left right : Nat) :
    Nat.min 3 (Nat.min 3 left + right) =
      Nat.min 3 (left + right) := by
  by_cases capped : 3 ≤ left
  · have inner : Nat.min 3 left = 3 :=
      Nat.min_eq_left capped
    calc
      Nat.min 3 (Nat.min 3 left + right) =
          Nat.min 3 (3 + right) := by rw [inner]
      _ = 3 := Nat.min_eq_left (by omega)
      _ = Nat.min 3 (left + right) :=
        (Nat.min_eq_left (by omega)).symm
  · have below : left ≤ 3 := by omega
    have inner : Nat.min 3 left = left :=
      Nat.min_eq_right below
    rw [inner]

private theorem pairFold_xCount (x y : Nat) :
    ∀ (letters : List Nat) (initial : S5_213Syntax.PairState),
      (letters.foldl
          (fun state letter =>
            S5_213Syntax.pairStep state
              (S5_213Syntax.pairSymbol x y letter))
          initial).xCount =
        Nat.min 3 (initial.xCount + letters.count x)
  | [], initial => by
      simpa using
        (Nat.min_eq_right (pairState_xCount_le_three initial)).symm
  | letter :: rest, initial => by
      simp only [List.foldl_cons]
      rw [pairFold_xCount x y rest]
      rw [pairStep_xCount]
      by_cases equal : letter = x
      · subst letter
        simp only [S5_213Syntax.pairSymbol, if_pos,
          List.count_cons_self]
        rw [cap_three_cap_add]
        congr 1
        omega
      · have symbolNotX :
            S5_213Syntax.pairSymbol x y letter ≠ .x := by
          unfold S5_213Syntax.pairSymbol
          rw [if_neg equal]
          split <;> decide
        rw [if_neg symbolNotX]
        rw [cap_three_cap_add]
        simp [equal]

private theorem pairFold_yCount (x y : Nat) (different : x ≠ y) :
    ∀ (letters : List Nat) (initial : S5_213Syntax.PairState),
      (letters.foldl
          (fun state letter =>
            S5_213Syntax.pairStep state
              (S5_213Syntax.pairSymbol x y letter))
          initial).yCount =
        Nat.min 3 (initial.yCount + letters.count y)
  | [], initial => by
      simpa using
        (Nat.min_eq_right (pairState_yCount_le_three initial)).symm
  | letter :: rest, initial => by
      simp only [List.foldl_cons]
      rw [pairFold_yCount x y different rest]
      rw [pairStep_yCount]
      by_cases isY : letter = y
      · subst letter
        have notX : y ≠ x := Ne.symm different
        simp only [S5_213Syntax.pairSymbol, if_neg notX, if_pos,
          List.count_cons_self]
        rw [cap_three_cap_add]
        congr 1
        omega
      · have symbolNotY :
            S5_213Syntax.pairSymbol x y letter ≠ .y := by
          unfold S5_213Syntax.pairSymbol
          split <;> decide
        rw [if_neg symbolNotY]
        rw [cap_three_cap_add]
        simp [isY]

private theorem s5_213_pairFold_value (x y : Nat) :
    ∀ (letters : List Nat) (initial : S5_213Syntax.PairState),
      letters.foldl
          (fun value letter =>
            Generated.Catalogue.S5_213.table.mul value
              (pairValuation x y letter))
          (s5_213PairStateValue initial) =
        s5_213PairStateValue
          (letters.foldl
            (fun state letter =>
              S5_213Syntax.pairStep state
                (S5_213Syntax.pairSymbol x y letter))
            initial)
  | [], _ => rfl
  | letter :: rest, initial => by
      simp only [List.foldl_cons, pairValuation]
      rw [s5_213_pairStep_value]
      exact s5_213_pairFold_value x y rest
        (S5_213Syntax.pairStep initial
          (S5_213Syntax.pairSymbol x y letter))

private theorem s5_498_pairFold_value (x y : Nat) :
    ∀ (letters : List Nat) (initial : S5_213Syntax.PairState),
      letters.foldl
          (fun value letter =>
            Generated.Catalogue.S5_498.table.mul value
              (pairValuation x y letter))
          (s5_498PairStateValue initial) =
        s5_498PairStateValue
          (letters.foldl
            (fun state letter =>
              S5_213Syntax.pairStep state
                (S5_213Syntax.pairSymbol x y letter))
            initial)
  | [], _ => rfl
  | letter :: rest, initial => by
      simp only [List.foldl_cons, pairValuation]
      rw [s5_498_pairStep_value]
      exact s5_498_pairFold_value x y rest
        (S5_213Syntax.pairStep initial
          (S5_213Syntax.pairSymbol x y letter))

private theorem pairScan_xCount
    (word : Word Nat) (x y : Nat) :
    (S5_213Syntax.pairScan word x y).xCount =
      S5_213Syntax.cappedMultiplicity word x := by
  unfold S5_213Syntax.pairScan S5_213Syntax.cappedMultiplicity
  simpa [S5_213Syntax.PairState.xCount] using
    pairFold_xCount x y word.toList .empty

private theorem pairScan_yCount
    (word : Word Nat) {x y : Nat} (different : x ≠ y) :
    (S5_213Syntax.pairScan word x y).yCount =
      S5_213Syntax.cappedMultiplicity word y := by
  unfold S5_213Syntax.pairScan S5_213Syntax.cappedMultiplicity
  simpa [S5_213Syntax.PairState.yCount] using
    pairFold_yCount x y different word.toList .empty

private theorem s5_213_eval_pair
    (word : Word Nat) (x y : Nat) :
    Generated.Catalogue.S5_213.table.semigroup.eval
        (pairValuation x y) word =
      s5_213PairStateValue
        (S5_213Syntax.pairScan word x y) := by
  rw [s5_213_eval_eq_listEval]
  unfold s5_213ListEval S5_213Syntax.pairScan
  simpa [s5_213PairStateValue] using
    s5_213_pairFold_value x y word.toList .empty

private theorem s5_498_eval_pair
    (word : Word Nat) (x y : Nat) :
    Generated.Catalogue.S5_498.table.semigroup.eval
        (pairValuation x y) word =
      s5_498PairStateValue
        (S5_213Syntax.pairScan word x y) := by
  rw [s5_498_eval_eq_listEval]
  unfold s5_498ListEval S5_213Syntax.pairScan
  simpa [s5_498PairStateValue] using
    s5_498_pairFold_value x y word.toList .empty

private theorem s5_213_state_eq_xy_of_counts_value
    (state : S5_213Syntax.PairState)
    (xCount : state.xCount = 1)
    (yCount : state.yCount = 1)
    (value : s5_213PairStateValue state = 1) :
    state = .xy := by
  cases state <;>
    simp_all [S5_213Syntax.PairState.xCount,
      S5_213Syntax.PairState.yCount, s5_213PairStateValue]

private theorem s5_498_state_eq_xy_of_counts_value
    (state : S5_213Syntax.PairState)
    (xCount : state.xCount = 1)
    (yCount : state.yCount = 1)
    (value : s5_498PairStateValue state = 1) :
    state = .xy := by
  cases state <;>
    simp_all [S5_213Syntax.PairState.xCount,
      S5_213Syntax.PairState.yCount, s5_498PairStateValue]

private theorem s5_213_simplePrecedes_forward
    {left right : Word Nat} {x y : Nat}
    (equalEval :
      s5_213PairStateValue (S5_213Syntax.pairScan left x y) =
        s5_213PairStateValue (S5_213Syntax.pairScan right x y))
    (capped :
      ∀ letter,
        S5_213Syntax.cappedMultiplicity left letter =
          S5_213Syntax.cappedMultiplicity right letter)
    (precedes : S5_213Syntax.SimplePrecedes left x y) :
    S5_213Syntax.SimplePrecedes right x y := by
  rcases precedes with ⟨different, leftState⟩
  refine ⟨different, ?_⟩
  have rightXCount :
      (S5_213Syntax.pairScan right x y).xCount = 1 := by
    calc
      _ = S5_213Syntax.cappedMultiplicity right x :=
        pairScan_xCount right x y
      _ = S5_213Syntax.cappedMultiplicity left x :=
        (capped x).symm
      _ = (S5_213Syntax.pairScan left x y).xCount :=
        (pairScan_xCount left x y).symm
      _ = 1 := by rw [leftState]; rfl
  have rightYCount :
      (S5_213Syntax.pairScan right x y).yCount = 1 := by
    calc
      _ = S5_213Syntax.cappedMultiplicity right y :=
        pairScan_yCount right different
      _ = S5_213Syntax.cappedMultiplicity left y :=
        (capped y).symm
      _ = (S5_213Syntax.pairScan left x y).yCount :=
        (pairScan_yCount left different).symm
      _ = 1 := by rw [leftState]; rfl
  have rightValue :
      s5_213PairStateValue
          (S5_213Syntax.pairScan right x y) = 1 := by
    rw [← equalEval, leftState]
    rfl
  exact s5_213_state_eq_xy_of_counts_value
    (S5_213Syntax.pairScan right x y)
    rightXCount rightYCount rightValue

private theorem s5_498_simplePrecedes_forward
    {left right : Word Nat} {x y : Nat}
    (equalEval :
      s5_498PairStateValue (S5_213Syntax.pairScan left x y) =
        s5_498PairStateValue (S5_213Syntax.pairScan right x y))
    (capped :
      ∀ letter,
        S5_213Syntax.cappedMultiplicity left letter =
          S5_213Syntax.cappedMultiplicity right letter)
    (precedes : S5_213Syntax.SimplePrecedes left x y) :
    S5_213Syntax.SimplePrecedes right x y := by
  rcases precedes with ⟨different, leftState⟩
  refine ⟨different, ?_⟩
  have rightXCount :
      (S5_213Syntax.pairScan right x y).xCount = 1 := by
    calc
      _ = S5_213Syntax.cappedMultiplicity right x :=
        pairScan_xCount right x y
      _ = S5_213Syntax.cappedMultiplicity left x :=
        (capped x).symm
      _ = (S5_213Syntax.pairScan left x y).xCount :=
        (pairScan_xCount left x y).symm
      _ = 1 := by rw [leftState]; rfl
  have rightYCount :
      (S5_213Syntax.pairScan right x y).yCount = 1 := by
    calc
      _ = S5_213Syntax.cappedMultiplicity right y :=
        pairScan_yCount right different
      _ = S5_213Syntax.cappedMultiplicity left y :=
        (capped y).symm
      _ = (S5_213Syntax.pairScan left x y).yCount :=
        (pairScan_yCount left different).symm
      _ = 1 := by rw [leftState]; rfl
  have rightValue :
      s5_498PairStateValue
          (S5_213Syntax.pairScan right x y) = 1 := by
    rw [← equalEval, leftState]
    rfl
  exact s5_498_state_eq_xy_of_counts_value
    (S5_213Syntax.pairScan right x y)
    rightXCount rightYCount rightValue

theorem s5_213_valid_simplePrecedes
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_213.table.semigroup)
    (capped :
      ∀ letter,
        S5_213Syntax.cappedMultiplicity identity.lhs letter =
          S5_213Syntax.cappedMultiplicity identity.rhs letter)
    (x y : Nat) :
    S5_213Syntax.SimplePrecedes identity.lhs x y ↔
      S5_213Syntax.SimplePrecedes identity.rhs x y := by
  have evaluated := valid (pairValuation x y)
  rw [s5_213_eval_pair, s5_213_eval_pair] at evaluated
  constructor
  · exact s5_213_simplePrecedes_forward evaluated capped
  · exact s5_213_simplePrecedes_forward evaluated.symm
      (fun letter => (capped letter).symm)

theorem s5_498_valid_simplePrecedes
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_498.table.semigroup)
    (capped :
      ∀ letter,
        S5_213Syntax.cappedMultiplicity identity.lhs letter =
          S5_213Syntax.cappedMultiplicity identity.rhs letter)
    (x y : Nat) :
    S5_213Syntax.SimplePrecedes identity.lhs x y ↔
      S5_213Syntax.SimplePrecedes identity.rhs x y := by
  have evaluated := valid (pairValuation x y)
  rw [s5_498_eval_pair, s5_498_eval_pair] at evaluated
  constructor
  · exact s5_498_simplePrecedes_forward evaluated capped
  · exact s5_498_simplePrecedes_forward evaluated.symm
      (fun letter => (capped letter).symm)

theorem sameSignature_of_s5_213_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_213.table.semigroup) :
    S5_213Syntax.SameCappedSingletonSignature
      identity.lhs identity.rhs := by
  have capped :
      ∀ letter,
        S5_213Syntax.cappedMultiplicity identity.lhs letter =
          S5_213Syntax.cappedMultiplicity identity.rhs letter :=
    fun letter =>
      s5_213_valid_cappedMultiplicity identity valid letter
  exact
    ⟨capped, fun x y =>
      s5_213_valid_simplePrecedes identity valid capped x y⟩

theorem sameSignature_of_s5_498_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_498.table.semigroup) :
    S5_213Syntax.SameCappedSingletonSignature
      identity.lhs identity.rhs := by
  have capped :
      ∀ letter,
        S5_213Syntax.cappedMultiplicity identity.lhs letter =
          S5_213Syntax.cappedMultiplicity identity.rhs letter :=
    fun letter =>
      s5_498_valid_cappedMultiplicity identity valid letter
  exact
    ⟨capped, fun x y =>
      s5_498_valid_simplePrecedes identity valid capped x y⟩

end SemigroupBasis.CoRoots.S5_213Invariant

namespace SemigroupBasis.CoRoots.S5_213

open SemigroupBasis

/-- Every formal consequence of the three laws preserves the exact capped
multiplicity and ordered-singleton signature. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_213Syntax.SameCappedSingletonSignature left right := by
  have targetModels :
      Models Generated.Catalogue.S5_213.table.semigroup basis :=
    models_of_finite_checks
      Generated.Catalogue.S5_213.table (by decide)
  exact S5_213Invariant.sameSignature_of_s5_213_valid
    ⟨left, right⟩
    (fun valuation => derivation.sound targetModels valuation)

end SemigroupBasis.CoRoots.S5_213

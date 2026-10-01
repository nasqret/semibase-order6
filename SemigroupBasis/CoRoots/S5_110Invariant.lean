import SemigroupBasis.CoRoots.S5_110Syntax

namespace SemigroupBasis.CoRoots.S5_110Invariant

open SemigroupBasis
open SemigroupBasis.CoRoots

private def s5_110ListEval
    (valuation : Nat → Fin 5) (letters : List Nat) : Fin 5 :=
  letters.foldl
    (fun value letter =>
      Generated.Catalogue.S5_110.table.mul value (valuation letter))
    4

theorem s5_110_element_five_identity (value : Fin 5) :
    Generated.Catalogue.S5_110.table.mul (4 : Fin 5) value = value ∧
      Generated.Catalogue.S5_110.table.mul value (4 : Fin 5) = value := by
  constructor <;> apply Fin.ext <;> revert value <;> decide

theorem s5_110_element_four_power_codes :
    Generated.Catalogue.S5_110.table.mul (3 : Fin 5) (3 : Fin 5) =
        (0 : Fin 5) ∧
      Generated.Catalogue.S5_110.table.mul (0 : Fin 5) (3 : Fin 5) =
        (0 : Fin 5) := by
  decide

theorem s5_110_singleton_order_separator :
    Generated.Catalogue.S5_110.table.mul (3 : Fin 5) (2 : Fin 5) =
        (1 : Fin 5) ∧
      Generated.Catalogue.S5_110.table.mul (2 : Fin 5) (3 : Fin 5) =
        (0 : Fin 5) := by
  decide

private theorem s5_110_eval_eq_listEval
    (valuation : Nat → Fin 5) (word : Word Nat) :
    Generated.Catalogue.S5_110.table.semigroup.eval valuation word =
      s5_110ListEval valuation word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun value letter =>
              Generated.Catalogue.S5_110.table.mul value
                (valuation letter))
            (valuation head) =
          tail.foldl
            (fun value letter =>
              Generated.Catalogue.S5_110.table.mul value
                (valuation letter))
            (Generated.Catalogue.S5_110.table.mul
              (4 : Fin 5) (valuation head))
      rw [(s5_110_element_five_identity (valuation head)).1]

private def multiplicityValuation
    (selected : Nat) : Nat → Fin 5 :=
  fun letter => if letter = selected then 3 else 4

private def multiplicityCode (count : Nat) : Fin 5 :=
  if count = 0 then 4
  else if count = 1 then 3
  else 0

private theorem s5_110_multiplicityCode_selected (count : Nat) :
    Generated.Catalogue.S5_110.table.mul
        (multiplicityCode count) (3 : Fin 5) =
      multiplicityCode (count + 1) := by
  by_cases zero : count = 0
  · subst count
    decide
  · by_cases one : count = 1
    · subst count
      decide
    · have successorZero : count + 1 ≠ 0 := by omega
      have successorOne : count + 1 ≠ 1 := by omega
      simp [multiplicityCode, zero, one, successorZero,
        successorOne, Generated.Catalogue.S5_110.table,
        Generated.Catalogue.S5_110.mul]

private theorem s5_110_multiplicityFold
    (selected : Nat) :
    ∀ (letters : List Nat) (initialCount : Nat),
      letters.foldl
          (fun value letter =>
            Generated.Catalogue.S5_110.table.mul value
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
        rw [s5_110_multiplicityCode_selected]
        rw [s5_110_multiplicityFold selected rest (initialCount + 1)]
        congr 1
        simp
        omega
      · rw [show multiplicityValuation selected letter = (4 : Fin 5) by
          simp [multiplicityValuation, equal]]
        rw [(s5_110_element_five_identity
          (multiplicityCode initialCount)).2]
        rw [s5_110_multiplicityFold selected rest initialCount]
        simp [equal]

private theorem s5_110_eval_multiplicity
    (word : Word Nat) (selected : Nat) :
    Generated.Catalogue.S5_110.table.semigroup.eval
        (multiplicityValuation selected) word =
      multiplicityCode (word.toList.count selected) := by
  rw [s5_110_eval_eq_listEval]
  unfold s5_110ListEval
  simpa [multiplicityCode] using
    s5_110_multiplicityFold selected word.toList 0

private theorem multiplicityCode_reflects_cap
    {leftCount rightCount : Nat}
    (equal :
      multiplicityCode leftCount =
        multiplicityCode rightCount) :
    Nat.min 2 leftCount = Nat.min 2 rightCount := by
  by_cases leftZero : leftCount = 0
  · subst leftCount
    by_cases rightZero : rightCount = 0
    · subst rightCount
      rfl
    · by_cases rightOne : rightCount = 1
      · subst rightCount
        simp [multiplicityCode] at equal
      · simp [multiplicityCode, rightZero, rightOne] at equal
  · by_cases leftOne : leftCount = 1
    · subst leftCount
      by_cases rightZero : rightCount = 0
      · subst rightCount
        simp [multiplicityCode] at equal
      · by_cases rightOne : rightCount = 1
        · subst rightCount
          rfl
        · simp [multiplicityCode, rightZero, rightOne] at equal
    · by_cases rightZero : rightCount = 0
      · subst rightCount
        simp [multiplicityCode, leftZero, leftOne] at equal
      · by_cases rightOne : rightCount = 1
        · subst rightCount
          simp [multiplicityCode, leftZero, leftOne] at equal
        · simp only [Nat.min_def]
          split <;> split <;> omega

/-- Direct S5_110 table valuations force cap-two multiplicity equality. -/
theorem s5_110_valid_cappedMultiplicity
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_110.table.semigroup)
    (letter : Nat) :
    S5_110Syntax.cappedMultiplicity identity.lhs letter =
      S5_110Syntax.cappedMultiplicity identity.rhs letter := by
  have evaluated := valid (multiplicityValuation letter)
  rw [s5_110_eval_multiplicity,
    s5_110_eval_multiplicity] at evaluated
  exact multiplicityCode_reflects_cap evaluated

private def pairSymbolValue : S5_110Syntax.PairSymbol → Fin 5
  | .other => 4
  | .x => 3
  | .y => 2

private def pairValuation (x y : Nat) : Nat → Fin 5 :=
  fun letter =>
    pairSymbolValue (S5_110Syntax.pairSymbol x y letter)

private def s5_110PairStateValue :
    S5_110Syntax.PairState → Fin 5
  | .empty => 4
  | .x1 => 3
  | .x2 => 0
  | .y1 => 2
  | .y2 => 0
  | .xy => 1
  | .yx | .x1y2 | .x2y1 | .x2y2 => 0

private theorem s5_110_pairStep_value
    (state : S5_110Syntax.PairState)
    (symbol : S5_110Syntax.PairSymbol) :
    Generated.Catalogue.S5_110.table.mul
        (s5_110PairStateValue state) (pairSymbolValue symbol) =
      s5_110PairStateValue (S5_110Syntax.pairStep state symbol) := by
  cases state <;> cases symbol <;> decide

private theorem pairStep_xCount
    (state : S5_110Syntax.PairState)
    (symbol : S5_110Syntax.PairSymbol) :
    (S5_110Syntax.pairStep state symbol).xCount =
      Nat.min 2
        (state.xCount + if symbol = .x then 1 else 0) := by
  cases state <;> cases symbol <;> decide

private theorem pairStep_yCount
    (state : S5_110Syntax.PairState)
    (symbol : S5_110Syntax.PairSymbol) :
    (S5_110Syntax.pairStep state symbol).yCount =
      Nat.min 2
        (state.yCount + if symbol = .y then 1 else 0) := by
  cases state <;> cases symbol <;> decide

private theorem pairState_xCount_le_two
    (state : S5_110Syntax.PairState) :
    state.xCount ≤ 2 := by
  cases state <;> decide

private theorem pairState_yCount_le_two
    (state : S5_110Syntax.PairState) :
    state.yCount ≤ 2 := by
  cases state <;> decide

private theorem cap_two_cap_add (left right : Nat) :
    Nat.min 2 (Nat.min 2 left + right) =
      Nat.min 2 (left + right) := by
  by_cases capped : 2 ≤ left
  · have inner : Nat.min 2 left = 2 :=
      Nat.min_eq_left capped
    calc
      Nat.min 2 (Nat.min 2 left + right) =
          Nat.min 2 (2 + right) := by rw [inner]
      _ = 2 := Nat.min_eq_left (by omega)
      _ = Nat.min 2 (left + right) :=
        (Nat.min_eq_left (by omega)).symm
  · have below : left ≤ 2 := by omega
    have inner : Nat.min 2 left = left :=
      Nat.min_eq_right below
    rw [inner]

private theorem pairFold_xCount (x y : Nat) :
    ∀ (letters : List Nat) (initial : S5_110Syntax.PairState),
      (letters.foldl
          (fun state letter =>
            S5_110Syntax.pairStep state
              (S5_110Syntax.pairSymbol x y letter))
          initial).xCount =
        Nat.min 2 (initial.xCount + letters.count x)
  | [], initial => by
      simpa using
        (Nat.min_eq_right (pairState_xCount_le_two initial)).symm
  | letter :: rest, initial => by
      simp only [List.foldl_cons]
      rw [pairFold_xCount x y rest]
      rw [pairStep_xCount]
      by_cases equal : letter = x
      · subst letter
        simp only [S5_110Syntax.pairSymbol, if_pos,
          List.count_cons_self]
        rw [cap_two_cap_add]
        congr 1
        omega
      · have symbolNotX :
            S5_110Syntax.pairSymbol x y letter ≠ .x := by
          unfold S5_110Syntax.pairSymbol
          rw [if_neg equal]
          split <;> decide
        rw [if_neg symbolNotX]
        rw [cap_two_cap_add]
        simp [equal]

private theorem pairFold_yCount (x y : Nat) (different : x ≠ y) :
    ∀ (letters : List Nat) (initial : S5_110Syntax.PairState),
      (letters.foldl
          (fun state letter =>
            S5_110Syntax.pairStep state
              (S5_110Syntax.pairSymbol x y letter))
          initial).yCount =
        Nat.min 2 (initial.yCount + letters.count y)
  | [], initial => by
      simpa using
        (Nat.min_eq_right (pairState_yCount_le_two initial)).symm
  | letter :: rest, initial => by
      simp only [List.foldl_cons]
      rw [pairFold_yCount x y different rest]
      rw [pairStep_yCount]
      by_cases isY : letter = y
      · subst letter
        have notX : y ≠ x := Ne.symm different
        simp only [S5_110Syntax.pairSymbol, if_neg notX, if_pos,
          List.count_cons_self]
        rw [cap_two_cap_add]
        congr 1
        omega
      · have symbolNotY :
            S5_110Syntax.pairSymbol x y letter ≠ .y := by
          unfold S5_110Syntax.pairSymbol
          split <;> decide
        rw [if_neg symbolNotY]
        rw [cap_two_cap_add]
        simp [isY]

private theorem s5_110_pairFold_value (x y : Nat) :
    ∀ (letters : List Nat) (initial : S5_110Syntax.PairState),
      letters.foldl
          (fun value letter =>
            Generated.Catalogue.S5_110.table.mul value
              (pairValuation x y letter))
          (s5_110PairStateValue initial) =
        s5_110PairStateValue
          (letters.foldl
            (fun state letter =>
              S5_110Syntax.pairStep state
                (S5_110Syntax.pairSymbol x y letter))
            initial)
  | [], _ => rfl
  | letter :: rest, initial => by
      simp only [List.foldl_cons, pairValuation]
      rw [s5_110_pairStep_value]
      exact s5_110_pairFold_value x y rest
        (S5_110Syntax.pairStep initial
          (S5_110Syntax.pairSymbol x y letter))

private theorem pairScan_xCount
    (word : Word Nat) (x y : Nat) :
    (S5_110Syntax.pairScan word x y).xCount =
      S5_110Syntax.cappedMultiplicity word x := by
  unfold S5_110Syntax.pairScan S5_110Syntax.cappedMultiplicity
  simpa [S5_110Syntax.PairState.xCount] using
    pairFold_xCount x y word.toList .empty

private theorem pairScan_yCount
    (word : Word Nat) {x y : Nat} (different : x ≠ y) :
    (S5_110Syntax.pairScan word x y).yCount =
      S5_110Syntax.cappedMultiplicity word y := by
  unfold S5_110Syntax.pairScan S5_110Syntax.cappedMultiplicity
  simpa [S5_110Syntax.PairState.yCount] using
    pairFold_yCount x y different word.toList .empty

private theorem s5_110_eval_pair
    (word : Word Nat) (x y : Nat) :
    Generated.Catalogue.S5_110.table.semigroup.eval
        (pairValuation x y) word =
      s5_110PairStateValue
        (S5_110Syntax.pairScan word x y) := by
  rw [s5_110_eval_eq_listEval]
  unfold s5_110ListEval S5_110Syntax.pairScan
  simpa [s5_110PairStateValue] using
    s5_110_pairFold_value x y word.toList .empty

private theorem s5_110_state_eq_xy_of_counts_value
    (state : S5_110Syntax.PairState)
    (xCount : state.xCount = 1)
    (yCount : state.yCount = 1)
    (value : s5_110PairStateValue state = 1) :
    state = .xy := by
  cases state <;>
    simp_all [S5_110Syntax.PairState.xCount,
      S5_110Syntax.PairState.yCount, s5_110PairStateValue]

private theorem s5_110_simplePrecedes_forward
    {left right : Word Nat} {x y : Nat}
    (equalEval :
      s5_110PairStateValue (S5_110Syntax.pairScan left x y) =
        s5_110PairStateValue (S5_110Syntax.pairScan right x y))
    (capped :
      ∀ letter,
        S5_110Syntax.cappedMultiplicity left letter =
          S5_110Syntax.cappedMultiplicity right letter)
    (precedes : S5_110Syntax.SimplePrecedes left x y) :
    S5_110Syntax.SimplePrecedes right x y := by
  rcases precedes with ⟨different, leftState⟩
  refine ⟨different, ?_⟩
  have rightXCount :
      (S5_110Syntax.pairScan right x y).xCount = 1 := by
    calc
      _ = S5_110Syntax.cappedMultiplicity right x :=
        pairScan_xCount right x y
      _ = S5_110Syntax.cappedMultiplicity left x :=
        (capped x).symm
      _ = (S5_110Syntax.pairScan left x y).xCount :=
        (pairScan_xCount left x y).symm
      _ = 1 := by rw [leftState]; rfl
  have rightYCount :
      (S5_110Syntax.pairScan right x y).yCount = 1 := by
    calc
      _ = S5_110Syntax.cappedMultiplicity right y :=
        pairScan_yCount right different
      _ = S5_110Syntax.cappedMultiplicity left y :=
        (capped y).symm
      _ = (S5_110Syntax.pairScan left x y).yCount :=
        (pairScan_yCount left different).symm
      _ = 1 := by rw [leftState]; rfl
  have rightValue :
      s5_110PairStateValue
          (S5_110Syntax.pairScan right x y) = 1 := by
    rw [← equalEval, leftState]
    rfl
  exact s5_110_state_eq_xy_of_counts_value
    (S5_110Syntax.pairScan right x y)
    rightXCount rightYCount rightValue

/-- Direct pair valuations force preservation of singleton precedence. -/
theorem s5_110_valid_simplePrecedes
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_110.table.semigroup)
    (capped :
      ∀ letter,
        S5_110Syntax.cappedMultiplicity identity.lhs letter =
          S5_110Syntax.cappedMultiplicity identity.rhs letter)
    (x y : Nat) :
    S5_110Syntax.SimplePrecedes identity.lhs x y ↔
      S5_110Syntax.SimplePrecedes identity.rhs x y := by
  have evaluated := valid (pairValuation x y)
  rw [s5_110_eval_pair, s5_110_eval_pair] at evaluated
  constructor
  · exact s5_110_simplePrecedes_forward evaluated capped
  · exact s5_110_simplePrecedes_forward evaluated.symm
      (fun letter => (capped letter).symm)

theorem sameSignature_of_s5_110_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_110.table.semigroup) :
    S5_110Syntax.SameCappedSingletonSignature
      identity.lhs identity.rhs := by
  have capped :
      ∀ letter,
        S5_110Syntax.cappedMultiplicity identity.lhs letter =
          S5_110Syntax.cappedMultiplicity identity.rhs letter :=
    fun letter =>
      s5_110_valid_cappedMultiplicity identity valid letter
  exact
    ⟨capped, fun x y =>
      s5_110_valid_simplePrecedes identity valid capped x y⟩

end SemigroupBasis.CoRoots.S5_110Invariant

namespace SemigroupBasis.CoRoots.S5_110

open SemigroupBasis

/-- Every formal consequence of the S5_110 basis preserves the cap-two
multiplicity and ordered-singleton signature. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_110Syntax.SameCappedSingletonSignature left right := by
  exact S5_110Invariant.sameSignature_of_s5_110_valid
    ⟨left, right⟩
    (fun valuation => derivation.sound models valuation)

end SemigroupBasis.CoRoots.S5_110

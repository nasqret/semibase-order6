import SemigroupBasis.MatrixUnits
import SemigroupBasis.Nonfinite.GraphParity

namespace SemigroupBasis
namespace MatrixUnit

universe u v w

variable {α : Type u} {I : Type v} {J : Type w}

/-- A word has zero support when one of its variables is assigned the zero
matrix unit. -/
def SupportZero (valuation : α → MatrixUnit I) (word : Word α) : Prop :=
  ∃ letter, letter ∈ word.toList ∧ valuation letter = zero

/-- The endpoint constraint imposed by an adjacent pair of nonzero matrix
units. The predicate is vacuous when either value is zero. -/
def EdgeMatches (valuation : α → MatrixUnit I) (source target : α) : Prop :=
  ∀ i j k l,
    valuation source = ofIndices i j →
      valuation target = ofIndices k l → j = k

/-- A word has a failed edge when some adjacent pair of nonzero matrix units
has unequal inner coordinates. -/
def FailedEdge (valuation : α → MatrixUnit I) (word : Word α) : Prop :=
  ∃ source target,
    (source, target) ∈ word.adjacentPairs ∧
      ¬EdgeMatches valuation source target

theorem edgeMatches_iff_of_values
    (valuation : α → MatrixUnit I) (source target : α)
    (i j k l : I)
    (sourceValue : valuation source = ofIndices i j)
    (targetValue : valuation target = ofIndices k l) :
    EdgeMatches valuation source target ↔ j = k := by
  constructor
  · intro hMatches
    exact hMatches i j k l sourceValue targetValue
  · intro innerEqual i' j' k' l' sourceValue' targetValue'
    have sourceCoordinates : i = i' ∧ j = j' := by
      simpa only [ofIndices, Option.some.injEq, Prod.mk.injEq] using
        sourceValue.symm.trans sourceValue'
    have targetCoordinates : k = k' ∧ l = l' := by
      simpa only [ofIndices, Option.some.injEq, Prod.mk.injEq] using
        targetValue.symm.trans targetValue'
    exact sourceCoordinates.2.symm.trans
      (innerEqual.trans targetCoordinates.1)

theorem exists_values_of_not_edgeMatches
    (valuation : α → MatrixUnit I) (source target : α)
    (mismatch : ¬EdgeMatches valuation source target) :
    ∃ i j k l,
      valuation source = ofIndices i j ∧
        valuation target = ofIndices k l ∧ j ≠ k := by
  cases sourceValue : valuation source with
  | none =>
      exfalso
      apply mismatch
      intro i j k l sourceNonzero _
      simp [sourceValue, ofIndices] at sourceNonzero
  | some sourcePair =>
      rcases sourcePair with ⟨i, j⟩
      cases targetValue : valuation target with
      | none =>
          exfalso
          apply mismatch
          intro i' j' k l _ targetNonzero
          simp [targetValue, ofIndices] at targetNonzero
      | some targetPair =>
          rcases targetPair with ⟨k, l⟩
          have sourceOfIndices : valuation source = ofIndices i j := by
            simpa [ofIndices] using sourceValue
          have targetOfIndices : valuation target = ofIndices k l := by
            simpa [ofIndices] using targetValue
          refine ⟨i, j, k, l, by rfl, by rfl, ?_⟩
          intro innerEqual
          exact mismatch <|
            (edgeMatches_iff_of_values valuation source target
              i j k l sourceOfIndices targetOfIndices).2 innerEqual

private theorem head_mem_toList (word : Word α) :
    word.head ∈ word.toList := by
  cases word
  simp [Word.toList]

private theorem final_mem_toList (word : Word α) :
    word.final ∈ word.toList := by
  cases word with
  | mk head tail =>
      simpa [Word.final, Word.toList] using
        (List.getLastD_mem_cons (l := tail) (a := head))

private theorem exists_indices_of_not_support
    (valuation : α → MatrixUnit I) (word : Word α)
    (noSupport : ¬SupportZero valuation word)
    {letter : α} (member : letter ∈ word.toList) :
    ∃ row column, valuation letter = ofIndices row column := by
  cases value : valuation letter with
  | none =>
      exact False.elim <| noSupport ⟨letter, member, value⟩
  | some coordinates =>
      rcases coordinates with ⟨row, column⟩
      exact ⟨row, column, by rfl⟩

private theorem fold_zero [DecidableEq I]
    (valuation : α → MatrixUnit I) (letters : List α) :
    letters.foldl
        (fun current letter => mul current (valuation letter))
        zero = zero := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.foldl_cons, zero_mul]
      exact ih

private theorem fold_zero_of_support [DecidableEq I]
    (valuation : α → MatrixUnit I) (letters : List α)
    (initial : MatrixUnit I)
    (zeroMember :
      ∃ letter, letter ∈ letters ∧ valuation letter = zero) :
    letters.foldl
        (fun current letter => mul current (valuation letter))
        initial = zero := by
  induction letters generalizing initial with
  | nil =>
      rcases zeroMember with ⟨letter, member, _⟩
      simp at member
  | cons next rest ih =>
      rcases zeroMember with ⟨letter, member, zeroValue⟩
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp only [List.foldl_cons, zeroValue, mul_zero]
        exact fold_zero valuation rest
      · simp only [List.foldl_cons]
        exact ih (mul initial (valuation next))
          ⟨letter, member, zeroValue⟩

/-- A zero-valued variable forces the value of the whole word to zero. -/
theorem eval_zero_of_support [DecidableEq I]
    (valuation : α → MatrixUnit I) (word : Word α)
    (zeroSupport : SupportZero valuation word) :
    (semigroup (I := I)).eval valuation word = zero := by
  cases word with
  | mk head tail =>
      rcases zeroSupport with ⟨letter, member, zeroValue⟩
      simp only [Word.toList, List.mem_cons] at member
      rcases member with rfl | member
      · simp only [Semigroup.eval, zeroValue]
        exact fold_zero valuation tail
      · exact fold_zero_of_support valuation tail (valuation head)
          ⟨letter, member, zeroValue⟩

private theorem fold_of_matches [DecidableEq I]
    (valuation : α → MatrixUnit I) (initial : I)
    (previous : α) (previousRow previousColumn : I)
    (letters : List α) (finalRow finalColumn : I)
    (previousValue :
      valuation previous = ofIndices previousRow previousColumn)
    (finalValue :
      valuation (letters.getLastD previous) =
        ofIndices finalRow finalColumn)
    (lettersNonzero :
      ∀ letter, letter ∈ letters → valuation letter ≠ zero)
    (edgesMatch :
      ∀ source target,
        (source, target) ∈ Word.adjacentPairsFrom previous letters →
          EdgeMatches valuation source target) :
    letters.foldl
        (fun current letter => mul current (valuation letter))
        (ofIndices initial previousColumn) =
      ofIndices initial finalColumn := by
  induction letters generalizing previous previousRow previousColumn with
  | nil =>
      simp only [List.getLastD_nil] at finalValue
      have coordinates :
          previousRow = finalRow ∧ previousColumn = finalColumn := by
        simpa only [ofIndices, Option.some.injEq, Prod.mk.injEq] using
          previousValue.symm.trans finalValue
      simp only [List.foldl_nil]
      rw [coordinates.2]
  | cons next rest ih =>
      have nextNonzero := lettersNonzero next (by simp)
      cases nextValue : valuation next with
      | none =>
          exact False.elim <| nextNonzero (by simpa [zero] using nextValue)
      | some nextCoordinates =>
          rcases nextCoordinates with ⟨nextRow, nextColumn⟩
          have nextValueOfIndices :
              valuation next = ofIndices nextRow nextColumn := by
            simpa [ofIndices] using nextValue
          have firstMatches : EdgeMatches valuation previous next :=
            edgesMatch previous next (by simp [Word.adjacentPairsFrom])
          have innerEqual : previousColumn = nextRow :=
            (edgeMatches_iff_of_values valuation previous next
              previousRow previousColumn nextRow nextColumn
              previousValue nextValueOfIndices).1 firstMatches
          simp only [List.foldl_cons]
          rw [nextValueOfIndices]
          rw [ofIndices_mul_ofIndices_of_eq _ _ _ _ innerEqual]
          exact ih next nextRow nextColumn
            nextValueOfIndices
            (by simpa only [List.getLastD_cons] using finalValue)
            (by
              intro letter member
              exact lettersNonzero letter (by simp [member]))
            (by
              intro source target member
              exact edgesMatch source target (by
                simp only [Word.adjacentPairsFrom, List.mem_cons]
                exact Or.inr member))

private theorem fold_zero_of_failed [DecidableEq I]
    (valuation : α → MatrixUnit I) (initial : I)
    (previous : α) (previousRow previousColumn : I)
    (letters : List α)
    (previousValue :
      valuation previous = ofIndices previousRow previousColumn)
    (lettersNonzero :
      ∀ letter, letter ∈ letters → valuation letter ≠ zero)
    (failed :
      ∃ source target,
        (source, target) ∈ Word.adjacentPairsFrom previous letters ∧
          ¬EdgeMatches valuation source target) :
    letters.foldl
        (fun current letter => mul current (valuation letter))
        (ofIndices initial previousColumn) = zero := by
  induction letters generalizing previous previousRow previousColumn with
  | nil =>
      rcases failed with ⟨source, target, member, _⟩
      simp [Word.adjacentPairsFrom] at member
  | cons next rest ih =>
      have nextNonzero := lettersNonzero next (by simp)
      cases nextValue : valuation next with
      | none =>
          exact False.elim <| nextNonzero (by simpa [zero] using nextValue)
      | some nextCoordinates =>
            rcases nextCoordinates with ⟨nextRow, nextColumn⟩
            have nextValueOfIndices :
                valuation next = ofIndices nextRow nextColumn := by
              simpa [ofIndices] using nextValue
            simp only [List.foldl_cons]
            rw [nextValueOfIndices]
            by_cases innerEqual : previousColumn = nextRow
            · have firstMatches : EdgeMatches valuation previous next :=
                (edgeMatches_iff_of_values valuation previous next
                  previousRow previousColumn nextRow nextColumn
                  previousValue nextValueOfIndices).2 innerEqual
              change
                List.foldl (fun current letter => mul current (valuation letter))
                  (mul (ofIndices initial previousColumn)
                    (ofIndices nextRow nextColumn)) rest = zero
              rw [ofIndices_mul_ofIndices_of_eq _ _ _ _ innerEqual]
              exact ih next nextRow nextColumn
                nextValueOfIndices
                (by
                  intro letter member
                  exact lettersNonzero letter (by simp [member]))
                (by
                  rcases failed with ⟨source, target, member, mismatch⟩
                  simp only [Word.adjacentPairsFrom, List.mem_cons] at member
                  rcases member with first | later
                  · have sourceEq : source = previous := congrArg Prod.fst first
                    have targetEq : target = next := congrArg Prod.snd first
                    subst source
                    subst target
                    exact False.elim (mismatch firstMatches)
                  · exact ⟨source, target, later, mismatch⟩)
            · change
                List.foldl (fun current letter => mul current (valuation letter))
                  (mul (ofIndices initial previousColumn)
                    (ofIndices nextRow nextColumn)) rest = zero
              rw [ofIndices_mul_ofIndices_of_ne _ _ _ _ innerEqual]
              exact fold_zero valuation rest

/-- With no zero support and no failed edge, evaluation retains exactly the
initial row and final column of the word. -/
theorem eval_of_no_obstruction [DecidableEq I]
    (valuation : α → MatrixUnit I) (word : Word α)
    (initialRow initialColumn finalRow finalColumn : I)
    (initialValue :
      valuation word.head = ofIndices initialRow initialColumn)
    (finalValue :
      valuation word.final = ofIndices finalRow finalColumn)
    (noSupport : ¬SupportZero valuation word)
    (noFailedEdge : ¬FailedEdge valuation word) :
    (semigroup (I := I)).eval valuation word =
      ofIndices initialRow finalColumn := by
  cases word with
  | mk head tail =>
      have tailNonzero :
          ∀ letter, letter ∈ tail → valuation letter ≠ zero := by
        intro letter member zeroValue
        exact noSupport ⟨letter, by simp [Word.toList, member], zeroValue⟩
      have allEdgesMatch :
          ∀ source target,
            (source, target) ∈ Word.adjacentPairsFrom head tail →
              EdgeMatches valuation source target := by
        intro source target member
        have wordMember :
            (source, target) ∈ (Word.mk head tail).adjacentPairs := by
          simpa [Word.adjacentPairs] using member
        by_cases hMatches : EdgeMatches valuation source target
        · exact hMatches
        · exact False.elim <| noFailedEdge
            ⟨source, target, wordMember, hMatches⟩
      change
        tail.foldl
            (fun current letter => mul current (valuation letter))
            (valuation head) =
          ofIndices initialRow finalColumn
      rw [initialValue]
      exact fold_of_matches valuation initialRow head
        initialRow initialColumn tail finalRow finalColumn
        initialValue (by simpa only [Word.final] using finalValue)
        tailNonzero allEdgesMatch

/-- With no zero support, a failed adjacent edge forces evaluation to zero. -/
theorem eval_zero_of_failedEdge [DecidableEq I]
    (valuation : α → MatrixUnit I) (word : Word α)
    (noSupport : ¬SupportZero valuation word)
    (failedEdge : FailedEdge valuation word) :
    (semigroup (I := I)).eval valuation word = zero := by
  cases word with
  | mk head tail =>
      have headNonzero : valuation head ≠ zero := by
        intro zeroValue
        exact noSupport ⟨head, by simp [Word.toList], zeroValue⟩
      have tailNonzero :
          ∀ letter, letter ∈ tail → valuation letter ≠ zero := by
        intro letter member zeroValue
        exact noSupport ⟨letter, by simp [Word.toList, member], zeroValue⟩
      cases headValue : valuation head with
      | none =>
          exact False.elim <| headNonzero (by simpa [zero] using headValue)
      | some headCoordinates =>
          rcases headCoordinates with ⟨headRow, headColumn⟩
          rcases failedEdge with ⟨source, target, member, mismatch⟩
          change
            tail.foldl
                (fun current letter => mul current (valuation letter))
                (valuation head) = zero
          rw [headValue]
          exact fold_zero_of_failed valuation headRow head
            headRow headColumn tail headValue tailNonzero
            ⟨source, target, by
              simpa [Word.adjacentPairs] using member, mismatch⟩

/-- The two obstruction predicates are an exact zero criterion. -/
theorem eval_eq_zero_iff [DecidableEq I]
    (valuation : α → MatrixUnit I) (word : Word α) :
    (semigroup (I := I)).eval valuation word = zero ↔
      SupportZero valuation word ∨ FailedEdge valuation word := by
  classical
  constructor
  · intro evaluatesToZero
    by_cases zeroSupport : SupportZero valuation word
    · exact Or.inl zeroSupport
    · by_cases failedEdge : FailedEdge valuation word
      · exact Or.inr failedEdge
      · rcases exists_indices_of_not_support valuation word zeroSupport
            (head_mem_toList word) with
          ⟨initialRow, initialColumn, initialValue⟩
        rcases exists_indices_of_not_support valuation word zeroSupport
            (final_mem_toList word) with
          ⟨finalRow, finalColumn, finalValue⟩
        have nonzeroEvaluation :=
          eval_of_no_obstruction valuation word
            initialRow initialColumn finalRow finalColumn
            initialValue finalValue zeroSupport failedEdge
        have impossible : ofIndices initialRow finalColumn = (zero : MatrixUnit I) :=
          nonzeroEvaluation.symm.trans evaluatesToZero
        simp [ofIndices, zero] at impossible
  · rintro (zeroSupport | failedEdge)
    · exact eval_zero_of_support valuation word zeroSupport
    · by_cases zeroSupport : SupportZero valuation word
      · exact eval_zero_of_support valuation word zeroSupport
      · exact eval_zero_of_failedEdge valuation word zeroSupport failedEdge

theorem eval_ne_zero_of_no_obstruction [DecidableEq I]
    (valuation : α → MatrixUnit I) (word : Word α)
    (noSupport : ¬SupportZero valuation word)
    (noFailedEdge : ¬FailedEdge valuation word) :
    (semigroup (I := I)).eval valuation word ≠ zero := by
  intro evaluatesToZero
  rcases (eval_eq_zero_iff valuation word).1 evaluatesToZero with
    zeroSupport | failedEdge
  · exact noSupport zeroSupport
  · exact noFailedEdge failedEdge

/-- Apply the same coordinate map to both endpoints of every nonzero value. -/
def recolor (color : I → J) (valuation : α → MatrixUnit I) :
    α → MatrixUnit J :=
  fun letter =>
    match valuation letter with
    | none => none
    | some (row, column) => ofIndices (color row) (color column)

@[simp]
theorem recolor_of_zero
    (color : I → J) (valuation : α → MatrixUnit I) (letter : α)
    (value : valuation letter = zero) :
    recolor color valuation letter = zero := by
  simp [recolor, value, zero]

@[simp]
theorem recolor_of_indices
    (color : I → J) (valuation : α → MatrixUnit I) (letter : α)
    (row column : I)
    (value : valuation letter = ofIndices row column) :
    recolor color valuation letter =
      ofIndices (color row) (color column) := by
  simp [recolor, value, ofIndices]

@[simp]
theorem recolor_eq_zero_iff
    (color : I → J) (valuation : α → MatrixUnit I) (letter : α) :
    recolor color valuation letter = zero ↔ valuation letter = zero := by
  cases value : valuation letter with
  | none => simp [recolor, value, zero]
  | some coordinates => simp [recolor, value, zero, ofIndices]

theorem supportZero_recolor_iff
    (color : I → J) (valuation : α → MatrixUnit I) (word : Word α) :
    SupportZero (recolor color valuation) word ↔
      SupportZero valuation word := by
  constructor
  · rintro ⟨letter, member, zeroValue⟩
    exact ⟨letter, member,
      (recolor_eq_zero_iff color valuation letter).1 zeroValue⟩
  · rintro ⟨letter, member, zeroValue⟩
    exact ⟨letter, member,
      (recolor_eq_zero_iff color valuation letter).2 zeroValue⟩

theorem edgeMatches_recolor
    (color : I → J) (valuation : α → MatrixUnit I)
    (source target : α)
    (hMatches : EdgeMatches valuation source target) :
    EdgeMatches (recolor color valuation) source target := by
  cases sourceValue : valuation source with
  | none =>
      intro i j k l sourceNonzero _
      simp [recolor, sourceValue, ofIndices] at sourceNonzero
  | some sourceCoordinates =>
      rcases sourceCoordinates with ⟨sourceRow, sourceColumn⟩
      cases targetValue : valuation target with
      | none =>
          intro i j k l _ targetNonzero
          simp [recolor, targetValue, ofIndices] at targetNonzero
      | some targetCoordinates =>
          rcases targetCoordinates with ⟨targetRow, targetColumn⟩
          intro i j k l sourceRecolored targetRecolored
          have sourceCoordinates :
              color sourceRow = i ∧ color sourceColumn = j := by
            simpa only [ofIndices, Option.some.injEq, Prod.mk.injEq] using
              (recolor_of_indices color valuation source
                sourceRow sourceColumn sourceValue).symm.trans
                sourceRecolored
          have targetCoordinates :
              color targetRow = k ∧ color targetColumn = l := by
            simpa only [ofIndices, Option.some.injEq, Prod.mk.injEq] using
              (recolor_of_indices color valuation target
                targetRow targetColumn targetValue).symm.trans
                targetRecolored
          have innerEqual : sourceColumn = targetRow :=
            hMatches sourceRow sourceColumn targetRow targetColumn
              sourceValue targetValue
          exact sourceCoordinates.2.symm.trans
            ((congrArg color innerEqual).trans targetCoordinates.1)

theorem not_failedEdge_recolor
    (color : I → J) (valuation : α → MatrixUnit I) (word : Word α)
    (noFailedEdge : ¬FailedEdge valuation word) :
    ¬FailedEdge (recolor color valuation) word := by
  rintro ⟨source, target, member, mismatch⟩
  apply noFailedEdge
  refine ⟨source, target, member, ?_⟩
  intro originalMatches
  exact mismatch <|
    edgeMatches_recolor color valuation source target originalMatches

theorem failedEdge_recolor_of_values
    (color : I → J) (valuation : α → MatrixUnit I) (word : Word α)
    (source target : α) (i j k l : I)
    (member : (source, target) ∈ word.adjacentPairs)
    (sourceValue : valuation source = ofIndices i j)
    (targetValue : valuation target = ofIndices k l)
    (coloredMismatch : color j ≠ color k) :
    FailedEdge (recolor color valuation) word := by
  refine ⟨source, target, member, ?_⟩
  intro hMatches
  exact coloredMismatch <|
    hMatches (color i) (color j) (color k) (color l)
      (recolor_of_indices color valuation source i j sourceValue)
      (recolor_of_indices color valuation target k l targetValue)

private theorem not_failedEdge_recolor_constant
    (value : J) (valuation : α → MatrixUnit I) (word : Word α) :
    ¬FailedEdge (recolor (fun _ => value) valuation) word := by
  rintro ⟨source, target, _, mismatch⟩
  apply mismatch
  cases sourceValue : valuation source with
  | none =>
      intro i j k l sourceNonzero _
      simp [recolor, sourceValue, ofIndices] at sourceNonzero
  | some sourceCoordinates =>
      rcases sourceCoordinates with ⟨sourceRow, sourceColumn⟩
      cases targetValue : valuation target with
      | none =>
          intro i j k l _ targetNonzero
          simp [recolor, targetValue, ofIndices] at targetNonzero
      | some targetCoordinates =>
          rcases targetCoordinates with ⟨targetRow, targetColumn⟩
          intro i j k l sourceRecolored targetRecolored
          have sourceCoordinates : value = i ∧ value = j := by
            simpa only [ofIndices, Option.some.injEq, Prod.mk.injEq] using
              (recolor_of_indices (fun _ : I => value) valuation source
                sourceRow sourceColumn sourceValue).symm.trans
                sourceRecolored
          have targetCoordinates : value = k ∧ value = l := by
            simpa only [ofIndices, Option.some.injEq, Prod.mk.injEq] using
              (recolor_of_indices (fun _ : I => value) valuation target
                targetRow targetColumn targetValue).symm.trans
                targetRecolored
          exact sourceCoordinates.2.symm.trans targetCoordinates.1

private theorem eval_constantFinTwo_of_noSupport [DecidableEq I]
    (valuation : α → MatrixUnit I) (word : Word α)
    (noSupport : ¬SupportZero valuation word) :
    (semigroup (I := Fin 2)).eval
        (recolor (fun _ : I => (0 : Fin 2)) valuation) word =
      ofIndices 0 0 := by
  rcases exists_indices_of_not_support valuation word noSupport
      (head_mem_toList word) with
    ⟨initialRow, initialColumn, initialValue⟩
  rcases exists_indices_of_not_support valuation word noSupport
      (final_mem_toList word) with
    ⟨finalRow, finalColumn, finalValue⟩
  exact eval_of_no_obstruction
    (recolor (fun _ : I => (0 : Fin 2)) valuation) word
    0 0 0 0
    (recolor_of_indices (fun _ : I => (0 : Fin 2)) valuation
      word.head initialRow initialColumn initialValue)
    (recolor_of_indices (fun _ : I => (0 : Fin 2)) valuation
      word.final finalRow finalColumn finalValue)
    (by
      intro support
      exact noSupport <|
        (supportZero_recolor_iff
          (fun _ : I => (0 : Fin 2)) valuation word).1 support)
    (not_failedEdge_recolor_constant 0 valuation word)

theorem eval_recolor_of_no_obstruction
    [DecidableEq I] [DecidableEq J]
    (color : I → J) (valuation : α → MatrixUnit I) (word : Word α)
    (initialRow initialColumn finalRow finalColumn : I)
    (initialValue :
      valuation word.head = ofIndices initialRow initialColumn)
    (finalValue :
      valuation word.final = ofIndices finalRow finalColumn)
    (noSupport : ¬SupportZero valuation word)
    (noFailedEdge : ¬FailedEdge valuation word) :
    (semigroup (I := J)).eval (recolor color valuation) word =
      ofIndices (color initialRow) (color finalColumn) := by
  exact eval_of_no_obstruction (recolor color valuation) word
    (color initialRow) (color initialColumn)
    (color finalRow) (color finalColumn)
    (recolor_of_indices color valuation word.head
      initialRow initialColumn initialValue)
    (recolor_of_indices color valuation word.final
      finalRow finalColumn finalValue)
    (by
      intro support
      exact noSupport <|
        (supportZero_recolor_iff color valuation word).1 support)
    (not_failedEdge_recolor color valuation word noFailedEdge)

/-- Color one distinguished coordinate `0` and every other coordinate `1`. -/
def twoColor [DecidableEq I] (anchor : I) (coordinate : I) : Fin 2 :=
  if coordinate = anchor then 0 else 1

theorem twoColor_distinguishes [DecidableEq I]
    {left right : I} (different : left ≠ right) :
    twoColor left left ≠ twoColor left right := by
  simp [twoColor, Ne.symm different]

/-- Every failed matrix-unit identity over an arbitrary index type already
fails after a two-color recoloring. The three branches respectively isolate a
zero-support difference, a failed-edge difference, and unequal exposed
endpoints. -/
theorem exists_finTwo_failure_of_failure [DecidableEq I]
    (identity : Identity α) (valuation : α → MatrixUnit I)
    (failure :
      (semigroup (I := I)).eval valuation identity.lhs ≠
        (semigroup (I := I)).eval valuation identity.rhs) :
    ∃ finTwoValuation : α → MatrixUnit (Fin 2),
      (semigroup (I := Fin 2)).eval finTwoValuation identity.lhs ≠
        (semigroup (I := Fin 2)).eval finTwoValuation identity.rhs := by
  classical
  by_cases leftSupport : SupportZero valuation identity.lhs
  · by_cases rightSupport : SupportZero valuation identity.rhs
    · exact False.elim <| failure <|
        (eval_zero_of_support valuation identity.lhs leftSupport).trans
          (eval_zero_of_support valuation identity.rhs rightSupport).symm
    · let collapsed :=
        recolor (fun _ : I => (0 : Fin 2)) valuation
      refine ⟨collapsed, ?_⟩
      have leftZero :
          (semigroup (I := Fin 2)).eval collapsed identity.lhs = zero :=
        eval_zero_of_support collapsed identity.lhs <|
          (supportZero_recolor_iff
            (fun _ : I => (0 : Fin 2)) valuation identity.lhs).2
            leftSupport
      have rightNonzero :
          (semigroup (I := Fin 2)).eval collapsed identity.rhs =
            ofIndices 0 0 :=
        eval_constantFinTwo_of_noSupport valuation identity.rhs rightSupport
      rw [leftZero, rightNonzero]
      simp [zero, ofIndices]
  · by_cases rightSupport : SupportZero valuation identity.rhs
    · let collapsed :=
        recolor (fun _ : I => (0 : Fin 2)) valuation
      refine ⟨collapsed, ?_⟩
      have leftNonzero :
          (semigroup (I := Fin 2)).eval collapsed identity.lhs =
            ofIndices 0 0 :=
        eval_constantFinTwo_of_noSupport valuation identity.lhs leftSupport
      have rightZero :
          (semigroup (I := Fin 2)).eval collapsed identity.rhs = zero :=
        eval_zero_of_support collapsed identity.rhs <|
          (supportZero_recolor_iff
            (fun _ : I => (0 : Fin 2)) valuation identity.rhs).2
            rightSupport
      rw [leftNonzero, rightZero]
      simp [zero, ofIndices]
    · by_cases leftFailed : FailedEdge valuation identity.lhs
      · by_cases rightFailed : FailedEdge valuation identity.rhs
        · exact False.elim <| failure <|
            (eval_zero_of_failedEdge valuation identity.lhs
              leftSupport leftFailed).trans
              (eval_zero_of_failedEdge valuation identity.rhs
                rightSupport rightFailed).symm
        · rcases leftFailed with ⟨source, target, member, mismatch⟩
          rcases exists_values_of_not_edgeMatches valuation source target
              mismatch with
            ⟨i, j, k, l, sourceValue, targetValue, innerDifferent⟩
          let color := twoColor j
          let colored := recolor color valuation
          have coloredMismatch : color j ≠ color k := by
            exact twoColor_distinguishes innerDifferent
          have leftFailedColored : FailedEdge colored identity.lhs :=
            failedEdge_recolor_of_values color valuation identity.lhs
              source target i j k l member sourceValue targetValue
              coloredMismatch
          have rightGoodColored : ¬FailedEdge colored identity.rhs :=
            not_failedEdge_recolor color valuation identity.rhs rightFailed
          have leftSupportGood : ¬SupportZero colored identity.lhs := by
            intro support
            exact leftSupport <|
              (supportZero_recolor_iff color valuation identity.lhs).1 support
          have rightSupportGood : ¬SupportZero colored identity.rhs := by
            intro support
            exact rightSupport <|
              (supportZero_recolor_iff color valuation identity.rhs).1 support
          have leftZero :=
            eval_zero_of_failedEdge colored identity.lhs
              leftSupportGood leftFailedColored
          have rightNonzero :=
            eval_ne_zero_of_no_obstruction colored identity.rhs
              rightSupportGood rightGoodColored
          refine ⟨colored, ?_⟩
          intro equality
          exact rightNonzero (equality.symm.trans leftZero)
      · by_cases rightFailed : FailedEdge valuation identity.rhs
        · rcases rightFailed with ⟨source, target, member, mismatch⟩
          rcases exists_values_of_not_edgeMatches valuation source target
              mismatch with
            ⟨i, j, k, l, sourceValue, targetValue, innerDifferent⟩
          let color := twoColor j
          let colored := recolor color valuation
          have coloredMismatch : color j ≠ color k := by
            exact twoColor_distinguishes innerDifferent
          have leftGoodColored : ¬FailedEdge colored identity.lhs :=
            not_failedEdge_recolor color valuation identity.lhs leftFailed
          have rightFailedColored : FailedEdge colored identity.rhs :=
            failedEdge_recolor_of_values color valuation identity.rhs
              source target i j k l member sourceValue targetValue
              coloredMismatch
          have leftSupportGood : ¬SupportZero colored identity.lhs := by
            intro support
            exact leftSupport <|
              (supportZero_recolor_iff color valuation identity.lhs).1 support
          have rightSupportGood : ¬SupportZero colored identity.rhs := by
            intro support
            exact rightSupport <|
              (supportZero_recolor_iff color valuation identity.rhs).1 support
          have leftNonzero :=
            eval_ne_zero_of_no_obstruction colored identity.lhs
              leftSupportGood leftGoodColored
          have rightZero :=
            eval_zero_of_failedEdge colored identity.rhs
              rightSupportGood rightFailedColored
          refine ⟨colored, ?_⟩
          intro equality
          exact leftNonzero (equality.trans rightZero)
        · rcases exists_indices_of_not_support valuation identity.lhs
              leftSupport (head_mem_toList identity.lhs) with
            ⟨leftInitial, leftInitialColumn, leftInitialValue⟩
          rcases exists_indices_of_not_support valuation identity.lhs
              leftSupport (final_mem_toList identity.lhs) with
            ⟨leftFinalRow, leftFinal, leftFinalValue⟩
          rcases exists_indices_of_not_support valuation identity.rhs
              rightSupport (head_mem_toList identity.rhs) with
            ⟨rightInitial, rightInitialColumn, rightInitialValue⟩
          rcases exists_indices_of_not_support valuation identity.rhs
              rightSupport (final_mem_toList identity.rhs) with
            ⟨rightFinalRow, rightFinal, rightFinalValue⟩
          have endpointDifferent :
              ofIndices leftInitial leftFinal ≠
                ofIndices rightInitial rightFinal := by
            intro endpointEqual
            apply failure
            exact
              (eval_of_no_obstruction valuation identity.lhs
                leftInitial leftInitialColumn leftFinalRow leftFinal
                leftInitialValue leftFinalValue leftSupport leftFailed).trans
                (endpointEqual.trans <|
                  (eval_of_no_obstruction valuation identity.rhs
                    rightInitial rightInitialColumn rightFinalRow rightFinal
                    rightInitialValue rightFinalValue rightSupport
                    rightFailed).symm)
          by_cases initialEqual : leftInitial = rightInitial
          · have finalDifferent : leftFinal ≠ rightFinal := by
              intro finalEqual
              apply endpointDifferent
              simp only [ofIndices, Option.some.injEq, Prod.mk.injEq]
              exact ⟨initialEqual, finalEqual⟩
            let color := twoColor leftFinal
            let colored := recolor color valuation
            have coloredFinalDifferent :
                color leftFinal ≠ color rightFinal :=
              twoColor_distinguishes finalDifferent
            have leftEval :=
              eval_recolor_of_no_obstruction color valuation identity.lhs
                leftInitial leftInitialColumn leftFinalRow leftFinal
                leftInitialValue leftFinalValue leftSupport leftFailed
            have rightEval :=
              eval_recolor_of_no_obstruction color valuation identity.rhs
                rightInitial rightInitialColumn rightFinalRow rightFinal
                rightInitialValue rightFinalValue rightSupport rightFailed
            refine ⟨colored, ?_⟩
            rw [leftEval, rightEval]
            intro valuesEqual
            have coordinates :
                color leftInitial = color rightInitial ∧
                  color leftFinal = color rightFinal := by
              simpa only [ofIndices, Option.some.injEq, Prod.mk.injEq] using
                valuesEqual
            exact coloredFinalDifferent coordinates.2
          · let color := twoColor leftInitial
            let colored := recolor color valuation
            have coloredInitialDifferent :
                color leftInitial ≠ color rightInitial :=
              twoColor_distinguishes initialEqual
            have leftEval :=
              eval_recolor_of_no_obstruction color valuation identity.lhs
                leftInitial leftInitialColumn leftFinalRow leftFinal
                leftInitialValue leftFinalValue leftSupport leftFailed
            have rightEval :=
              eval_recolor_of_no_obstruction color valuation identity.rhs
                rightInitial rightInitialColumn rightFinalRow rightFinal
                rightInitialValue rightFinalValue rightSupport rightFailed
            refine ⟨colored, ?_⟩
            rw [leftEval, rightEval]
            intro valuesEqual
            have coordinates :
                color leftInitial = color rightInitial ∧
                  color leftFinal = color rightFinal := by
              simpa only [ofIndices, Option.some.injEq, Prod.mk.injEq] using
                valuesEqual
            exact coloredInitialDifferent coordinates.1

/-- Semantic direction for the B2 separation route: every identity of the
five-element matrix-unit semigroup is an identity of the matrix-unit semigroup
over any decidable index type. -/
theorem satisfiedBy_of_finTwo [DecidableEq I]
    (identity : Identity α)
    (valid : identity.SatisfiedBy (semigroup (I := Fin 2))) :
    identity.SatisfiedBy (semigroup (I := I)) := by
  intro valuation
  by_cases equality :
      (semigroup (I := I)).eval valuation identity.lhs =
        (semigroup (I := I)).eval valuation identity.rhs
  · exact equality
  · rcases exists_finTwo_failure_of_failure identity valuation equality with
      ⟨finTwoValuation, reflectedFailure⟩
    exact False.elim <| reflectedFailure (valid finTwoValuation)

end MatrixUnit
end SemigroupBasis

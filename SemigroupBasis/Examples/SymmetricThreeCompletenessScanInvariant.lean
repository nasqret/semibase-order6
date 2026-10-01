import SemigroupBasis.Examples.SymmetricThreeCompletenessInvariant
import SemigroupBasis.Examples.SymmetricThreeCompletenessParityScan

namespace SemigroupBasis.Examples.SymmetricThreeCompleteness

open SemigroupBasis

private theorem finTwo_add_assoc (first second third : Fin 2) :
    (first + second) + third = first + (second + third) := by
  decide +revert

private theorem finTwo_add_left_comm (first second third : Fin 2) :
    first + (second + third) = second + (first + third) := by
  decide +revert

private theorem finTwo_self_cancel (value suffix : Fin 2) :
    value + (value + suffix) = suffix := by
  decide +revert

private theorem finTwo_add_zero (value : Fin 2) : value + 0 = value := by
  decide +revert

private theorem finTwo_zero_add (value : Fin 2) : 0 + value = value := by
  decide +revert

private theorem finTwo_val_add (first second : Fin 2) :
    (first + second).val = (first.val + second.val) % 2 := by
  decide +revert

private theorem finThree_add_assoc (first second third : Fin 3) :
    (first + second) + third = first + (second + third) := by
  decide +revert

private theorem finThree_add_zero (value : Fin 3) : value + 0 = value := by
  decide +revert

private theorem finThree_zero_add (value : Fin 3) : 0 + value = value := by
  decide +revert

/-- Sum of the chosen reflection bits over a parity state. -/
def reflectionSum (reflection : Nat → Fin 2) : List Nat → Fin 2
  | [] => 0
  | letter :: rest => reflection letter + reflectionSum reflection rest

@[simp]
theorem reflectionSum_nil (reflection : Nat → Fin 2) :
    reflectionSum reflection [] = 0 :=
  rfl

@[simp]
theorem reflectionSum_cons (reflection : Nat → Fin 2)
    (letter : Nat) (rest : List Nat) :
    reflectionSum reflection (letter :: rest) =
      reflection letter + reflectionSum reflection rest :=
  rfl

theorem reflectionSum_append (reflection : Nat → Fin 2)
    (left right : List Nat) :
    reflectionSum reflection (left ++ right) =
      reflectionSum reflection left + reflectionSum reflection right := by
  induction left with
  | nil =>
      simp only [List.nil_append, reflectionSum_nil]
      exact (finTwo_zero_add _).symm
  | cons letter rest inductionHypothesis =>
      simp only [List.cons_append, reflectionSum_cons, inductionHypothesis]
      exact (finTwo_add_assoc _ _ _).symm

theorem reflectionSum_perm (reflection : Nat → Fin 2)
    {left right : List Nat} (permutation : left.Perm right) :
    reflectionSum reflection left = reflectionSum reflection right := by
  induction permutation with
  | nil => rfl
  | cons letter _ inductionHypothesis =>
      simp only [reflectionSum_cons, inductionHypothesis]
  | swap first second rest =>
      simp only [reflectionSum_cons]
      exact finTwo_add_left_comm _ _ _
  | trans _ _ first second => exact first.trans second

theorem reflectionSum_parityReduce (reflection : Nat → Fin 2) :
    ∀ letters : List Nat,
      reflectionSum reflection (parityReduce letters) =
        reflectionSum reflection letters
  | [] => rfl
  | letter :: rest => by
      simp only [parityReduce, reflectionSum_cons]
      by_cases member : letter ∈ parityReduce rest
      · rw [if_pos member, ← reflectionSum_parityReduce reflection rest]
        have separated := reflectionSum_perm reflection
          (List.perm_cons_erase member)
        calc
          reflectionSum reflection ((parityReduce rest).erase letter) =
              reflection letter +
                (reflection letter +
                  reflectionSum reflection
                    ((parityReduce rest).erase letter)) := by
            exact (finTwo_self_cancel _ _).symm
          _ = reflection letter +
                reflectionSum reflection (parityReduce rest) := by
            exact congrArg (fun value => reflection letter + value)
              separated.symm
      · rw [if_neg member, ← reflectionSum_parityReduce reflection rest]
        rfl

/-- Sorting and parity reduction preserve every reflection character. -/
theorem reflectionSum_canonicalParity (reflection : Nat → Fin 2)
    (letters : List Nat) :
    reflectionSum reflection (canonicalParity letters) =
      reflectionSum reflection letters := by
  calc
    reflectionSum reflection (canonicalParity letters) =
        reflectionSum reflection (parityReduce letters) :=
      (reflectionSum_perm reflection
        (parityReduce_perm_canonicalParity letters)).symm
    _ = reflectionSum reflection letters :=
      reflectionSum_parityReduce reflection letters

theorem reflectionSum_toggleState (reflection : Nat → Fin 2)
    (state : List Nat) (letter : Nat) :
    reflectionSum reflection (toggleState state letter) =
      reflectionSum reflection state + reflection letter := by
  unfold toggleState
  rw [reflectionSum_canonicalParity, reflectionSum_append]
  simp only [reflectionSum_cons, reflectionSum_nil, finTwo_add_zero]

/-- The character value in `Fin 3`: zero reflection gives `+1`, and one
reflection gives `-1 = 2`. -/
def walshSign (reflection : Fin 2) : Fin 3 :=
  if reflection = 0 then 1 else 2

/-- Signed contribution of one directed transition to the selected rotation
coordinate. -/
def keyContribution (tested : Nat) (reflection : Nat → Fin 2)
    (key : Word Nat) : Fin 3 :=
  if key.head = tested then walshSign (reflectionSum reflection key.tail)
  else 0

/-- Sum of all signed contributions in scan order. -/
def transitionCoefficient (tested : Nat) (reflection : Nat → Fin 2) :
    List (Word Nat) → Fin 3
  | [] => 0
  | key :: rest =>
      keyContribution tested reflection key +
        transitionCoefficient tested reflection rest

@[simp]
theorem transitionCoefficient_nil (tested : Nat)
    (reflection : Nat → Fin 2) :
    transitionCoefficient tested reflection [] = 0 :=
  rfl

@[simp]
theorem transitionCoefficient_cons (tested : Nat)
    (reflection : Nat → Fin 2) (key : Word Nat)
    (rest : List (Word Nat)) :
    transitionCoefficient tested reflection (key :: rest) =
      keyContribution tested reflection key +
        transitionCoefficient tested reflection rest :=
  rfl

theorem keyContribution_transitionKey (tested : Nat)
    (reflection : Nat → Fin 2) (state : List Nat) (letter : Nat) :
    keyContribution tested reflection (transitionKey state letter) =
      signedRotation (reflectionSum reflection state)
        (if letter = tested then 1 else 0) := by
  unfold keyContribution walshSign signedRotation
  simp only [transitionKey_head, transitionKey_tail]
  by_cases same : letter = tested
  · rw [if_pos same, if_pos same]
    by_cases zero : reflectionSum reflection state = 0
    · simp [zero]
    · simp [zero, negateRotation]
  · rw [if_neg same, if_neg same]
    by_cases zero : reflectionSum reflection state = 0
    · simp [zero]
    · simp [zero, negateRotation]

private theorem coordScan_rotation (tested : Nat)
    (reflection : Nat → Fin 2) :
    ∀ (state letters : List Nat) (current : Coord),
      current.reflection = reflectionSum reflection state →
      (letters.foldl
          (fun value letter =>
            coordMul value
              (Coord.mk (if letter = tested then 1 else 0)
                (reflection letter))) current).rotation =
        current.rotation +
          transitionCoefficient tested reflection
            (transitionKeysFrom state letters)
  | _, [], current, _ => by
      simp only [List.foldl_nil, transitionKeysFrom,
        transitionCoefficient_nil]
      exact (finThree_add_zero current.rotation).symm
  | state, letter :: rest, current, currentReflection => by
      let next := coordMul current
        (Coord.mk (if letter = tested then 1 else 0) (reflection letter))
      have nextReflection :
          next.reflection =
            reflectionSum reflection (toggleState state letter) := by
        change current.reflection + reflection letter =
          reflectionSum reflection (toggleState state letter)
        rw [currentReflection, reflectionSum_toggleState]
      simp only [List.foldl_cons, transitionKeysFrom,
        transitionCoefficient_cons]
      rw [coordScan_rotation tested reflection
        (toggleState state letter) rest next nextReflection]
      change
        (current.rotation +
            signedRotation current.reflection
              (if letter = tested then 1 else 0)) +
            transitionCoefficient tested reflection
              (transitionKeysFrom (toggleState state letter) rest) =
          current.rotation +
            (keyContribution tested reflection
                (transitionKey state letter) +
              transitionCoefficient tested reflection
                (transitionKeysFrom (toggleState state letter) rest))
      rw [currentReflection, ← keyContribution_transitionKey]
      exact finThree_add_assoc _ _ _

private theorem coordScan_reflection (reflection : Nat → Fin 2) :
    ∀ (letters : List Nat) (current : Coord),
      (letters.foldl
          (fun value letter =>
            coordMul value (Coord.mk 0 (reflection letter)))
          current).reflection =
        current.reflection + reflectionSum reflection letters
  | [], current => by
      simp only [List.foldl_nil, reflectionSum_nil]
      exact (finTwo_add_zero current.reflection).symm
  | letter :: rest, current => by
      simp only [List.foldl_cons, reflectionSum_cons]
      rw [coordScan_reflection reflection rest
        (coordMul current (Coord.mk 0 (reflection letter)))]
      change
        (current.reflection + reflection letter) +
            reflectionSum reflection rest =
          current.reflection +
            (reflection letter + reflectionSum reflection rest)
      exact finTwo_add_assoc _ _ _

theorem parityValue_eq_reflectionSum (reflection : Nat → Fin 2)
    (word : Word Nat) :
    parityValue reflection word =
      reflectionSum reflection word.toList := by
  unfold parityValue
  rw [coordEval_eq_evalList]
  unfold coordEvalList
  have scanned := coordScan_reflection reflection word.toList coordOne
  simpa only [coordOne, finTwo_zero_add] using scanned

def singletonReflection (tested : Nat) : Nat → Fin 2 :=
  fun letter => if letter = tested then 1 else 0

private theorem reflectionSum_singleton_val (tested : Nat) :
    ∀ letters : List Nat,
      (reflectionSum (singletonReflection tested) letters).val =
        letters.count tested % 2
  | [] => rfl
  | letter :: rest => by
      simp only [reflectionSum_cons, singletonReflection]
      by_cases same : letter = tested
      · subst letter
        rw [if_pos rfl, List.count_cons_self, finTwo_val_add,
          reflectionSum_singleton_val tested rest]
        omega
      · rw [if_neg same, List.count_cons_of_ne same, finTwo_val_add,
          reflectionSum_singleton_val tested rest]
        omega

theorem count_mod_two_eq_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy symmetricThree.semigroup)
    (tested : Nat) :
    identity.lhs.toList.count tested % 2 =
      identity.rhs.toList.count tested % 2 := by
  have parity := parityValue_eq_of_valid identity valid
    (singletonReflection tested)
  rw [parityValue_eq_reflectionSum,
    parityValue_eq_reflectionSum] at parity
  have values := congrArg Fin.val parity
  simpa only [reflectionSum_singleton_val] using values

theorem finalState_eq_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy symmetricThree.semigroup) :
    finalStateFrom [] identity.lhs.toList =
      finalStateFrom [] identity.rhs.toList := by
  rw [finalStateFrom_nil, finalStateFrom_nil]
  apply canonicalParity_eq_of_modCounts
  exact count_mod_two_eq_of_valid identity valid

/-- The S3 rotation coordinate is precisely the Walsh sum of the directed
transitions recorded by the parity scan. -/
theorem coefficientValue_eq_transitionCoefficient
    (tested : Nat) (reflection : Nat → Fin 2) (word : Word Nat) :
    coefficientValue tested reflection word =
      transitionCoefficient tested reflection
        (transitionKeysFrom [] word.toList) := by
  unfold coefficientValue
  rw [coordEval_eq_evalList]
  unfold coordEvalList
  have scanned := coordScan_rotation tested reflection [] word.toList
    coordOne rfl
  simpa only [coordOne, finThree_zero_add] using scanned

theorem transitionCoefficient_eq_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy symmetricThree.semigroup)
    (tested : Nat) (reflection : Nat → Fin 2) :
    transitionCoefficient tested reflection
        (transitionKeysFrom [] identity.lhs.toList) =
      transitionCoefficient tested reflection
        (transitionKeysFrom [] identity.rhs.toList) := by
  rw [← coefficientValue_eq_transitionCoefficient,
    ← coefficientValue_eq_transitionCoefficient]
  exact coefficientValue_eq_of_valid identity valid tested reflection

end SemigroupBasis.Examples.SymmetricThreeCompleteness

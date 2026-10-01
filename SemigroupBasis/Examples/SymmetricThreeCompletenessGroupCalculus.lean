import SemigroupBasis.Examples.SymmetricThreeCompletenessTerm

namespace SemigroupBasis.Examples.SymmetricThreeCompleteness

open SemigroupBasis

local infixl:70 " *t " => termMul.mul

theorem inv_unique_left {value candidate : Term}
    (inverse : candidate *t value = one) : candidate = inv value := by
  calc
    candidate = candidate *t one := (mul_one candidate).symm
    _ = candidate *t (value *t inv value) := by rw [mul_inv]
    _ = (candidate *t value) *t inv value :=
      (termMul.assoc _ _ _).symm
    _ = one *t inv value := by rw [inverse]
    _ = inv value := one_mul _

theorem inv_unique_right {value candidate : Term}
    (inverse : value *t candidate = one) : candidate = inv value := by
  calc
    candidate = one *t candidate := (one_mul candidate).symm
    _ = (inv value *t value) *t candidate := by rw [inv_mul]
    _ = inv value *t (value *t candidate) := termMul.assoc _ _ _
    _ = inv value *t one := by rw [inverse]
    _ = inv value := mul_one _

@[simp]
theorem inv_one : inv one = one := by
  symm
  apply inv_unique_left
  exact one_mul one

@[simp]
theorem inv_inv (value : Term) : inv (inv value) = value := by
  symm
  apply inv_unique_left
  exact mul_inv value

theorem inv_mul_rev (left right : Term) :
    inv (left *t right) = inv right *t inv left := by
  symm
  apply inv_unique_left
  calc
    (inv right *t inv left) *t (left *t right) =
        inv right *t (inv left *t (left *t right)) := by
      exact termMul.assoc _ _ _
    _ = inv right *t ((inv left *t left) *t right) := by
      rw [termMul.assoc]
    _ = inv right *t (one *t right) := by rw [inv_mul]
    _ = inv right *t right := by rw [one_mul]
    _ = one := inv_mul right

theorem inv_mul_cancel_left (value suffix : Term) :
    inv value *t (value *t suffix) = suffix := by
  calc
    inv value *t (value *t suffix) =
        (inv value *t value) *t suffix :=
      (termMul.assoc _ _ _).symm
    _ = one *t suffix := by rw [inv_mul]
    _ = suffix := one_mul _

theorem mul_inv_cancel_left (value suffix : Term) :
    value *t (inv value *t suffix) = suffix := by
  calc
    value *t (inv value *t suffix) =
        (value *t inv value) *t suffix :=
      (termMul.assoc _ _ _).symm
    _ = one *t suffix := by rw [mul_inv]
    _ = suffix := one_mul _

theorem inv_mul_cancel_right (initial value : Term) :
    (initial *t inv value) *t value = initial := by
  calc
    (initial *t inv value) *t value =
        initial *t (inv value *t value) := termMul.assoc _ _ _
    _ = initial *t one := by rw [inv_mul]
    _ = initial := mul_one _

theorem mul_inv_cancel_right (initial value : Term) :
    (initial *t value) *t inv value = initial := by
  calc
    (initial *t value) *t inv value =
        initial *t (value *t inv value) := termMul.assoc _ _ _
    _ = initial *t one := by rw [mul_inv]
    _ = initial := mul_one _

theorem mul_left_cancel {left right factor : Term}
    (equality : factor *t left = factor *t right) : left = right := by
  calc
    left = inv factor *t (factor *t left) :=
      (inv_mul_cancel_left factor left).symm
    _ = inv factor *t (factor *t right) := by rw [equality]
    _ = right := inv_mul_cancel_left factor right

theorem mul_right_cancel {left right factor : Term}
    (equality : left *t factor = right *t factor) : left = right := by
  calc
    left = (left *t factor) *t inv factor :=
      (mul_inv_cancel_right left factor).symm
    _ = (right *t factor) *t inv factor := by rw [equality]
    _ = right := mul_inv_cancel_right right factor

def square (value : Term) : Term := value *t value

@[simp]
theorem square_classOf (word : Word Nat) :
    square (classOf word) =
      classOf (symmetricThreeSquare word) := by
  rfl

theorem square_comm (left right : Term) :
    square left *t square right = square right *t square left := by
  refine Quotient.inductionOn left ?_
  intro leftWord
  refine Quotient.inductionOn right ?_
  intro rightWord
  exact square_mul_square_comm leftWord rightWord

theorem square_cube_eq_one (value : Term) :
    square value *t (square value *t square value) = one := by
  refine Quotient.inductionOn value ?_
  exact square_cube

theorem square_square_eq_inv (value : Term) :
    square value *t square value = inv (square value) := by
  apply inv_unique_right
  exact square_cube_eq_one value

theorem inv_square (value : Term) :
    inv (square value) = square value *t square value :=
  (square_square_eq_inv value).symm

def conjugate (actor value : Term) : Term :=
  (actor *t value) *t inv actor

theorem conjugate_mul (actor left right : Term) :
    conjugate actor (left *t right) =
      conjugate actor left *t conjugate actor right := by
  unfold conjugate
  have cancelMiddle :
      inv actor *t ((actor *t right) *t inv actor) =
        right *t inv actor := by
    calc
      inv actor *t ((actor *t right) *t inv actor) =
          (inv actor *t (actor *t right)) *t inv actor :=
        (termMul.assoc _ _ _).symm
      _ = right *t inv actor := by rw [inv_mul_cancel_left]
  calc
    (actor *t (left *t right)) *t inv actor =
        ((actor *t left) *t right) *t inv actor := by
      exact congrArg (fun value => value *t inv actor)
        (termMul.assoc actor left right).symm
    _ = (actor *t left) *t (right *t inv actor) :=
      termMul.assoc _ _ _
    _ = (actor *t left) *t
        (inv actor *t ((actor *t right) *t inv actor)) := by
      exact congrArg (fun value => (actor *t left) *t value)
        cancelMiddle.symm
    _ = ((actor *t left) *t inv actor) *t
        ((actor *t right) *t inv actor) :=
      (termMul.assoc _ _ _).symm

theorem conjugate_square (actor value : Term) :
    conjugate actor (square value) =
      square (conjugate actor value) := by
  unfold square
  exact conjugate_mul actor value value

theorem conjugate_one (actor : Term) :
    conjugate actor one = one := by
  unfold conjugate
  rw [mul_one, mul_inv]

/-- The group commutator in the convention `a b a^-1 b^-1`. -/
def commutator (left right : Term) : Term :=
  ((left *t right) *t inv left) *t inv right

/-- A commutator is a product of three squares. -/
theorem commutator_eq_square_product (left right : Term) :
    commutator left right =
      square left *t
        (square (inv left *t right) *t square (inv right)) := by
  have firstPair :
      square left *t square (inv left *t right) =
        ((left *t right) *t inv left) *t right := by
    unfold square
    calc
      (left *t left) *t
          ((inv left *t right) *t (inv left *t right)) =
          left *t
            (left *t ((inv left *t right) *t
              (inv left *t right))) := termMul.assoc _ _ _
      _ = left *t
            ((left *t (inv left *t right)) *t
              (inv left *t right)) := by
        exact congrArg (fun value => left *t value)
          (termMul.assoc left (inv left *t right)
            (inv left *t right)).symm
      _ = left *t (right *t (inv left *t right)) := by
        rw [mul_inv_cancel_left]
      _ = (left *t right) *t (inv left *t right) :=
        (termMul.assoc _ _ _).symm
      _ = ((left *t right) *t inv left) *t right :=
        (termMul.assoc _ _ _).symm
  unfold commutator
  symm
  calc
    square left *t
        (square (inv left *t right) *t square (inv right)) =
        (square left *t square (inv left *t right)) *t
          square (inv right) := (termMul.assoc _ _ _).symm
    _ =
        (((left *t right) *t inv left) *t right) *t
          square (inv right) := by rw [firstPair]
    _ = (((left *t right) *t inv left) *t right) *t
          (inv right *t inv right) := rfl
    _ = ((left *t right) *t inv left) *t
          (right *t (inv right *t inv right)) := termMul.assoc _ _ _
    _ = ((left *t right) *t inv left) *t inv right := by
      rw [mul_inv_cancel_left]

/-- Swapping two adjacent factors emits their commutator on the left. -/
theorem mul_eq_commutator_mul_swap (left right : Term) :
    left *t right = commutator left right *t (right *t left) := by
  symm
  unfold commutator
  calc
    (((left *t right) *t inv left) *t inv right) *t
        (right *t left) =
        ((left *t right) *t inv left) *t
          (inv right *t (right *t left)) := termMul.assoc _ _ _
    _ = ((left *t right) *t inv left) *t left := by
      rw [inv_mul_cancel_left]
    _ = left *t right := inv_mul_cancel_right _ _

/-- Moving a square through a factor conjugates the square base. -/
theorem square_mul_eq_mul_conjugate_square
    (value actor : Term) :
    square value *t actor =
      actor *t square (conjugate (inv actor) value) := by
  apply mul_left_cancel (factor := inv actor)
  calc
    inv actor *t (square value *t actor) =
        (inv actor *t square value) *t actor :=
      (termMul.assoc _ _ _).symm
    _ = conjugate (inv actor) (square value) := by
      unfold conjugate
      rw [inv_inv]
    _ = square (conjugate (inv actor) value) :=
      conjugate_square _ _
    _ = inv actor *t
        (actor *t square (conjugate (inv actor) value)) :=
      (inv_mul_cancel_left actor _).symm

end SemigroupBasis.Examples.SymmetricThreeCompleteness

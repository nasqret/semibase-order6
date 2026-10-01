import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.Examples.SymmetricThreeCompletenessGroupCalculus

namespace SemigroupBasis.Examples.SymmetricThreeCompleteness

open SemigroupBasis

local infixl:70 " *t " => termMul.mul

/-- Product of square classes.  The empty product is represented by the
positive identity class. -/
def squareProduct : List Term → Term
  | [] => one
  | value :: rest => square value *t squareProduct rest

@[simp]
theorem squareProduct_nil : squareProduct [] = one :=
  rfl

@[simp]
theorem squareProduct_cons (value : Term) (rest : List Term) :
    squareProduct (value :: rest) =
      square value *t squareProduct rest :=
  rfl

theorem squareProduct_append (left right : List Term) :
    squareProduct (left ++ right) =
      squareProduct left *t squareProduct right := by
  induction left with
  | nil =>
      simp only [List.nil_append, squareProduct_nil, one_mul]
  | cons value rest inductionHypothesis =>
      simp only [List.cons_append, squareProduct_cons,
        inductionHypothesis, termMul.assoc]

theorem square_comm_squareProduct (value : Term) (payload : List Term) :
    square value *t squareProduct payload =
      squareProduct payload *t square value := by
  induction payload with
  | nil =>
      simp only [squareProduct_nil, mul_one, one_mul]
  | cons next rest inductionHypothesis =>
      simp only [squareProduct_cons]
      calc
        square value *t (square next *t squareProduct rest) =
            (square value *t square next) *t squareProduct rest :=
          (termMul.assoc _ _ _).symm
        _ = (square next *t square value) *t squareProduct rest := by
          rw [square_comm]
        _ = square next *t (square value *t squareProduct rest) :=
          termMul.assoc _ _ _
        _ = square next *t (squareProduct rest *t square value) := by
          rw [inductionHypothesis]
        _ = (square next *t squareProduct rest) *t square value :=
          (termMul.assoc _ _ _).symm

theorem squareProduct_comm (left right : List Term) :
    squareProduct left *t squareProduct right =
      squareProduct right *t squareProduct left := by
  induction left with
  | nil =>
      simp only [squareProduct_nil, one_mul, mul_one]
  | cons value rest inductionHypothesis =>
      simp only [squareProduct_cons]
      calc
        (square value *t squareProduct rest) *t squareProduct right =
            square value *t
              (squareProduct rest *t squareProduct right) :=
          termMul.assoc _ _ _
        _ = square value *t
              (squareProduct right *t squareProduct rest) := by
          rw [inductionHypothesis]
        _ = (square value *t squareProduct right) *t
              squareProduct rest :=
          (termMul.assoc _ _ _).symm
        _ = (squareProduct right *t square value) *t
              squareProduct rest := by
          rw [square_comm_squareProduct]
        _ = squareProduct right *t
              (square value *t squareProduct rest) :=
          termMul.assoc _ _ _

theorem squareProduct_conjugate (actor : Term) (payload : List Term) :
    conjugate actor (squareProduct payload) =
      squareProduct (payload.map (conjugate actor)) := by
  induction payload with
  | nil =>
      simp only [squareProduct_nil, List.map_nil, conjugate_one]
  | cons value rest inductionHypothesis =>
      simp only [squareProduct_cons, List.map_cons, conjugate_mul,
        conjugate_square, inductionHypothesis]

theorem exists_squareProduct_inv (payload : List Term) :
    ∃ inversePayload,
      inv (squareProduct payload) = squareProduct inversePayload := by
  induction payload with
  | nil =>
      exact ⟨[], by simp only [squareProduct_nil, inv_one]⟩
  | cons value rest inductionHypothesis =>
      obtain ⟨inverseRest, inverseRestEq⟩ := inductionHypothesis
      refine ⟨inverseRest ++ [value, value], ?_⟩
      rw [squareProduct_cons, inv_mul_rev, inverseRestEq, inv_square,
        squareProduct_append]
      simp only [squareProduct_cons, squareProduct_nil, mul_one]

/-- Equality modulo a product of squares, with the payload kept explicit. -/
def SquareEquivalent (left right : Term) : Prop :=
  ∃ payload, left = squareProduct payload *t right

theorem SquareEquivalent.refl (value : Term) :
    SquareEquivalent value value := by
  refine ⟨[], ?_⟩
  simp only [squareProduct_nil, one_mul]

theorem SquareEquivalent.trans {left middle right : Term}
    (first : SquareEquivalent left middle)
    (second : SquareEquivalent middle right) :
    SquareEquivalent left right := by
  obtain ⟨firstPayload, firstEq⟩ := first
  obtain ⟨secondPayload, secondEq⟩ := second
  refine ⟨firstPayload ++ secondPayload, ?_⟩
  rw [firstEq, secondEq, squareProduct_append, termMul.assoc]

theorem SquareEquivalent.symm {left right : Term}
    (equivalent : SquareEquivalent left right) :
    SquareEquivalent right left := by
  obtain ⟨payload, equality⟩ := equivalent
  obtain ⟨inversePayload, inverseEq⟩ :=
    exists_squareProduct_inv payload
  refine ⟨inversePayload, ?_⟩
  rw [← inverseEq, equality]
  exact (inv_mul_cancel_left (squareProduct payload) right).symm

theorem SquareEquivalent.mul_right {left right : Term}
    (equivalent : SquareEquivalent left right) (suffix : Term) :
    SquareEquivalent (left *t suffix) (right *t suffix) := by
  obtain ⟨payload, equality⟩ := equivalent
  refine ⟨payload, ?_⟩
  rw [equality, termMul.assoc]

theorem SquareEquivalent.mul_left {left right : Term}
    (initial : Term) (equivalent : SquareEquivalent left right) :
    SquareEquivalent (initial *t left) (initial *t right) := by
  obtain ⟨payload, equality⟩ := equivalent
  refine ⟨payload.map (conjugate initial), ?_⟩
  rw [equality, ← squareProduct_conjugate]
  unfold conjugate
  calc
    initial *t (squareProduct payload *t right) =
        (initial *t squareProduct payload) *t right :=
      (termMul.assoc _ _ _).symm
    _ = (((initial *t squareProduct payload) *t inv initial) *t
          initial) *t right := by
      rw [inv_mul_cancel_right]
    _ = ((initial *t squareProduct payload) *t inv initial) *t
          (initial *t right) := by
      rw [termMul.assoc]

theorem SquareEquivalent.mul
    {left₁ right₁ left₂ right₂ : Term}
    (first : SquareEquivalent left₁ right₁)
    (second : SquareEquivalent left₂ right₂) :
    SquareEquivalent (left₁ *t left₂) (right₁ *t right₂) :=
  (first.mul_right left₂).trans (second.mul_left right₁)

theorem square_equivalent_one (value : Term) :
    SquareEquivalent (square value) one := by
  refine ⟨[value], ?_⟩
  simp only [squareProduct_cons, squareProduct_nil, mul_one]

theorem squareProduct_equivalent_one (payload : List Term) :
    SquareEquivalent (squareProduct payload) one := by
  refine ⟨payload, ?_⟩
  rw [mul_one]

theorem commutator_equivalent_one (left right : Term) :
    SquareEquivalent (commutator left right) one := by
  refine ⟨[left, inv left *t right, inv right], ?_⟩
  rw [commutator_eq_square_product]
  simp only [squareProduct_cons, squareProduct_nil, mul_one]

theorem mul_squareEquivalent_swap (left right : Term) :
    SquareEquivalent (left *t right) (right *t left) := by
  refine ⟨[left, inv left *t right, inv right], ?_⟩
  rw [mul_eq_commutator_mul_swap, commutator_eq_square_product]
  simp only [squareProduct_cons, squareProduct_nil, mul_one]

def generator (letter : Nat) : Term :=
  classOf (Word.singleton letter)

/-- Product of singleton generator classes, allowing the empty list. -/
def headProduct : List Nat → Term
  | [] => one
  | letter :: rest => generator letter *t headProduct rest

@[simp]
theorem headProduct_nil : headProduct [] = one :=
  rfl

@[simp]
theorem headProduct_cons (letter : Nat) (rest : List Nat) :
    headProduct (letter :: rest) =
      generator letter *t headProduct rest :=
  rfl

theorem headProduct_append (left right : List Nat) :
    headProduct (left ++ right) =
      headProduct left *t headProduct right := by
  induction left with
  | nil =>
      simp only [List.nil_append, headProduct_nil, one_mul]
  | cons letter rest inductionHypothesis =>
      simp only [List.cons_append, headProduct_cons,
        inductionHypothesis, termMul.assoc]

theorem headProduct_perm {left right : List Nat}
    (permutation : left.Perm right) :
    SquareEquivalent (headProduct left) (headProduct right) := by
  induction permutation with
  | nil => exact SquareEquivalent.refl _
  | cons letter _ inductionHypothesis =>
      exact inductionHypothesis.mul_left (generator letter)
  | swap left right rest =>
      simp only [headProduct_cons]
      simpa only [termMul.assoc] using
        (mul_squareEquivalent_swap (generator right) (generator left)).mul_right
          (headProduct rest)
  | trans _ _ first second =>
      exact first.trans second

theorem headProduct_double_cancel (letter : Nat) (rest : List Nat) :
    SquareEquivalent
      (headProduct (letter :: letter :: rest))
      (headProduct rest) := by
  simpa only [headProduct_cons, square, termMul.assoc, one_mul] using
    (square_equivalent_one (generator letter)).mul_right
      (headProduct rest)

theorem headProduct_parityReduce (letters : List Nat) :
    SquareEquivalent (headProduct letters)
      (headProduct (parityReduce letters)) := by
  induction letters with
  | nil => exact SquareEquivalent.refl _
  | cons letter rest inductionHypothesis =>
      have prefixed := inductionHypothesis.mul_left (generator letter)
      simp only [parityReduce]
      by_cases member : letter ∈ parityReduce rest
      · rw [if_pos member]
        have permutation :
            (letter :: parityReduce rest).Perm
              (letter :: letter :: (parityReduce rest).erase letter) :=
          List.Perm.cons letter (List.perm_cons_erase member)
        exact prefixed.trans <|
          (headProduct_perm permutation).trans <|
            headProduct_double_cancel letter
              ((parityReduce rest).erase letter)
      · rw [if_neg member]
        exact prefixed

def canonicalParity (letters : List Nat) : List Nat :=
  (parityReduce letters).mergeSort
    (fun left right : Nat => decide (left ≤ right))

theorem parityReduce_perm_canonicalParity (letters : List Nat) :
    (parityReduce letters).Perm (canonicalParity letters) := by
  exact (List.mergeSort_perm _ _).symm

theorem headProduct_canonicalParity (letters : List Nat) :
    SquareEquivalent (headProduct letters)
      (headProduct (canonicalParity letters)) :=
  (headProduct_parityReduce letters).trans
    (headProduct_perm (parityReduce_perm_canonicalParity letters))

theorem classOf_eq_headProduct (word : Word Nat) :
    classOf word = headProduct word.toList := by
  cases word with
  | mk head tail =>
      change classOf { head := head, tail := tail } =
        headProduct (head :: tail)
      simp only [headProduct_cons]
      induction tail generalizing head with
      | nil =>
          change classOf (Word.singleton head) =
            generator head *t one
          rw [mul_one]
          rfl
      | cons next rest inductionHypothesis =>
          change
            classOf ({ head := head, tail := [] } ++
              { head := next, tail := rest }) =
              generator head *t headProduct (next :: rest)
          rw [← mul_classOf, inductionHypothesis]
          rfl

theorem classOf_squareEquivalent_canonicalParity (word : Word Nat) :
    SquareEquivalent (classOf word)
      (headProduct (canonicalParity word.toList)) := by
  rw [classOf_eq_headProduct]
  exact headProduct_canonicalParity word.toList

end SemigroupBasis.Examples.SymmetricThreeCompleteness

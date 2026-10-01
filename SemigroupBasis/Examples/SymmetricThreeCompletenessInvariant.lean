import SemigroupBasis.Examples.SymmetricThree
import SemigroupBasis.Examples.SymmetricThreeCompletenessTerm

namespace SemigroupBasis.Examples.SymmetricThreeCompleteness

open SemigroupBasis

/-- Coordinates for `S3 = C3 semidirect C2`.  The second coordinate acts on
the first by inversion. -/
structure Coord where
  rotation : Fin 3
  reflection : Fin 2
deriving DecidableEq, Repr

def negateRotation : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 2
  | _ => 1

def signedRotation (reflection : Fin 2) (rotation : Fin 3) : Fin 3 :=
  if reflection = 0 then rotation else negateRotation rotation

def coordMul (left right : Coord) : Coord :=
  { rotation := left.rotation +
      signedRotation left.reflection right.rotation
    reflection := left.reflection + right.reflection }

def coordSemigroup : Semigroup Coord where
  mul := coordMul
  assoc := by
    intro left middle right
    rcases left with ⟨leftRotation, leftReflection⟩
    rcases middle with ⟨middleRotation, middleReflection⟩
    rcases right with ⟨rightRotation, rightReflection⟩
    decide +revert

def coordOne : Coord := ⟨0, 0⟩

@[simp]
theorem coordMul_one_left (value : Coord) :
    coordMul coordOne value = value := by
  rcases value with ⟨rotation, reflection⟩
  decide +revert

@[simp]
theorem coordMul_one_right (value : Coord) :
    coordMul value coordOne = value := by
  rcases value with ⟨rotation, reflection⟩
  decide +revert

/-- Reconstruct the exact stored table element from semidirect coordinates. -/
def coordReconstruct : Coord → Fin 6
  | ⟨0, 0⟩ => 0
  | ⟨1, 0⟩ => 4
  | ⟨_, 0⟩ => 5
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 3
  | ⟨_, _⟩ => 2

/-- Classify the stored table element into semidirect coordinates. -/
def coordClassify : Fin 6 → Coord
  | 0 => ⟨0, 0⟩
  | 1 => ⟨0, 1⟩
  | 2 => ⟨2, 1⟩
  | 3 => ⟨1, 1⟩
  | 4 => ⟨1, 0⟩
  | _ => ⟨2, 0⟩

theorem coordReconstruct_classify (value : Fin 6) :
    coordReconstruct (coordClassify value) = value := by
  decide +revert

theorem coordClassify_reconstruct (value : Coord) :
    coordClassify (coordReconstruct value) = value := by
  rcases value with ⟨rotation, reflection⟩
  decide +revert

theorem coordReconstruct_injective :
    Function.Injective coordReconstruct := by
  intro left right equality
  have classified := congrArg coordClassify equality
  simpa [coordClassify_reconstruct] using classified

theorem coordClassify_injective :
    Function.Injective coordClassify := by
  intro left right equality
  have reconstructed := congrArg coordReconstruct equality
  simpa [coordReconstruct_classify] using reconstructed

/-- The coordinate multiplication is exactly the stored Cayley table. -/
theorem coordReconstruct_mul (left right : Coord) :
    coordReconstruct (coordMul left right) =
      symmetricThreeMul
        (coordReconstruct left) (coordReconstruct right) := by
  rcases left with ⟨leftRotation, leftReflection⟩
  rcases right with ⟨rightRotation, rightReflection⟩
  decide +revert

/-- Table multiplication classifies as semidirect multiplication. -/
theorem coordClassify_mul (left right : Fin 6) :
    coordClassify (symmetricThreeMul left right) =
      coordMul (coordClassify left) (coordClassify right) := by
  apply coordReconstruct_injective
  rw [coordReconstruct_classify, coordReconstruct_mul,
    coordReconstruct_classify, coordReconstruct_classify]

/-- Evaluation of a possibly empty list in semidirect coordinates. -/
def coordEvalList {alpha : Type}
    (valuation : alpha → Coord) (letters : List alpha) : Coord :=
  letters.foldl (fun current letter => coordMul current (valuation letter))
    coordOne

@[simp]
theorem coordEvalList_nil {alpha : Type}
    (valuation : alpha → Coord) :
    coordEvalList valuation [] = coordOne :=
  rfl

theorem coordEvalList_append {alpha : Type}
    (valuation : alpha → Coord) (left right : List alpha) :
    coordEvalList valuation (left ++ right) =
      coordMul (coordEvalList valuation left)
        (coordEvalList valuation right) := by
  unfold coordEvalList
  rw [List.foldl_append]
  generalize
    left.foldl (fun current letter => coordMul current (valuation letter))
      coordOne = initial
  induction right generalizing initial with
  | nil =>
      exact (coordMul_one_right initial).symm
  | cons letter rest inductionHypothesis =>
      simp only [List.foldl_cons]
      calc
        rest.foldl
            (fun current next => coordMul current (valuation next))
            (coordMul initial (valuation letter)) =
            coordMul (coordMul initial (valuation letter))
              (rest.foldl
                (fun current next => coordMul current (valuation next))
                coordOne) := inductionHypothesis _
        _ = coordMul initial
              (coordMul (valuation letter)
                (rest.foldl
                  (fun current next => coordMul current (valuation next))
                  coordOne)) := coordSemigroup.assoc _ _ _
        _ = coordMul initial
              (rest.foldl
                (fun current next => coordMul current (valuation next))
                (valuation letter)) := by
          rw [inductionHypothesis (valuation letter)]
        _ = coordMul initial
              (rest.foldl
                (fun current next => coordMul current (valuation next))
                (coordMul coordOne (valuation letter))) := by
          rw [coordMul_one_left]

/-- Coordinate evaluation agrees with semigroup evaluation on a nonempty
word. -/
theorem coordEval_eq_evalList {alpha : Type}
    (valuation : alpha → Coord) (word : Word alpha) :
    coordSemigroup.eval valuation word =
      coordEvalList valuation word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter => coordMul current (valuation letter))
            (valuation head) =
          (head :: tail).foldl
            (fun current letter => coordMul current (valuation letter))
            coordOne
      simp only [List.foldl_cons, coordMul_one_left]

/-- Reconstructing a coordinate evaluation gives evaluation in the exact
stored table. -/
private theorem coordReconstruct_fold {alpha : Type}
    (valuation : alpha → Coord) :
    ∀ (letters : List alpha) (initial : Coord),
      coordReconstruct
          (letters.foldl
            (fun current letter => coordMul current (valuation letter))
            initial) =
        letters.foldl
          (fun current letter =>
            symmetricThreeMul current
              (coordReconstruct (valuation letter)))
          (coordReconstruct initial)
  | [], _ => rfl
  | letter :: rest, initial => by
      simp only [List.foldl_cons]
      rw [coordReconstruct_fold valuation rest
        (coordMul initial (valuation letter))]
      exact congrArg
        (fun value =>
          rest.foldl
            (fun current next =>
              symmetricThreeMul current
                (coordReconstruct (valuation next))) value)
        (coordReconstruct_mul initial (valuation letter))

theorem coordReconstruct_eval {alpha : Type}
    (valuation : alpha → Coord) (word : Word alpha) :
    coordReconstruct (coordSemigroup.eval valuation word) =
      symmetricThree.semigroup.eval
        (fun letter => coordReconstruct (valuation letter)) word := by
  cases word with
  | mk head tail =>
      change
        coordReconstruct
            (tail.foldl
              (fun current letter => coordMul current (valuation letter))
              (valuation head)) =
          tail.foldl
            (fun current letter =>
              symmetricThreeMul current
                (coordReconstruct (valuation letter)))
            (coordReconstruct (valuation head))
      exact coordReconstruct_fold valuation tail (valuation head)

/-- Classifying a stored-table evaluation gives coordinate evaluation. -/
theorem coordClassify_eval {alpha : Type}
    (valuation : alpha → Fin 6) (word : Word alpha) :
    coordClassify (symmetricThree.semigroup.eval valuation word) =
      coordSemigroup.eval (fun letter => coordClassify (valuation letter))
        word := by
  apply coordReconstruct_injective
  rw [coordReconstruct_classify, coordReconstruct_eval]
  apply congrArg
    (fun rho : alpha → Fin 6 =>
      symmetricThree.semigroup.eval rho word)
  funext letter
  exact (coordReconstruct_classify (valuation letter)).symm

/-- Validity in the stored `S3` table yields equality under every coordinate
valuation. -/
theorem coordEval_eq_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy symmetricThree.semigroup)
    (valuation : Nat → Coord) :
    coordSemigroup.eval valuation identity.lhs =
      coordSemigroup.eval valuation identity.rhs := by
  apply coordReconstruct_injective
  rw [coordReconstruct_eval, coordReconstruct_eval]
  exact valid (fun letter => coordReconstruct (valuation letter))

/-- Conversely, coordinate equality for all valuations is exactly validity
in the stored table. -/
theorem valid_of_coordEval_eq
    (identity : Identity Nat)
    (valid : ∀ valuation : Nat → Coord,
      coordSemigroup.eval valuation identity.lhs =
        coordSemigroup.eval valuation identity.rhs) :
    identity.SatisfiedBy symmetricThree.semigroup := by
  intro valuation
  apply coordClassify_injective
  rw [coordClassify_eval, coordClassify_eval]
  exact valid (fun letter => coordClassify (valuation letter))

/-- The reflection component of a word under a chosen Boolean assignment. -/
def parityValue (reflection : Nat → Fin 2) (word : Word Nat) : Fin 2 :=
  (coordSemigroup.eval (fun letter => Coord.mk 0 (reflection letter)) word).reflection

/-- The signed coefficient of one selected variable under a reflection
assignment.  Only that variable receives rotation coordinate one. -/
def coefficientValue (tested : Nat) (reflection : Nat → Fin 2)
    (word : Word Nat) : Fin 3 :=
  (coordSemigroup.eval
    (fun letter =>
      Coord.mk (if letter = tested then 1 else 0) (reflection letter))
    word).rotation

theorem parityValue_eq_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy symmetricThree.semigroup)
    (reflection : Nat → Fin 2) :
    parityValue reflection identity.lhs =
      parityValue reflection identity.rhs := by
  exact congrArg Coord.reflection
    (coordEval_eq_of_valid identity valid
      (fun letter => Coord.mk 0 (reflection letter)))

theorem coefficientValue_eq_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy symmetricThree.semigroup)
    (tested : Nat) (reflection : Nat → Fin 2) :
    coefficientValue tested reflection identity.lhs =
      coefficientValue tested reflection identity.rhs := by
  exact congrArg Coord.rotation
    (coordEval_eq_of_valid identity valid
      (fun letter =>
        Coord.mk (if letter = tested then 1 else 0) (reflection letter)))

end SemigroupBasis.Examples.SymmetricThreeCompleteness

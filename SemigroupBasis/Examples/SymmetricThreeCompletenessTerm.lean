import SemigroupBasis.DerivationQuotient
import SemigroupBasis.Examples.SymmetricThreeSquareCalculus

namespace SemigroupBasis.Examples.SymmetricThreeCompleteness

open SemigroupBasis

/-- The term semigroup presented by the three positive-word laws for `S3`. -/
abbrev Term := TermSemigroup symmetricThreeBasis

/-- Multiplication in the presented term semigroup. -/
abbrev termMul : Semigroup Term := termSemigroup symmetricThreeBasis

/-- The derivability class represented by a nonempty word. -/
abbrev classOf (word : Word Nat) : Term :=
  termClass symmetricThreeBasis word

/-- A fixed positive representative of the identity class. -/
def oneWord : Word Nat :=
  symmetricThreeSixthPower (Word.singleton 0)

/-- The identity class in the presented term semigroup. -/
def one : Term := classOf oneWord

theorem classOf_eq_iff {left right : Word Nat} :
    classOf left = classOf right ↔
      Derives symmetricThreeBasis left right :=
  termClass_eq_iff_derives symmetricThreeBasis

@[simp]
theorem mul_classOf (left right : Word Nat) :
    termMul.mul (classOf left) (classOf right) =
      classOf (left ++ right) :=
  rfl

/-- Every sixth power represents the same identity class. -/
theorem classOf_sixthPower (word : Word Nat) :
    classOf (symmetricThreeSixthPower word) = one := by
  apply classOf_eq_iff.mpr
  exact symmetricThreeDerivesCommonSixth word (Word.singleton 0)

/-- The fixed class `one` is a left identity on represented terms. -/
theorem one_mul_classOf (word : Word Nat) :
    termMul.mul one (classOf word) = classOf word := by
  change classOf (oneWord ++ word) = classOf word
  apply classOf_eq_iff.mpr
  exact symmetricThreeDerivesSixthLeftIdentity (Word.singleton 0) word

/-- The fixed class `one` is a right identity on represented terms. -/
theorem mul_one_classOf (word : Word Nat) :
    termMul.mul (classOf word) one = classOf word := by
  change classOf (word ++ oneWord) = classOf word
  apply classOf_eq_iff.mpr
  exact symmetricThreeDerivesSixthRightIdentity (Word.singleton 0) word

private theorem derives_append_congr
    {left right : Word Nat}
    (derivation : Derives symmetricThreeBasis left right) :
    Derives symmetricThreeBasis (left ++ left) (right ++ right) := by
  exact Derives.trans
    (Derives.appendRight derivation left)
    (Derives.prepend right derivation)

private theorem derives_fifthPower_congr
    {left right : Word Nat}
    (derivation : Derives symmetricThreeBasis left right) :
    Derives symmetricThreeBasis
      (symmetricThreeFifthPower left)
      (symmetricThreeFifthPower right) := by
  have twice := derives_append_congr derivation
  have thrice :
      Derives symmetricThreeBasis
        ((left ++ left) ++ left) ((right ++ right) ++ right) :=
    Derives.trans
      (Derives.appendRight twice left)
      (Derives.prepend (right ++ right) derivation)
  have fourTimes :
      Derives symmetricThreeBasis
        (((left ++ left) ++ left) ++ left)
        (((right ++ right) ++ right) ++ right) :=
    Derives.trans
      (Derives.appendRight thrice left)
      (Derives.prepend ((right ++ right) ++ right) derivation)
  have fiveTimes :
      Derives symmetricThreeBasis
        ((((left ++ left) ++ left) ++ left) ++ left)
        ((((right ++ right) ++ right) ++ right) ++ right) :=
    Derives.trans
      (Derives.appendRight fourTimes left)
      (Derives.prepend (((right ++ right) ++ right) ++ right) derivation)
  simpa [symmetricThreeFifthPower] using fiveTimes

/-- Fifth power descends to a well-defined inverse operation on term classes. -/
def inv : Term → Term :=
  Quotient.lift
    (fun word : Word Nat => classOf (symmetricThreeFifthPower word))
    (by
      intro left right derivation
      exact classOf_eq_iff.mpr
        (derives_fifthPower_congr derivation))

@[simp]
theorem inv_classOf (word : Word Nat) :
    inv (classOf word) = classOf (symmetricThreeFifthPower word) :=
  rfl

/-- Fifth power is a left inverse in the term model. -/
theorem inv_mul_classOf (word : Word Nat) :
    termMul.mul (inv (classOf word)) (classOf word) = one := by
  rw [inv_classOf, mul_classOf]
  apply classOf_eq_iff.mpr
  exact symmetricThreeDerivesFifthPowerLeftInverse
    (Word.singleton 0) word

/-- Fifth power is a right inverse in the term model. -/
theorem mul_inv_classOf (word : Word Nat) :
    termMul.mul (classOf word) (inv (classOf word)) = one := by
  rw [inv_classOf, mul_classOf]
  apply classOf_eq_iff.mpr
  exact symmetricThreeDerivesFifthPowerRightInverse
    (Word.singleton 0) word

/-- The fixed class is a two-sided identity on all quotient elements. -/
theorem one_mul (value : Term) : termMul.mul one value = value := by
  refine Quotient.inductionOn value ?_
  exact one_mul_classOf

/-- The fixed class is a two-sided identity on all quotient elements. -/
theorem mul_one (value : Term) : termMul.mul value one = value := by
  refine Quotient.inductionOn value ?_
  exact mul_one_classOf

/-- Fifth power is a left inverse on all quotient elements. -/
theorem inv_mul (value : Term) : termMul.mul (inv value) value = one := by
  refine Quotient.inductionOn value ?_
  exact inv_mul_classOf

/-- Fifth power is a right inverse on all quotient elements. -/
theorem mul_inv (value : Term) : termMul.mul value (inv value) = one := by
  refine Quotient.inductionOn value ?_
  exact mul_inv_classOf

/-- Square classes commute in the term model. -/
theorem square_mul_square_comm
    (left right : Word Nat) :
    termMul.mul
        (classOf (symmetricThreeSquare left))
        (classOf (symmetricThreeSquare right)) =
      termMul.mul
        (classOf (symmetricThreeSquare right))
        (classOf (symmetricThreeSquare left)) := by
  rw [mul_classOf, mul_classOf]
  exact classOf_eq_iff.mpr
    (symmetricThreeDerivesCommuteSquares left right)

/-- Every square class has exponent dividing three. -/
theorem square_cube (word : Word Nat) :
    termMul.mul
        (classOf (symmetricThreeSquare word))
        (termMul.mul
          (classOf (symmetricThreeSquare word))
          (classOf (symmetricThreeSquare word))) =
      one := by
  rw [mul_classOf, mul_classOf]
  apply classOf_eq_iff.mpr
  let tripleSquare :=
    symmetricThreeSquare word ++
      (symmetricThreeSquare word ++ symmetricThreeSquare word)
  have insertIdentity :=
    symmetricThreeDerivesInsertSixthLeft
      (Word.singleton 0) tripleSquare
  have cancellation :=
    symmetricThreeDerivesCancelThreeSquaresRight oneWord word
  exact Derives.trans
    (by simpa [tripleSquare, Word.append_assoc] using insertIdentity)
    (by simpa [tripleSquare, Word.append_assoc] using cancellation)

end SemigroupBasis.Examples.SymmetricThreeCompleteness

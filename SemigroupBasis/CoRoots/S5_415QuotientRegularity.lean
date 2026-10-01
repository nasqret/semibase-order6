import SemigroupBasis.CoRoots.S5_415Regularity
import SemigroupBasis.DerivationQuotient
import SemigroupBasis.Regular

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-- An `S5_415` inverse witness descends to an inverse pair in the term
semigroup presented by `basis`. -/
theorem InverseWitness.termClass_isInverse
    {word : Word Nat} (witness : InverseWitness word) :
    (termSemigroup basis).IsInverse
      (termClass basis word)
      (termClass basis witness.inverse) := by
  constructor
  · simpa only [termSemigroup_mul_termClass] using
      (termClass_eq_iff_derives basis).2 witness.word_inverse_word
  · simpa only [termSemigroup_mul_termClass] using
      (termClass_eq_iff_derives basis).2 witness.inverse_word_inverse

/-- An `S5_415` inverse witness makes the represented term class regular. -/
theorem InverseWitness.termClass_isRegular
    {word : Word Nat} (witness : InverseWitness word) :
    (termSemigroup basis).IsRegular (termClass basis word) :=
  ⟨termClass basis witness.inverse, witness.termClass_isInverse⟩

/-- The class of `A B A` has inverse the class of `B A B`. -/
theorem cellTermClass_isInverse (A B : Word Nat) :
    (termSemigroup basis).IsInverse
      (termClass basis (cell A B))
      (termClass basis (cell B A)) :=
  (cellInverseWitness A B).termClass_isInverse

/-- The class of every nonempty-gap cell is regular. -/
theorem cellTermClass_isRegular (A B : Word Nat) :
    (termSemigroup basis).IsRegular (termClass basis (cell A B)) :=
  (cellInverseWitness A B).termClass_isRegular

/-- The class of `A A` is its own inverse. -/
theorem emptyGapSquareTermClass_isInverse (A : Word Nat) :
    (termSemigroup basis).IsInverse
      (termClass basis (emptyGapSquare A))
      (termClass basis (emptyGapSquare A)) :=
  (emptyGapSquareInverseWitness A).termClass_isInverse

/-- The class of every empty-gap square is regular. -/
theorem emptyGapSquareTermClass_isRegular (A : Word Nat) :
    (termSemigroup basis).IsRegular
      (termClass basis (emptyGapSquare A)) :=
  (emptyGapSquareInverseWitness A).termClass_isRegular

/-- Appended witnesses descend to inverse classes in reverse order. -/
theorem InverseWitness.append_termClass_isInverse
    {u v : Word Nat}
    (uWitness : InverseWitness u)
    (vWitness : InverseWitness v) :
    (termSemigroup basis).IsInverse
      (termClass basis (u ++ v))
      (termClass basis
        (vWitness.inverse ++ uWitness.inverse)) :=
  (uWitness.append vWitness).termClass_isInverse

/-- The class represented by an append of witnessed words is regular. -/
theorem InverseWitness.append_termClass_isRegular
    {u v : Word Nat}
    (uWitness : InverseWitness u)
    (vWitness : InverseWitness v) :
    (termSemigroup basis).IsRegular (termClass basis (u ++ v)) :=
  (uWitness.append vWitness).termClass_isRegular

end SemigroupBasis.CoRoots.S5_415

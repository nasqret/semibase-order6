import SemigroupBasis.CoRoots.S5_415

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-- Proof-relevant data exhibiting a word as regular modulo the `S5_415`
basis. -/
structure InverseWitness (word : Word Nat) where
  inverse : Word Nat
  word_inverse_word :
    Derives basis ((word ++ inverse) ++ word) word
  inverse_word_inverse :
    Derives basis ((inverse ++ word) ++ inverse) inverse

/-- The product of a word and a chosen inverse is derivably idempotent. -/
theorem InverseWitness.derivesWordInverseIdempotent
    {word : Word Nat} (witness : InverseWitness word) :
    Derives basis
      ((word ++ witness.inverse) ++ (word ++ witness.inverse))
      (word ++ witness.inverse) := by
  simpa [Word.append_assoc] using
    Derives.appendRight witness.word_inverse_word witness.inverse

/-- The product of a chosen inverse and its word is derivably idempotent. -/
theorem InverseWitness.derivesInverseWordIdempotent
    {word : Word Nat} (witness : InverseWitness word) :
    Derives basis
      ((witness.inverse ++ word) ++ (witness.inverse ++ word))
      (witness.inverse ++ word) := by
  simpa [Word.append_assoc] using
    Derives.appendRight witness.inverse_word_inverse word

/-- Derivably idempotent words commute.  Expand both to squares, apply the
square-commutation basis consequence, and contract the squares again. -/
theorem derivesCommuteIdempotents
    (left right : Word Nat)
    (leftIdempotent : Derives basis (left ++ left) left)
    (rightIdempotent : Derives basis (right ++ right) right) :
    Derives basis (left ++ right) (right ++ left) := by
  have step1 :
      Derives basis (left ++ right) ((left ++ left) ++ right) :=
    Derives.appendRight leftIdempotent.symm right
  have step2 :
      Derives basis ((left ++ left) ++ right)
        ((left ++ left) ++ (right ++ right)) :=
    Derives.prepend (left ++ left) rightIdempotent.symm
  have step3 :
      Derives basis ((left ++ left) ++ (right ++ right))
        ((right ++ right) ++ (left ++ left)) :=
    derivesSquareCommutation left right
  have step4 :
      Derives basis ((right ++ right) ++ (left ++ left))
        (right ++ (left ++ left)) :=
    Derives.appendRight rightIdempotent (left ++ left)
  have step5 :
      Derives basis (right ++ (left ++ left)) (right ++ left) :=
    Derives.prepend right leftIdempotent
  exact step1.trans <| step2.trans <| step3.trans <| step4.trans step5

/-- A nonempty-gap cell `A B A`. -/
def cell (A B : Word Nat) : Word Nat :=
  (A ++ B) ++ A

/-- The explicit inverse law for `A B A`, whose chosen inverse is `B A B`.
Three sandwich contractions reduce the alternating nine-block word. -/
theorem derivesCellInverseLaw (A B : Word Nat) :
    Derives basis
      ((cell A B ++ cell B A) ++ cell A B)
      (cell A B) := by
  have step1 :
      Derives basis
        ((cell A B ++ cell B A) ++ cell A B)
        ((((((A ++ B) ++ A) ++ B) ++ A) ++ B) ++ A) := by
    simpa [cell, Word.append_assoc] using
      Derives.appendRight (derivesSandwichContraction A B)
        (((B ++ A) ++ B) ++ A)
  have step2 :
      Derives basis
        ((((((A ++ B) ++ A) ++ B) ++ A) ++ B) ++ A)
        ((((A ++ B) ++ A) ++ B) ++ A) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (derivesSandwichContraction A B) (B ++ A)
  have step3 :
      Derives basis ((((A ++ B) ++ A) ++ B) ++ A)
        (cell A B) := by
    simpa [cell] using derivesSandwichContraction A B
  exact step1.trans <| step2.trans step3

/-- The cell `A B A` is regular, with explicit inverse `B A B`. -/
def cellInverseWitness (A B : Word Nat) : InverseWitness (cell A B) where
  inverse := cell B A
  word_inverse_word := derivesCellInverseLaw A B
  inverse_word_inverse := derivesCellInverseLaw B A

/-- The empty-gap cell, written as the square `A A`. -/
def emptyGapSquare (A : Word Nat) : Word Nat :=
  A ++ A

/-- The power law makes every empty-gap square derivably idempotent. -/
theorem derivesEmptyGapSquareIdempotent (A : Word Nat) :
    Derives basis
      (emptyGapSquare A ++ emptyGapSquare A)
      (emptyGapSquare A) := by
  have first :
      Derives basis ((A ++ A) ++ (A ++ A)) ((A ++ A) ++ A) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (derivesPowerContraction A) A
  simpa [emptyGapSquare] using first.trans (derivesPowerContraction A)

/-- The self-inverse law for the empty-gap square. -/
theorem derivesEmptyGapSquareInverseLaw (A : Word Nat) :
    Derives basis
      ((emptyGapSquare A ++ emptyGapSquare A) ++ emptyGapSquare A)
      (emptyGapSquare A) := by
  have first :=
    Derives.appendRight (derivesEmptyGapSquareIdempotent A)
      (emptyGapSquare A)
  exact first.trans (derivesEmptyGapSquareIdempotent A)

/-- The square `A A` is regular and is its own chosen inverse. -/
def emptyGapSquareInverseWitness (A : Word Nat) :
    InverseWitness (emptyGapSquare A) where
  inverse := emptyGapSquare A
  word_inverse_word := derivesEmptyGapSquareInverseLaw A
  inverse_word_inverse := derivesEmptyGapSquareInverseLaw A

/-- Products of witnessed regular words are witnessed regular.  The inverse
of `u v` is `vInv uInv`; the middle idempotents commute by the square law. -/
def InverseWitness.append
    {u v : Word Nat}
    (uWitness : InverseWitness u)
    (vWitness : InverseWitness v) :
    InverseWitness (u ++ v) where
  inverse := vWitness.inverse ++ uWitness.inverse
  word_inverse_word := by
    have commuteMiddle :
        Derives basis
          ((v ++ vWitness.inverse) ++ (uWitness.inverse ++ u))
          ((uWitness.inverse ++ u) ++ (v ++ vWitness.inverse)) :=
      derivesCommuteIdempotents
        (v ++ vWitness.inverse) (uWitness.inverse ++ u)
        vWitness.derivesWordInverseIdempotent
        uWitness.derivesInverseWordIdempotent
    have step1 :
        Derives basis
          (((u ++ v) ++ (vWitness.inverse ++ uWitness.inverse)) ++
            (u ++ v))
          (((((u ++ uWitness.inverse) ++ u) ++ v) ++
            vWitness.inverse) ++ v) := by
      simpa [Word.append_assoc] using
        Derives.appendRight (Derives.prepend u commuteMiddle) v
    have step2 :
        Derives basis
          (((((u ++ uWitness.inverse) ++ u) ++ v) ++
            vWitness.inverse) ++ v)
          (((u ++ v) ++ vWitness.inverse) ++ v) := by
      simpa [Word.append_assoc] using
        Derives.appendRight uWitness.word_inverse_word
          ((v ++ vWitness.inverse) ++ v)
    have step3 :
        Derives basis (((u ++ v) ++ vWitness.inverse) ++ v)
          (u ++ v) := by
      simpa [Word.append_assoc] using
        Derives.prepend u vWitness.word_inverse_word
    exact step1.trans <| step2.trans step3
  inverse_word_inverse := by
    have commuteMiddle :
        Derives basis
          ((uWitness.inverse ++ u) ++ (v ++ vWitness.inverse))
          ((v ++ vWitness.inverse) ++ (uWitness.inverse ++ u)) :=
      derivesCommuteIdempotents
        (uWitness.inverse ++ u) (v ++ vWitness.inverse)
        uWitness.derivesInverseWordIdempotent
        vWitness.derivesWordInverseIdempotent
    have step1 :
        Derives basis
          (((vWitness.inverse ++ uWitness.inverse) ++ (u ++ v)) ++
            (vWitness.inverse ++ uWitness.inverse))
          (((((vWitness.inverse ++ v) ++ vWitness.inverse) ++
            uWitness.inverse) ++ u) ++ uWitness.inverse) := by
      simpa [Word.append_assoc] using
        Derives.appendRight
          (Derives.prepend vWitness.inverse commuteMiddle)
          uWitness.inverse
    have step2 :
        Derives basis
          (((((vWitness.inverse ++ v) ++ vWitness.inverse) ++
            uWitness.inverse) ++ u) ++ uWitness.inverse)
          (((vWitness.inverse ++ uWitness.inverse) ++ u) ++
            uWitness.inverse) := by
      simpa [Word.append_assoc] using
        Derives.appendRight vWitness.inverse_word_inverse
          ((uWitness.inverse ++ u) ++ uWitness.inverse)
    have step3 :
        Derives basis
          (((vWitness.inverse ++ uWitness.inverse) ++ u) ++
            uWitness.inverse)
          (vWitness.inverse ++ uWitness.inverse) := by
      simpa [Word.append_assoc] using
        Derives.prepend vWitness.inverse
          uWitness.inverse_word_inverse
    exact step1.trans <| step2.trans step3

end SemigroupBasis.CoRoots.S5_415

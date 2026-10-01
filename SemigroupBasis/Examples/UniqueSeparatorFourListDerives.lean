import SemigroupBasis.Examples.UniqueSeparatorFour

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The nonempty word represented by a head and tail list. -/
def uniqueSeparatorWordOfCons (head : Nat) (tail : List Nat) :
    Word Nat :=
  ⟨head, tail⟩

/-- List-level derivability.  The empty list is related only to itself;
nonempty lists carry the corresponding semigroup-word derivation. -/
inductive UniqueSeparatorListDerives : List Nat → List Nat → Prop
  | empty : UniqueSeparatorListDerives [] []
  | words {leftHead rightHead : Nat}
      {leftTail rightTail : List Nat} :
      Derives uniqueSeparatorFourBasis
          (uniqueSeparatorWordOfCons leftHead leftTail)
          (uniqueSeparatorWordOfCons rightHead rightTail) →
        UniqueSeparatorListDerives
          (leftHead :: leftTail) (rightHead :: rightTail)

namespace UniqueSeparatorListDerives

theorem refl :
    ∀ letters : List Nat,
      UniqueSeparatorListDerives letters letters
  | [] => .empty
  | _ :: _ => .words (Derives.refl _)

theorem symm {left right : List Nat}
    (derivation : UniqueSeparatorListDerives left right) :
    UniqueSeparatorListDerives right left := by
  cases derivation with
  | empty =>
      exact .empty
  | words wordDerivation =>
      exact .words wordDerivation.symm

theorem trans {left middle right : List Nat}
    (first : UniqueSeparatorListDerives left middle)
    (second : UniqueSeparatorListDerives middle right) :
    UniqueSeparatorListDerives left right := by
  cases first with
  | empty =>
      cases second
      exact .empty
  | words firstWord =>
      cases second with
      | words secondWord =>
          exact .words (firstWord.trans secondWord)

theorem prepend (pre : List Nat) {left right : List Nat}
    (derivation : UniqueSeparatorListDerives left right) :
    UniqueSeparatorListDerives
      (pre ++ left) (pre ++ right) := by
  cases pre with
  | nil =>
      simpa using derivation
  | cons head tail =>
      cases derivation with
      | empty =>
          simpa using refl (head :: tail)
      | @words leftHead rightHead leftTail rightTail wordDerivation =>
          exact .words <| by
            have prefixed :=
              Derives.prepend
                (uniqueSeparatorWordOfCons head tail)
                wordDerivation
            simpa [uniqueSeparatorWordOfCons, Word.append,
              List.append_assoc] using prefixed

theorem append {left right : List Nat}
    (derivation : UniqueSeparatorListDerives left right)
    (suffix : List Nat) :
    UniqueSeparatorListDerives
      (left ++ suffix) (right ++ suffix) := by
  cases derivation with
  | empty =>
      simpa using refl suffix
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      cases suffix with
      | nil =>
          simpa using
            (UniqueSeparatorListDerives.words wordDerivation)
      | cons head tail =>
          exact .words <| by
            have appended :=
              Derives.appendRight wordDerivation
                (uniqueSeparatorWordOfCons head tail)
            simpa [uniqueSeparatorWordOfCons, Word.append,
              List.append_assoc] using appended

theorem context (pre suffix : List Nat)
    {left right : List Nat}
    (derivation : UniqueSeparatorListDerives left right) :
    UniqueSeparatorListDerives
      (pre ++ left ++ suffix)
      (pre ++ right ++ suffix) := by
  simpa [List.append_assoc] using
    (derivation.prepend pre).append suffix

theorem ofWord {left right : Word Nat}
    (derivation :
      Derives uniqueSeparatorFourBasis left right) :
    UniqueSeparatorListDerives left.toList right.toList := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact .words derivation

theorem toWord {leftHead rightHead : Nat}
    {leftTail rightTail : List Nat}
    (derivation :
      UniqueSeparatorListDerives
        (leftHead :: leftTail) (rightHead :: rightTail)) :
    Derives uniqueSeparatorFourBasis
      (uniqueSeparatorWordOfCons leftHead leftTail)
      (uniqueSeparatorWordOfCons rightHead rightTail) := by
  cases derivation with
  | words wordDerivation =>
      exact wordDerivation

theorem from_cons {leftHead : Nat} {leftTail target : List Nat}
    (derivation :
      UniqueSeparatorListDerives
        (leftHead :: leftTail) target) :
    ∃ rightHead rightTail,
      target = rightHead :: rightTail ∧
        Derives uniqueSeparatorFourBasis
          (uniqueSeparatorWordOfCons leftHead leftTail)
          (uniqueSeparatorWordOfCons rightHead rightTail) := by
  cases derivation with
  | words wordDerivation =>
      exact ⟨_, _, rfl, wordDerivation⟩

theorem target_ne_nil {leftHead : Nat} {leftTail target : List Nat}
    (derivation :
      UniqueSeparatorListDerives
        (leftHead :: leftTail) target) :
    target ≠ [] := by
  obtain ⟨rightHead, rightTail, rfl, _⟩ :=
    from_cons derivation
  simp

end UniqueSeparatorListDerives

end SemigroupBasis.Examples

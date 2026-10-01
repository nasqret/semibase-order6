import SemigroupBasis.Equational

namespace SemigroupBasis.CoRoots.S5_107

open SemigroupBasis

/-- The nonempty word represented by a head and tail list. -/
def listWordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- Basis-parameterized list-level derivability. The empty list is related
only to itself; nonempty lists carry the corresponding semigroup-word
derivation. -/
inductive ListDerives (basis : List (Identity Nat)) :
    List Nat → List Nat → Prop
  | empty : ListDerives basis [] []
  | words {leftHead rightHead : Nat}
      {leftTail rightTail : List Nat} :
      Derives basis
          (listWordOfCons leftHead leftTail)
          (listWordOfCons rightHead rightTail) →
        ListDerives basis
          (leftHead :: leftTail) (rightHead :: rightTail)

namespace ListDerives

theorem refl {basis : List (Identity Nat)} :
    ∀ letters : List Nat, ListDerives basis letters letters
  | [] => .empty
  | _ :: _ => .words (Derives.refl _)

theorem symm {basis : List (Identity Nat)}
    {left right : List Nat}
    (derivation : ListDerives basis left right) :
    ListDerives basis right left := by
  cases derivation with
  | empty =>
      exact .empty
  | words wordDerivation =>
      exact .words wordDerivation.symm

theorem trans {basis : List (Identity Nat)}
    {left middle right : List Nat}
    (first : ListDerives basis left middle)
    (second : ListDerives basis middle right) :
    ListDerives basis left right := by
  cases first with
  | empty =>
      cases second
      exact .empty
  | words firstWord =>
      cases second with
      | words secondWord =>
          exact .words (firstWord.trans secondWord)

theorem prepend (pre : List Nat)
    {basis : List (Identity Nat)} {left right : List Nat}
    (derivation : ListDerives basis left right) :
    ListDerives basis (pre ++ left) (pre ++ right) := by
  cases pre with
  | nil =>
      simpa using derivation
  | cons head tail =>
      cases derivation with
      | empty =>
          simpa using
            (refl (basis := basis) (head :: tail))
      | @words leftHead rightHead leftTail rightTail wordDerivation =>
          exact .words <| by
            have prefixed :=
              Derives.prepend
                (listWordOfCons head tail)
                wordDerivation
            simpa [listWordOfCons, Word.append,
              List.append_assoc] using prefixed

theorem append {basis : List (Identity Nat)}
    {left right : List Nat}
    (derivation : ListDerives basis left right)
    (suffix : List Nat) :
    ListDerives basis (left ++ suffix) (right ++ suffix) := by
  cases derivation with
  | empty =>
      simpa using (refl (basis := basis) suffix)
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      cases suffix with
      | nil =>
          simpa using
            (ListDerives.words wordDerivation)
      | cons head tail =>
          exact .words <| by
            have appended :=
              Derives.appendRight wordDerivation
                (listWordOfCons head tail)
            simpa [listWordOfCons, Word.append,
              List.append_assoc] using appended

theorem context (pre suffix : List Nat)
    {basis : List (Identity Nat)} {left right : List Nat}
    (derivation : ListDerives basis left right) :
    ListDerives basis
      (pre ++ left ++ suffix)
      (pre ++ right ++ suffix) := by
  simpa [List.append_assoc] using
    (derivation.prepend pre).append suffix

theorem ofWord {basis : List (Identity Nat)}
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    ListDerives basis left.toList right.toList := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact .words derivation

theorem toWord {basis : List (Identity Nat)}
    {leftHead rightHead : Nat}
    {leftTail rightTail : List Nat}
    (derivation :
      ListDerives basis
        (leftHead :: leftTail) (rightHead :: rightTail)) :
    Derives basis
      (listWordOfCons leftHead leftTail)
      (listWordOfCons rightHead rightTail) := by
  cases derivation with
  | words wordDerivation =>
      exact wordDerivation

theorem from_cons {basis : List (Identity Nat)}
    {leftHead : Nat} {leftTail target : List Nat}
    (derivation :
      ListDerives basis (leftHead :: leftTail) target) :
    ∃ rightHead rightTail,
      target = rightHead :: rightTail ∧
        Derives basis
          (listWordOfCons leftHead leftTail)
          (listWordOfCons rightHead rightTail) := by
  cases derivation with
  | words wordDerivation =>
      exact ⟨_, _, rfl, wordDerivation⟩

theorem target_ne_nil {basis : List (Identity Nat)}
    {leftHead : Nat} {leftTail target : List Nat}
    (derivation :
      ListDerives basis (leftHead :: leftTail) target) :
    target ≠ [] := by
  obtain ⟨rightHead, rightTail, rfl, _⟩ :=
    from_cons derivation
  simp

/-- A list permutation is derivable whenever every adjacent swap at the head
of a suffix is derivable. Prefixes are supplied by `prepend`. -/
theorem of_perm {basis : List (Identity Nat)}
    (adjacentSwap :
      ∀ (left right : Nat) (suffix : List Nat),
        ListDerives basis
          (left :: right :: suffix)
          (right :: left :: suffix))
    {source target : List Nat}
    (permutation : source.Perm target) :
    ListDerives basis source target := by
  induction permutation with
  | nil =>
      exact .empty
  | cons head _ ih =>
      simpa using ih.prepend [head]
  | swap left right suffix =>
      exact (adjacentSwap left right suffix).symm
  | trans _ _ ihFirst ihSecond =>
      exact ihFirst.trans ihSecond

end ListDerives

end SemigroupBasis.CoRoots.S5_107

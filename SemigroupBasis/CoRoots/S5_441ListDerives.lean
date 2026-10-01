import SemigroupBasis.CoRoots.S5_441PrimitiveDerivations
import SemigroupBasis.CoRoots.S5_107ListDerives

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis

/-- List-level derivability specialized to the `S5_441` basis. -/
abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

namespace ListDerives

theorem refl (letters : List Nat) :
    S5_107.ListDerives basis letters letters :=
  S5_107.ListDerives.refl (basis := basis) letters

theorem symm {left right : List Nat}
    (derivation : S5_107.ListDerives basis left right) :
    S5_107.ListDerives basis right left :=
  S5_107.ListDerives.symm (basis := basis) derivation

theorem trans {left middle right : List Nat}
    (first : S5_107.ListDerives basis left middle)
    (second : S5_107.ListDerives basis middle right) :
    S5_107.ListDerives basis left right :=
  S5_107.ListDerives.trans (basis := basis) first second

theorem prepend (pre : List Nat) {left right : List Nat}
    (derivation : S5_107.ListDerives basis left right) :
    S5_107.ListDerives basis
      (pre ++ left) (pre ++ right) :=
  S5_107.ListDerives.prepend (basis := basis) pre derivation

theorem append {left right : List Nat}
    (derivation : S5_107.ListDerives basis left right)
    (suffix : List Nat) :
    S5_107.ListDerives basis
      (left ++ suffix) (right ++ suffix) :=
  S5_107.ListDerives.append (basis := basis) derivation suffix

theorem context (pre suffix : List Nat) {left right : List Nat}
    (derivation : S5_107.ListDerives basis left right) :
    S5_107.ListDerives basis
      (pre ++ left ++ suffix)
      (pre ++ right ++ suffix) :=
  S5_107.ListDerives.context
    (basis := basis) pre suffix derivation

theorem ofWord {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_107.ListDerives basis left.toList right.toList :=
  S5_107.ListDerives.ofWord (basis := basis) derivation

theorem toWord {leftHead rightHead : Nat}
    {leftTail rightTail : List Nat}
    (derivation :
      S5_107.ListDerives basis
        (leftHead :: leftTail) (rightHead :: rightTail)) :
    Derives basis
      (S5_107.listWordOfCons leftHead leftTail)
      (S5_107.listWordOfCons rightHead rightTail) :=
  S5_107.ListDerives.toWord (basis := basis) derivation

theorem from_cons {leftHead : Nat} {leftTail target : List Nat}
    (derivation :
      S5_107.ListDerives basis (leftHead :: leftTail) target) :
    ∃ rightHead rightTail,
      target = rightHead :: rightTail ∧
        Derives basis
          (S5_107.listWordOfCons leftHead leftTail)
          (S5_107.listWordOfCons rightHead rightTail) :=
  S5_107.ListDerives.from_cons (basis := basis) derivation

theorem target_ne_nil {leftHead : Nat} {leftTail target : List Nat}
    (derivation :
      S5_107.ListDerives basis (leftHead :: leftTail) target) :
    target ≠ [] :=
  S5_107.ListDerives.target_ne_nil
    (basis := basis) derivation

theorem of_perm
    (adjacentSwap :
      ∀ (left right : Nat) (suffix : List Nat),
        S5_107.ListDerives basis
          (left :: right :: suffix)
          (right :: left :: suffix))
    {source target : List Nat}
    (permutation : source.Perm target) :
    S5_107.ListDerives basis source target :=
  S5_107.ListDerives.of_perm
    (basis := basis) adjacentSwap permutation

end ListDerives

end SemigroupBasis.CoRoots.S5_441

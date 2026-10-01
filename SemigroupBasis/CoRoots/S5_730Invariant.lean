import SemigroupBasis.CoRoots.S5_730
import SemigroupBasis.CoRoots.S5_196

/-!
Source-only exact invariants for the `S5_730` basis.

This module records only the four coordinates supplied by the semantic
certificate. It makes no normalization or completeness claim.
-/

namespace SemigroupBasis.CoRoots.S5_730Invariant

open SemigroupBasis

/-- Equality of the exact head, support, exact final, and optional globally
simple final variable. -/
structure SameSignature (left right : Word Nat) : Prop where
  head : left.head = right.head
  support : S5_196.SameSupport left right
  final :
    left.tail.getLastD left.head =
      right.tail.getLastD right.head
  simpleFinal : S5_196.SameSimpleFinal left right

abbrev sameSignature (left right : Word Nat) : Prop :=
  SameSignature left right

namespace SameSignature

theorem refl (word : Word Nat) : SameSignature word word :=
  ⟨rfl, fun _ => Iff.rfl, rfl, fun _ => Iff.rfl⟩

theorem symm {left right : Word Nat}
    (same : SameSignature left right) :
    SameSignature right left :=
  ⟨same.head.symm,
    fun letter => (same.support letter).symm,
    same.final.symm,
    fun letter => (same.simpleFinal letter).symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameSignature left middle)
    (second : SameSignature middle right) :
    SameSignature left right :=
  ⟨first.head.trans second.head,
    fun letter =>
      (first.support letter).trans (second.support letter),
    first.final.trans second.final,
    fun letter =>
      (first.simpleFinal letter).trans
        (second.simpleFinal letter)⟩

end SameSignature

end SemigroupBasis.CoRoots.S5_730Invariant

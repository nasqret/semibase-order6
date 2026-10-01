import SemigroupBasis.CoRoots.S5_303
import SemigroupBasis.CoRoots.S5_83Invariant

namespace SemigroupBasis.CoRoots.S5_303

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_83

/-- The literal final variable, including the singleton stratum. -/
def FinalLetter (word : Word Nat) (z : Nat) : Prop :=
  match terminalSplit word with
  | .singleton final => final = z
  | .pair _ _ final => final = z

/-- A globally unique final variable with its exact penultimate variable.
The penultimate variable itself may have occurred earlier. -/
def UniqueFinalPair (word : Word Nat) (p t : Nat) : Prop :=
  match terminalSplit word with
  | .singleton _ => False
  | .pair stem penultimate final =>
      penultimate = p ∧ final = t ∧
        final ≠ penultimate ∧ final ∉ stem

/-- Componentwise form of the content plus penultimate/final invariant. -/
structure SameContentEndpointSignature
    (left right : Word Nat) : Prop where
  support : SameSupport left right
  singleton :
    IsSingletonWord left ↔ IsSingletonWord right
  finalLetter :
    ∀ z, FinalLetter left z ↔ FinalLetter right z
  uniqueFinalPair :
    ∀ p t, UniqueFinalPair left p t ↔
      UniqueFinalPair right p t

namespace SameContentEndpointSignature

theorem symm {left right : Word Nat}
    (same : SameContentEndpointSignature left right) :
    SameContentEndpointSignature right left :=
  ⟨fun z => (same.support z).symm,
    same.singleton.symm,
    fun z => (same.finalLetter z).symm,
    fun p t => (same.uniqueFinalPair p t).symm⟩

end SameContentEndpointSignature

end SemigroupBasis.CoRoots.S5_303

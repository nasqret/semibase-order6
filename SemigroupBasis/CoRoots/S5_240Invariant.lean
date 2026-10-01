import SemigroupBasis.CoRoots.S5_240
import SemigroupBasis.CoRoots.S5_83Invariant

namespace SemigroupBasis.CoRoots.S5_240

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_83

/-- The penultimate variable occurs exactly once, and the ordered final pair
is the specified pair. The final variable may have occurred earlier. -/
def SimplePenultimatePair (word : Word Nat) (p t : Nat) : Prop :=
  match terminalSplit word with
  | .singleton _ => False
  | .pair stem penultimate final =>
      penultimate = p ∧ final = t ∧
        p ∉ stem ∧ t ≠ p

theorem simplePenultimatePair_penultimate_mem
    {word : Word Nat} {p t : Nat}
    (pair : SimplePenultimatePair word p t) :
    p ∈ word.toList := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      simp [SimplePenultimatePair, splitEq] at pair
  | pair stem penultimate final =>
      have parts :
          penultimate = p ∧ final = t ∧
            p ∉ stem ∧ t ≠ p := by
        simpa [SimplePenultimatePair, splitEq] using pair
      rw [← terminalSplit_renderList word, splitEq]
      simp [TerminalSplit.renderList, parts.1]

/-- Componentwise form of the complete S5_240 endpoint-suffix invariant. -/
structure SameEndpointSuffixSignature
    (left right : Word Nat) : Prop where
  support : SameSupport left right
  singleton :
    IsSingletonWord left ↔ IsSingletonWord right
  uniqueFinal :
    ∀ z, UniqueFinal left z ↔ UniqueFinal right z
  simplePenultimatePair :
    ∀ p t,
      SimplePenultimatePair left p t ↔
        SimplePenultimatePair right p t

namespace SameEndpointSuffixSignature

theorem symm {left right : Word Nat}
    (same : SameEndpointSuffixSignature left right) :
    SameEndpointSuffixSignature right left :=
  ⟨fun z => (same.support z).symm,
    same.singleton.symm,
    fun z => (same.uniqueFinal z).symm,
    fun p t => (same.simplePenultimatePair p t).symm⟩

end SameEndpointSuffixSignature

end SemigroupBasis.CoRoots.S5_240

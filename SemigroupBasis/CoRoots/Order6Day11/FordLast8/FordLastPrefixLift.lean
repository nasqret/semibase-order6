import SemigroupBasis.CoRoots.Order6Day11.FordLast8.FordLastPresentation
import SemigroupBasis.CoRoots.S5_348Family

/-! Every S5_348 derivation replays behind a retained nonempty prefix. No cancellation is asserted. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLast8

open SemigroupBasis

abbrev lowerBasis : List (Identity Nat) := SemigroupBasis.CoRoots.S5_348.basis
abbrev coreTable : FiniteTable := Generated.Catalogue.S5_348.table
abbrev LowerSignature := SemigroupBasis.Examples.SimpleSequenceFirstGap.SameSignature

theorem guardedLowerAxiom (identity : Identity Nat) (member : identity ∈ lowerBasis)
    (substitution : Nat → Word Nat) (guard : Word Nat) :
    Derives basis (guard ++ identity.lhs.bind substitution)
      (guard ++ identity.rhs.bind substitution) := by
  simp only [lowerBasis, SemigroupBasis.CoRoots.S5_348.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have literal : SemigroupBasis.CoRoots.S5_348.powerLaw =
        (⟨(Word.mk 0 [0]), (Word.mk 0 [0, 0])⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.prepend guard (rawLaw00 (substitution 0))
  · have literal : SemigroupBasis.CoRoots.S5_348.leftDuplicationLaw =
        (⟨(Word.mk 0 [1, 0]), (Word.mk 0 [0, 1, 0])⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.prepend guard (rawLaw01 (substitution 0) (substitution 1)).symm
  · have literal : SemigroupBasis.CoRoots.S5_348.rightDuplicationLaw =
        (⟨(Word.mk 0 [1, 0]), (Word.mk 0 [1, 0, 0])⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.prepend guard (rawLaw07 (substitution 0) (substitution 1))
  · have literal : SemigroupBasis.CoRoots.S5_348.squareInterleaveLaw =
        (⟨(Word.mk 0 [0, 1, 1]), (Word.mk 0 [1, 0, 1])⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.prepend guard (rawLaw02 (substitution 0) (substitution 1))
  · have literal : SemigroupBasis.CoRoots.S5_348.squareFinalSwitchLaw =
        (⟨(Word.mk 0 [0, 1, 1]), (Word.mk 0 [1, 1, 0])⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.prepend guard (rawLaw03 (substitution 0) (substitution 1))
  · have literal : SemigroupBasis.CoRoots.S5_348.squareInitialSwitchLaw =
        (⟨(Word.mk 0 [0, 1, 1]), (Word.mk 1 [0, 0, 1])⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      rawLaw08 guard (substitution 0) (substitution 1)
  · have literal : SemigroupBasis.CoRoots.S5_348.firstGapGatherLaw =
        (⟨(Word.mk 0 [0, 1, 2]), (Word.mk 0 [1, 0, 2])⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.prepend guard (rawLaw04 (substitution 0) (substitution 1) (substitution 2))

private theorem bind_append (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution = left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second = word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) : word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

theorem liftLowerWithPrefix {left right : Word Nat}
    (derivation : Derives lowerBasis left right)
    (guard : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis (guard ++ left.bind substitution) (guard ++ right.bind substitution) := by
  induction derivation generalizing guard substitution with
  | fromBasis member => exact guardedLowerAxiom _ member substitution guard
  | refl => exact Derives.refl _
  | symm _ induction => exact (induction guard substitution).symm
  | trans _ _ first second => exact (first guard substitution).trans (second guard substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (guard ++ stem.bind substitution) substitution
  | appendRight _ final induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (induction guard substitution) (final.bind substitution)
  | subst _ next induction =>
      simpa [bind_bind] using
        induction guard (fun letter => (next letter).bind substitution)

theorem samePrefixOfLowerValid (left right guard : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy coreTable.semigroup) :
    Derives basis (guard ++ left) (guard ++ right) := by
  have lower := SemigroupBasis.CoRoots.S5_348Family.S5_348.basis_complete.2
    (Identity.mk left right) valid
  simpa [bind_singleton] using liftLowerWithPrefix lower guard Word.singleton

end SemigroupBasis.CoRoots.Order6Day11.FordLast8

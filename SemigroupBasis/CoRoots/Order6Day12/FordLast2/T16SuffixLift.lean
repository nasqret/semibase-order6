import SemigroupBasis.CoRoots.Order6Day12.FordLast2.T16Presentation
import SemigroupBasis.CoRoots.Order6Day12.FordLast2.T16CoreObservations

/-! The exact S5_610 calculus replays before a retained nonempty suffix.
Only squareFinalSwitchLaw changes the final letter; its guarded instance is
exactly B9 law07. Reversal supplies the already-tested head-case interface. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day12.FordLast2

open SemigroupBasis

abbrev lowerBasis : List (Identity Nat) := SemigroupBasis.CoRoots.S5_381.basis

theorem guardedLowerAxiom (identity : Identity Nat) (member : identity ∈ lowerBasis)
    (substitution : Nat → Word Nat) (guard : Word Nat) :
    Derives basis (identity.lhs.bind substitution ++ guard)
      (identity.rhs.bind substitution ++ guard) := by
  simp only [lowerBasis, SemigroupBasis.CoRoots.S5_381.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have literal : SemigroupBasis.CoRoots.S5_381.powerLaw =
        (⟨(Word.mk 0 [0]), (Word.mk 0 [0, 0])⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.appendRight (rawLaw00 (substitution 0)) guard
  · have literal : SemigroupBasis.CoRoots.S5_381.leftDuplicationLaw =
        (⟨(Word.mk 0 [1, 0]), (Word.mk 0 [0, 1, 0])⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.appendRight (rawLaw01 (substitution 0) (substitution 1)) guard
  · have literal : SemigroupBasis.CoRoots.S5_381.rightDuplicationLaw =
        (⟨(Word.mk 0 [1, 0]), (Word.mk 0 [1, 0, 0])⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.appendRight (rawLaw02 (substitution 0) (substitution 1)) guard
  · have literal : SemigroupBasis.CoRoots.S5_381.squareInterleaveLaw =
        (⟨(Word.mk 0 [0, 1, 1]), (Word.mk 0 [1, 0, 1])⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.appendRight (rawLaw03 (substitution 0) (substitution 1)) guard
  · have literal : SemigroupBasis.CoRoots.S5_381.squareFinalSwitchLaw =
        (⟨(Word.mk 0 [0, 1, 1]), (Word.mk 0 [1, 1, 0])⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      rawLaw07 (substitution 0) (substitution 1) guard
  · have literal : SemigroupBasis.CoRoots.S5_381.squareInitialSwitchLaw =
        (⟨(Word.mk 0 [0, 1, 1]), (Word.mk 1 [0, 0, 1])⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.appendRight (rawLaw04 (substitution 0) (substitution 1)) guard
  · have literal : SemigroupBasis.CoRoots.S5_381.interiorInsertionLaw =
        (⟨(Word.mk 0 [1, 2, 0]), (Word.mk 0 [1, 0, 2, 0])⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.appendRight (rawLaw05 (substitution 0) (substitution 1) (substitution 2)) guard
  · have literal : SemigroupBasis.CoRoots.S5_381.prefixedGatherLaw =
        (⟨(Word.mk 0 [1, 2, 1]), (Word.mk 0 [2, 1, 1])⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.appendRight (rawLaw06 (substitution 0) (substitution 1) (substitution 2)) guard

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

theorem liftLowerWithSuffix {left right : Word Nat}
    (derivation : Derives lowerBasis left right)
    (guard : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis (left.bind substitution ++ guard) (right.bind substitution ++ guard) := by
  induction derivation generalizing guard substitution with
  | fromBasis member => exact guardedLowerAxiom _ member substitution guard
  | refl => exact Derives.refl _
  | symm _ induction => exact (induction guard substitution).symm
  | trans _ _ first second => exact (first guard substitution).trans (second guard substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind substitution) (induction guard substitution)
  | appendRight _ final induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (final.bind substitution ++ guard) substitution
  | subst _ next induction =>
      simpa [bind_bind] using
        induction guard (fun letter => (next letter).bind substitution)

theorem sameSuffixOfCoreValid (left right guard : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy coreTable.semigroup) :
    Derives basis (left ++ guard) (right ++ guard) := by
  have lower := SemigroupBasis.CoRoots.S5_381Family.S5_610.representative_basis.2
    (Identity.mk left right) valid
  simpa [bind_singleton] using liftLowerWithSuffix lower guard Word.singleton

theorem samePrefixOfLowerValid (left right guard : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy reversedCore) :
    Derives dualBasis (guard ++ left) (guard ++ right) := by
  have directValid : (Identity.mk left.reverse right.reverse).SatisfiedBy coreTable.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed (Identity.mk left right) coreTable.semigroup).mp valid
  have directStep := sameSuffixOfCoreValid left.reverse right.reverse guard.reverse directValid
  simpa only [Word.reverse_append, Word.reverse_reverse] using directStep.reverse

theorem dualPower (word : Word Nat) :
    Derives dualBasis (word ++ word) ((word ++ word) ++ word) := by
  have step := (rawLaw00 word.reverse).reverse
  simpa only [Word.reverse_append, Word.reverse_reverse, Word.append_assoc] using step

theorem dualRepeatHead (left middle : Word Nat) :
    Derives dualBasis ((left ++ middle) ++ left) (((left ++ left) ++ middle) ++ left) := by
  have step := (rawLaw02 left.reverse middle.reverse).reverse
  simpa only [Word.reverse_append, Word.reverse_reverse, Word.append_assoc] using step

end SemigroupBasis.CoRoots.Order6Day12.FordLast2

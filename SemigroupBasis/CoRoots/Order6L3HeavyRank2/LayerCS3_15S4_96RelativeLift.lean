import SemigroupBasis.CoRoots.Order6L3HeavyRank2.Blocks
import SemigroupBasis.Examples.AffineParityFourSyntax

/-!
# Initial-relative affine lift for the isolated seven-law C3 pair

The fourth and fifth three-variable displayed laws are exactly the two
non-power affine-parity axioms under an arbitrary nonempty initial guard.
The seventh displayed law is retained as its own named bridge witness; the
literal first six-law source is neither imported nor reconstructed.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_15S4_96

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_15S4_96

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def powerIdentity : Identity Nat :=
  ⟨w 0 [], w 0 [0, 0]⟩

private def guardedSquareReturnIdentity : Identity Nat :=
  ⟨w 0 [1, 2], w 0 [2, 2, 1, 2]⟩

private def guardedMiddleSquareIdentity : Identity Nat :=
  ⟨w 0 [1, 2, 1, 2], w 0 [2, 1, 1, 2]⟩

/-- The frozen seventh law, including its exact orientation and both words. -/
def bridgeIdentity : Identity Nat :=
  ⟨w 0 [0, 1, 2, 0, 1], w 0 [1, 0, 2, 0, 1]⟩

private theorem targetPower :
    Derives targetBasis powerIdentity.lhs powerIdentity.rhs :=
  Derives.fromBasis (e := powerIdentity) (by decide)

private theorem targetGuardedSquareReturn :
    Derives targetBasis
      guardedSquareReturnIdentity.lhs guardedSquareReturnIdentity.rhs :=
  Derives.fromBasis (e := guardedSquareReturnIdentity) (by decide)

private theorem targetGuardedMiddleSquare :
    Derives targetBasis
      guardedMiddleSquareIdentity.lhs guardedMiddleSquareIdentity.rhs :=
  Derives.fromBasis (e := guardedMiddleSquareIdentity) (by decide)

/-- The mandatory `xxyzxy = xyxzxy` bridge is a genuine displayed-law path. -/
theorem derivesBridge :
    Derives targetBasis bridgeIdentity.lhs bridgeIdentity.rhs :=
  Derives.fromBasis (e := bridgeIdentity) (by decide)

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- The exact power axiom for an arbitrary nonempty substituted word. -/
theorem derivesTripleExpansion (word : Word Nat) :
    Derives targetBasis word ((word ++ word) ++ word) := by
  have substituted :=
    Derives.subst targetPower
      (instantiateThreeWords word word word)
  simpa [powerIdentity, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
    substituted

/-- `x y z = x z z y z` supplies the affine square-return axiom under
an arbitrary fixed nonempty initial guard. -/
theorem derivesSquareReturnUnderPrefix
    (initial x y : Word Nat) :
    Derives targetBasis
      (initial ++ (((x ++ x) ++ y) ++ x))
      (initial ++ (y ++ x)) := by
  have substituted :=
    Derives.subst targetGuardedSquareReturn.symm
      (instantiateThreeWords initial y x)
  simpa [guardedSquareReturnIdentity, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
    substituted

/-- `x y z y z = x z y y z` supplies the affine middle-square axiom
under the same arbitrary nonempty initial guard. -/
theorem derivesMiddleSquareUnderPrefix
    (initial x y : Word Nat) :
    Derives targetBasis
      (initial ++ (((x ++ y) ++ y) ++ x))
      (initial ++ (((y ++ x) ++ y) ++ x)) := by
  have substituted :=
    Derives.subst targetGuardedMiddleSquare.symm
      (instantiateThreeWords initial y x)
  simpa [guardedMiddleSquareIdentity, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
    substituted

/-- Every literal complete affine-parity axiom lifts after any fixed
nonempty guard, without changing its displayed orientation. -/
theorem derivesAffineAxiomUnderPrefix
    (identity : Identity Nat)
    (member : identity ∈ affineParityFourBasis)
    (initial : Word Nat) :
    Derives targetBasis
      (initial ++ identity.lhs) (initial ++ identity.rhs) := by
  simp only [affineParityFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · simpa [affineParityPowerLaw, affineParityX, affineParityXXX,
      powerIdentity, w, Word.singleton, Word.append] using
      Derives.prepend initial targetPower
  · simpa [affineParitySquareReturnLaw, affineParityXXYX,
      affineParityYX, Word.singleton, Word.append, Word.append_assoc] using
      derivesSquareReturnUnderPrefix
        initial (Word.singleton 0) (Word.singleton 1)
  · simpa [affineParityMiddleSquareLaw, affineParityXYYX,
      affineParityYXYX, Word.singleton, Word.append, Word.append_assoc] using
      derivesMiddleSquareUnderPrefix
        initial (Word.singleton 0) (Word.singleton 1)

private def prefixSubstitution
    (sigma : Nat → Word Nat) (initial : Word Nat) : Nat → Word Nat
  | 2 => initial
  | letter => sigma letter

/-- The fresh literal variable `2`, absent from all three affine axioms,
records the nonempty initial before an arbitrary substitution is applied. -/
theorem liftAffineAxiomUnderPrefix
    (identity : Identity Nat)
    (member : identity ∈ affineParityFourBasis)
    (initial : Word Nat) (sigma : Nat → Word Nat) :
    Derives targetBasis
      (initial ++ identity.lhs.bind sigma)
      (initial ++ identity.rhs.bind sigma) := by
  have substituted :=
    Derives.subst
      (derivesAffineAxiomUnderPrefix identity member (Word.singleton 2))
      (prefixSubstitution sigma initial)
  simp only [affineParityFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    simpa [affineParityPowerLaw, affineParitySquareReturnLaw,
      affineParityMiddleSquareLaw, affineParityX, affineParityXXX,
      affineParityXXYX, affineParityYX, affineParityXYYX,
      affineParityYXYX, prefixSubstitution, Word.bind,
      Word.singleton, Word.append, Word.append_assoc] using substituted

private theorem bind_append
    (left right : Word Nat) (sigma : Nat → Word Nat) :
    (left ++ right).bind sigma =
      left.bind sigma ++ right.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (tau sigma : Nat → Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun letter => (tau letter).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Every unrestricted affine-parity derivation survives under any fixed
nonempty initial guard, uniformly in the substituted alphabet and words. -/
theorem liftAffineUnderPrefix
    {left right : Word Nat}
    (derivation : Derives affineParityFourBasis left right)
    (initial : Word Nat) (sigma : Nat → Word Nat) :
    Derives targetBasis
      (initial ++ left.bind sigma) (initial ++ right.bind sigma) := by
  induction derivation generalizing initial sigma with
  | fromBasis member =>
      exact liftAffineAxiomUnderPrefix _ member initial sigma
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact (induction initial sigma).symm
  | trans _ _ first second =>
      exact (first initial sigma).trans (second initial sigma)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (initial ++ stem.bind sigma) sigma
  | appendRight _ appended induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (induction initial sigma) (appended.bind sigma)
  | subst _ tau induction =>
      simpa [bind_bind] using
        induction initial (fun letter => (tau letter).bind sigma)

/-- Identity-substitution specialization of the initial-relative lift. -/
theorem liftAffineUnderPrefixIdentity
    {left right : Word Nat}
    (derivation : Derives affineParityFourBasis left right)
    (initial : Word Nat) :
    Derives targetBasis (initial ++ left) (initial ++ right) := by
  simpa [bind_singleton] using
    liftAffineUnderPrefix derivation initial Word.singleton

/-- Add the same parity-neutral double copy of the first letter to the front
of an arbitrary nonempty word, using only the exact displayed power law. -/
theorem derivesHeadDoubleExpansion (word : Word Nat) :
    Derives targetBasis word
      ((Word.singleton word.head ++ Word.singleton word.head) ++ word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simpa [Word.singleton, Word.append] using
            derivesTripleExpansion (Word.singleton head)
      | cons next remaining =>
          simpa [Word.singleton, Word.append, Word.append_assoc] using
            Derives.appendRight
              (derivesTripleExpansion (Word.singleton head))
              (Word.mk next remaining)

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_15S4_96

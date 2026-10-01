import SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028
import SemigroupBasis.CoRoots.S5_869

/-!
# Final-relative S5_869/S5_871 transfer for the rank-028 five-law basis

The complete common lower-order basis has power, tail duplication, squared
prefix, and initial-gap axioms. The first two occur literally in the frozen
target. Its law 01 supplies guarded squared-prefix expansion. Guarded
initial-gap expansion is the association-fixed two-step chain

`xyxzt -> xyxzxzt -> xyxzxt`,

using displayed tail duplication followed by displayed law 03. A structural
induction consequently lifts every lower-order derivation under an arbitrary
nonempty final guard.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_871

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank028.basis

private def w (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

private def powerIdentity : Identity Nat :=
  ⟨w 0 [0], w 0 [0, 0]⟩

private def tailDuplicationIdentity : Identity Nat :=
  ⟨w 0 [1], w 0 [1, 1]⟩

private def squaredPrefixContractionIdentity : Identity Nat :=
  ⟨w 0 [0, 1, 0, 2], w 0 [0, 1, 2]⟩

private def alternatingContractionIdentity : Identity Nat :=
  ⟨w 0 [1, 0, 1, 2], w 0 [1, 0, 2]⟩

private theorem targetPower :
    Derives targetBasis powerIdentity.lhs powerIdentity.rhs :=
  Derives.fromBasis (e := powerIdentity) (by decide)

private theorem targetTailDuplication :
    Derives targetBasis
      tailDuplicationIdentity.lhs tailDuplicationIdentity.rhs :=
  Derives.fromBasis (e := tailDuplicationIdentity) (by decide)

private theorem targetSquaredPrefixContraction :
    Derives targetBasis
      squaredPrefixContractionIdentity.lhs
      squaredPrefixContractionIdentity.rhs :=
  Derives.fromBasis (e := squaredPrefixContractionIdentity) (by decide)

private theorem targetAlternatingContraction :
    Derives targetBasis
      alternatingContractionIdentity.lhs
      alternatingContractionIdentity.rhs :=
  Derives.fromBasis (e := alternatingContractionIdentity) (by decide)

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- Literal frozen tail duplication after arbitrary nonempty substitutions. -/
theorem derivesTailExpansion (first second : Word Nat) :
    Derives targetBasis
      (first ++ second) ((first ++ second) ++ second) := by
  have substituted :=
    Derives.subst targetTailDuplication
      (instantiateThreeWords first second second)
  simpa [tailDuplicationIdentity, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
    substituted

/-- Frozen law 01 supplies the squared-prefix axiom under a final guard. -/
theorem derivesSquaredPrefixRelative
    (first second guard : Word Nat) :
    Derives targetBasis
      (((first ++ first) ++ second) ++ guard)
      ((((first ++ first) ++ second) ++ first) ++ guard) := by
  have substituted :=
    Derives.subst targetSquaredPrefixContraction.symm
      (instantiateThreeWords first second guard)
  simpa [squaredPrefixContractionIdentity, w,
    instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- Frozen law 03 contracts an alternating block under its final guard. -/
private theorem derivesAlternatingContraction
    (first second guard : Word Nat) :
    Derives targetBasis
      ((((first ++ second) ++ first) ++ second) ++ guard)
      (((first ++ second) ++ first) ++ guard) := by
  have substituted :=
    Derives.subst targetAlternatingContraction
      (instantiateThreeWords first second guard)
  simpa [alternatingContractionIdentity, w,
    instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- The missing guarded initial-gap axiom has exactly two displayed steps:
tail-duplicate `xy · xz`, then contract the internal alternating block. -/
theorem derivesInitialGapRelative
    (first second third guard : Word Nat) :
    Derives targetBasis
      ((((first ++ second) ++ first) ++ third) ++ guard)
      (((((first ++ second) ++ first) ++ third) ++ first) ++ guard) := by
  have expanded :=
    Derives.appendRight
      (derivesTailExpansion (first ++ second) (first ++ third)) guard
  have contracted :=
    Derives.prepend (first ++ second)
      (derivesAlternatingContraction first third guard)
  exact Derives.trans
    (by simpa [Word.append_assoc] using expanded)
    (by simpa [Word.append_assoc] using contracted)

/-- Every axiom of the complete common S5_869/S5_871 basis lifts under an
arbitrary nonempty final guard. -/
theorem derivesS5_869AxiomRelative
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_869.basis)
    (guard : Word Nat) :
    Derives targetBasis
      (identity.lhs ++ guard) (identity.rhs ++ guard) := by
  simp only [SemigroupBasis.CoRoots.S5_869.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simpa [SemigroupBasis.CoRoots.S5_869.powerLaw,
      SemigroupBasis.CoRoots.S5_869.xx,
      SemigroupBasis.CoRoots.S5_869.xxx, powerIdentity, w] using
      Derives.appendRight targetPower guard
  · simpa [SemigroupBasis.CoRoots.S5_869.tailDuplicationLaw,
      SemigroupBasis.CoRoots.S5_869.xy,
      SemigroupBasis.CoRoots.S5_869.xyy,
      tailDuplicationIdentity, w] using
      Derives.appendRight targetTailDuplication guard
  · simpa [SemigroupBasis.CoRoots.S5_869.squaredPrefixLaw,
      SemigroupBasis.CoRoots.S5_869.xxy,
      SemigroupBasis.CoRoots.S5_869.xxyx,
      Word.singleton, Word.append, Word.append_assoc] using
      derivesSquaredPrefixRelative
        (Word.singleton 0) (Word.singleton 1) guard
  · simpa [SemigroupBasis.CoRoots.S5_869.initialGapLaw,
      SemigroupBasis.CoRoots.S5_869.xyxz,
      SemigroupBasis.CoRoots.S5_869.xyxzx,
      Word.singleton, Word.append, Word.append_assoc] using
      derivesInitialGapRelative
        (Word.singleton 0) (Word.singleton 1)
        (Word.singleton 2) guard

private def guardSubstitution
    (sigma : Nat → Word Nat) (guard : Word Nat) : Nat → Word Nat
  | 3 => guard
  | letter => sigma letter

/-- Fresh literal `3` is absent from all four complete lower-order axioms. -/
theorem liftS5_869AxiomUnderGuard
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_869.basis)
    (guard : Word Nat) (sigma : Nat → Word Nat) :
    Derives targetBasis
      (identity.lhs.bind sigma ++ guard)
      (identity.rhs.bind sigma ++ guard) := by
  have substituted :=
    Derives.subst
      (derivesS5_869AxiomRelative identity member (Word.singleton 3))
      (guardSubstitution sigma guard)
  simp only [SemigroupBasis.CoRoots.S5_869.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals
    simpa [SemigroupBasis.CoRoots.S5_869.powerLaw,
      SemigroupBasis.CoRoots.S5_869.tailDuplicationLaw,
      SemigroupBasis.CoRoots.S5_869.squaredPrefixLaw,
      SemigroupBasis.CoRoots.S5_869.initialGapLaw,
      SemigroupBasis.CoRoots.S5_869.xx,
      SemigroupBasis.CoRoots.S5_869.xxx,
      SemigroupBasis.CoRoots.S5_869.xy,
      SemigroupBasis.CoRoots.S5_869.xyy,
      SemigroupBasis.CoRoots.S5_869.xxy,
      SemigroupBasis.CoRoots.S5_869.xxyx,
      SemigroupBasis.CoRoots.S5_869.xyxz,
      SemigroupBasis.CoRoots.S5_869.xyxzx,
      guardSubstitution, Word.bind, Word.singleton,
      Word.append, Word.append_assoc] using substituted

private theorem bind_append
    (left right : Word Nat) (sigma : Nat → Word Nat) :
    (left ++ right).bind sigma = left.bind sigma ++ right.bind sigma := by
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

/-- Structural induction lifts every unrestricted lower-order derivation
before an arbitrary nonempty final guard and after any substitution. -/
theorem liftS5_869UnderGuard
    {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_869.basis left right)
    (guard : Word Nat) (sigma : Nat → Word Nat) :
    Derives targetBasis
      (left.bind sigma ++ guard) (right.bind sigma ++ guard) := by
  induction derivation generalizing guard sigma with
  | fromBasis member =>
      exact liftS5_869AxiomUnderGuard _ member guard sigma
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact (induction guard sigma).symm
  | trans _ _ first second =>
      exact (first guard sigma).trans (second guard sigma)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind sigma) (induction guard sigma)
  | appendRight _ appended induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (appended.bind sigma ++ guard) sigma
  | subst _ tau induction =>
      simpa [bind_bind] using
        induction guard (fun letter => (tau letter).bind sigma)

/-- Identity-substitution specialization of the structural relative lift. -/
theorem liftS5_869UnderGuardIdentity
    {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_869.basis left right)
    (guard : Word Nat) :
    Derives targetBasis (left ++ guard) (right ++ guard) := by
  simpa [bind_singleton] using
    liftS5_869UnderGuard derivation guard Word.singleton

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_871

import SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank025
import SemigroupBasis.CoRoots.S5_831Family

/-!
# Final-relative S5_831/S5_832 transfer for the rank-025 nine-law basis

The sealed common right-factor basis is `xx = xxx; xyx = xyy`.  Power is
literal target law 00; target law 05 is precisely copy under a nonempty final
guard.  Structural induction lifts all right-factor derivations uniformly.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_832

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank025.basis

private def w (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

private def powerIdentity : Identity Nat :=
  ⟨w 0 [0], w 0 [0, 0]⟩

private def copyRelativeIdentity : Identity Nat :=
  ⟨w 0 [1, 0, 2], w 0 [1, 1, 2]⟩

private def rightDuplicationIdentity : Identity Nat :=
  ⟨w 0 [1, 0], w 0 [1, 0, 0]⟩

private theorem targetPower :
    Derives targetBasis powerIdentity.lhs powerIdentity.rhs :=
  Derives.fromBasis (e := powerIdentity) (by decide)

private theorem targetCopyRelative :
    Derives targetBasis copyRelativeIdentity.lhs copyRelativeIdentity.rhs :=
  Derives.fromBasis (e := copyRelativeIdentity) (by decide)

private theorem targetRightDuplication :
    Derives targetBasis
      rightDuplicationIdentity.lhs rightDuplicationIdentity.rhs :=
  Derives.fromBasis (e := rightDuplicationIdentity) (by decide)

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- The frozen rank-025 unary power law after arbitrary whole-word substitution. -/
theorem derivesPower (word : Word Nat) :
    Derives targetBasis (word ++ word) ((word ++ word) ++ word) := by
  have substituted :=
    Derives.subst targetPower (instantiateThreeWords word word word)
  simpa [powerIdentity, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using substituted

/-- Frozen law 01 duplicates the common final when that variable is repeated. -/
theorem derivesRightDuplication (word middle : Word Nat) :
    Derives targetBasis
      ((word ++ middle) ++ word)
      (((word ++ middle) ++ word) ++ word) := by
  have substituted :=
    Derives.subst targetRightDuplication
      (instantiateThreeWords word middle middle)
  simpa [rightDuplicationIdentity, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using substituted

/-- Frozen law 05 is the exact lower-order copy law under any nonempty guard. -/
theorem derivesCopyRelative
    (first second guard : Word Nat) :
    Derives targetBasis
      (((first ++ second) ++ first) ++ guard)
      (((first ++ second) ++ second) ++ guard) := by
  have substituted :=
    Derives.subst targetCopyRelative
      (instantiateThreeWords first second guard)
  simpa [copyRelativeIdentity, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using substituted

/-- Each axiom of the complete common S5_831/S5_832 basis lifts relative to
an arbitrary nonempty final guard. -/
theorem derivesS5_831AxiomRelative
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_831.basis)
    (guard : Word Nat) :
    Derives targetBasis
      (identity.lhs ++ guard) (identity.rhs ++ guard) := by
  simp only [SemigroupBasis.CoRoots.S5_831.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simpa [SemigroupBasis.CoRoots.S5_831.powerLaw,
      SemigroupBasis.CoRoots.S5_831.xx,
      SemigroupBasis.CoRoots.S5_831.xxx,
      powerIdentity, w] using
      Derives.appendRight targetPower guard
  · simpa [SemigroupBasis.CoRoots.S5_831.copyLaw,
      SemigroupBasis.CoRoots.S5_831.xyx,
      SemigroupBasis.CoRoots.S5_831.xyy,
      Word.singleton, Word.append, Word.append_assoc] using
      derivesCopyRelative (Word.singleton 0) (Word.singleton 1) guard

private def guardSubstitution
    (sigma : Nat → Word Nat) (guard : Word Nat) : Nat → Word Nat
  | 2 => guard
  | letter => sigma letter

/-- Fresh variable `2` is absent from both common lower-order axioms. -/
theorem liftS5_831AxiomUnderGuard
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_831.basis)
    (guard : Word Nat) (sigma : Nat → Word Nat) :
    Derives targetBasis
      (identity.lhs.bind sigma ++ guard)
      (identity.rhs.bind sigma ++ guard) := by
  have substituted :=
    Derives.subst
      (derivesS5_831AxiomRelative identity member (Word.singleton 2))
      (guardSubstitution sigma guard)
  simp only [SemigroupBasis.CoRoots.S5_831.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals
    simpa [SemigroupBasis.CoRoots.S5_831.powerLaw,
      SemigroupBasis.CoRoots.S5_831.copyLaw,
      SemigroupBasis.CoRoots.S5_831.xx,
      SemigroupBasis.CoRoots.S5_831.xxx,
      SemigroupBasis.CoRoots.S5_831.xyx,
      SemigroupBasis.CoRoots.S5_831.xyy,
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

/-- Structural induction lifts every unrestricted common right-factor
derivation before an arbitrary nonempty final guard. -/
theorem liftS5_831UnderGuard
    {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_831.basis left right)
    (guard : Word Nat) (sigma : Nat → Word Nat) :
    Derives targetBasis
      (left.bind sigma ++ guard) (right.bind sigma ++ guard) := by
  induction derivation generalizing guard sigma with
  | fromBasis member =>
      exact liftS5_831AxiomUnderGuard _ member guard sigma
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
theorem liftS5_831UnderGuardIdentity
    {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_831.basis left right)
    (guard : Word Nat) :
    Derives targetBasis (left ++ guard) (right ++ guard) := by
  simpa [bind_singleton] using
    liftS5_831UnderGuard derivation guard Word.singleton

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_832

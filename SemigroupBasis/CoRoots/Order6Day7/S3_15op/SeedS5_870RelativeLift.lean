import SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank066
import SemigroupBasis.CoRoots.S5_870

/-!
# Final-relative S5_870 transfer for the frozen rank-066 ten-law basis

The complete S5_870 gap-signature basis has eight cap/sort laws. Its two
final-preserving cap laws occur literally in rank 066; each of the other six
laws occurs as an exact displayed law after adjoining a fresh final guard.
Structural induction therefore lifts every unrestricted S5_870 derivation
under an arbitrary nonempty final guard. No finite-alphabet hypothesis or
semantic transport shortcut is used.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_870

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank066.basis

private def w (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

private def capBothIdentity : Identity Nat :=
  ⟨w 0 [0, 0], w 0 [0]⟩

private def capFinalIdentity : Identity Nat :=
  ⟨w 0 [1, 0, 0], w 0 [1, 0]⟩

private def capInitialRelativeIdentity : Identity Nat :=
  ⟨w 0 [0, 1, 0, 2], w 0 [0, 1, 2]⟩

private def capGeneralRelativeIdentity : Identity Nat :=
  ⟨w 0 [1, 0, 2, 0, 3], w 0 [1, 0, 2, 3]⟩

private def sortBothRelativeIdentity : Identity Nat :=
  ⟨w 0 [1, 0, 1, 2], w 0 [1, 1, 0, 2]⟩

private def sortInitialRelativeIdentity : Identity Nat :=
  ⟨w 0 [1, 2, 0, 1, 3], w 0 [1, 2, 1, 0, 3]⟩

private def sortFinalRelativeIdentity : Identity Nat :=
  ⟨w 0 [1, 2, 0, 2, 3], w 0 [1, 2, 2, 0, 3]⟩

private def sortGeneralRelativeIdentity : Identity Nat :=
  ⟨w 0 [1, 2, 3, 0, 2, 4], w 0 [1, 2, 3, 2, 0, 4]⟩

private theorem targetCapBoth :
    Derives targetBasis capBothIdentity.lhs capBothIdentity.rhs :=
  Derives.fromBasis (e := capBothIdentity) (by decide)

private theorem targetCapFinal :
    Derives targetBasis capFinalIdentity.lhs capFinalIdentity.rhs :=
  Derives.fromBasis (e := capFinalIdentity) (by decide)

private theorem targetCapInitialRelative :
    Derives targetBasis
      capInitialRelativeIdentity.lhs capInitialRelativeIdentity.rhs :=
  Derives.fromBasis (e := capInitialRelativeIdentity) (by decide)

private theorem targetCapGeneralRelative :
    Derives targetBasis
      capGeneralRelativeIdentity.lhs capGeneralRelativeIdentity.rhs :=
  Derives.fromBasis (e := capGeneralRelativeIdentity) (by decide)

private theorem targetSortBothRelative :
    Derives targetBasis
      sortBothRelativeIdentity.lhs sortBothRelativeIdentity.rhs :=
  Derives.fromBasis (e := sortBothRelativeIdentity) (by decide)

private theorem targetSortInitialRelative :
    Derives targetBasis
      sortInitialRelativeIdentity.lhs sortInitialRelativeIdentity.rhs :=
  Derives.fromBasis (e := sortInitialRelativeIdentity) (by decide)

private theorem targetSortFinalRelative :
    Derives targetBasis
      sortFinalRelativeIdentity.lhs sortFinalRelativeIdentity.rhs :=
  Derives.fromBasis (e := sortFinalRelativeIdentity) (by decide)

private theorem targetSortGeneralRelative :
    Derives targetBasis
      sortGeneralRelativeIdentity.lhs sortGeneralRelativeIdentity.rhs :=
  Derives.fromBasis (e := sortGeneralRelativeIdentity) (by decide)

private def instantiateFiveWords
    (first second third fourth fifth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | 4 => fifth
  | letter + 5 => Word.singleton (letter + 5)

/-- Literal rank-066 power contraction, used in its expansion direction. -/
theorem derivesPower (first : Word Nat) :
    Derives targetBasis
      (first ++ first) ((first ++ first) ++ first) := by
  have substituted :=
    Derives.subst targetCapBoth.symm
      (instantiateFiveWords first first first first first)
  simpa [capBothIdentity, w, instantiateFiveWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
    substituted

/-- Literal rank-066 final-gap cap duplicates an already repeated final. -/
theorem derivesRightExpansion (first second : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ first)
      (((first ++ second) ++ first) ++ first) := by
  have substituted :=
    Derives.subst targetCapFinal.symm
      (instantiateFiveWords first second second second second)
  simpa [capFinalIdentity, w, instantiateFiveWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
    substituted

/-- Each exact gap-signature axiom is present literally or as its one-step
rank-066 displayed version with an arbitrary nonempty final guard. -/
theorem derivesS5_870AxiomRelative
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_870.basis)
    (guard : Word Nat) :
    Derives targetBasis
      (identity.lhs ++ guard) (identity.rhs ++ guard) := by
  simp only [SemigroupBasis.CoRoots.S5_870.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [SemigroupBasis.CoRoots.S5_870.capBothEmptyLaw,
      SemigroupBasis.CoRoots.S5_870.xxx,
      SemigroupBasis.CoRoots.S5_870.xx, capBothIdentity, w] using
      Derives.appendRight targetCapBoth guard
  · have substituted :=
      Derives.subst targetCapInitialRelative
        (instantiateFiveWords
          (Word.singleton 0) (Word.singleton 3) guard guard guard)
    simpa [SemigroupBasis.CoRoots.S5_870.capInitialGapEmptyLaw,
      SemigroupBasis.CoRoots.S5_870.xxtx,
      SemigroupBasis.CoRoots.S5_870.xxt,
      capInitialRelativeIdentity, w, instantiateFiveWords,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using
      substituted
  · simpa [SemigroupBasis.CoRoots.S5_870.capFinalGapEmptyLaw,
      SemigroupBasis.CoRoots.S5_870.xhxx,
      SemigroupBasis.CoRoots.S5_870.xhx, capFinalIdentity, w] using
      Derives.appendRight targetCapFinal guard
  · have substituted :=
      Derives.subst targetCapGeneralRelative
        (instantiateFiveWords (Word.singleton 0) (Word.singleton 1)
          (Word.singleton 3) guard guard)
    simpa [SemigroupBasis.CoRoots.S5_870.capGeneralLaw,
      SemigroupBasis.CoRoots.S5_870.xhxtx,
      SemigroupBasis.CoRoots.S5_870.xhxt,
      capGeneralRelativeIdentity, w, instantiateFiveWords,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using
      substituted
  · have substituted :=
      Derives.subst targetSortBothRelative
        (instantiateFiveWords
          (Word.singleton 0) (Word.singleton 2) guard guard guard)
    simpa [SemigroupBasis.CoRoots.S5_870.sortBothEmptyLaw,
      SemigroupBasis.CoRoots.S5_870.xyxy,
      SemigroupBasis.CoRoots.S5_870.xyyx,
      sortBothRelativeIdentity, w, instantiateFiveWords,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using
      substituted
  · have substituted :=
      Derives.subst targetSortInitialRelative
        (instantiateFiveWords (Word.singleton 0) (Word.singleton 2)
          (Word.singleton 3) guard guard)
    simpa [SemigroupBasis.CoRoots.S5_870.sortInitialGapEmptyLaw,
      SemigroupBasis.CoRoots.S5_870.xytxy,
      SemigroupBasis.CoRoots.S5_870.xytyx,
      sortInitialRelativeIdentity, w, instantiateFiveWords,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using
      substituted
  · have substituted :=
      Derives.subst targetSortFinalRelative
        (instantiateFiveWords (Word.singleton 0) (Word.singleton 1)
          (Word.singleton 2) guard guard)
    simpa [SemigroupBasis.CoRoots.S5_870.sortFinalGapEmptyLaw,
      SemigroupBasis.CoRoots.S5_870.xhyxy,
      SemigroupBasis.CoRoots.S5_870.xhyyx,
      sortFinalRelativeIdentity, w, instantiateFiveWords,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using
      substituted
  · have substituted :=
      Derives.subst targetSortGeneralRelative
        (instantiateFiveWords (Word.singleton 0) (Word.singleton 1)
          (Word.singleton 2) (Word.singleton 3) guard)
    simpa [SemigroupBasis.CoRoots.S5_870.sortGeneralLaw,
      SemigroupBasis.CoRoots.S5_870.xhytxy,
      SemigroupBasis.CoRoots.S5_870.xhytyx,
      sortGeneralRelativeIdentity, w, instantiateFiveWords,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using
      substituted

private def guardSubstitution
    (sigma : Nat → Word Nat) (guard : Word Nat) : Nat → Word Nat
  | 4 => guard
  | letter => sigma letter

/-- Fresh literal `4` occurs in none of the complete eight lower-order laws. -/
theorem liftS5_870AxiomUnderGuard
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_870.basis)
    (guard : Word Nat) (sigma : Nat → Word Nat) :
    Derives targetBasis
      (identity.lhs.bind sigma ++ guard)
      (identity.rhs.bind sigma ++ guard) := by
  have substituted :=
    Derives.subst
      (derivesS5_870AxiomRelative identity member (Word.singleton 4))
      (guardSubstitution sigma guard)
  simp only [SemigroupBasis.CoRoots.S5_870.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simpa [SemigroupBasis.CoRoots.S5_870.capBothEmptyLaw,
      SemigroupBasis.CoRoots.S5_870.capInitialGapEmptyLaw,
      SemigroupBasis.CoRoots.S5_870.capFinalGapEmptyLaw,
      SemigroupBasis.CoRoots.S5_870.capGeneralLaw,
      SemigroupBasis.CoRoots.S5_870.sortBothEmptyLaw,
      SemigroupBasis.CoRoots.S5_870.sortInitialGapEmptyLaw,
      SemigroupBasis.CoRoots.S5_870.sortFinalGapEmptyLaw,
      SemigroupBasis.CoRoots.S5_870.sortGeneralLaw,
      SemigroupBasis.CoRoots.S5_870.xx,
      SemigroupBasis.CoRoots.S5_870.xxx,
      SemigroupBasis.CoRoots.S5_870.xxtx,
      SemigroupBasis.CoRoots.S5_870.xxt,
      SemigroupBasis.CoRoots.S5_870.xhxx,
      SemigroupBasis.CoRoots.S5_870.xhx,
      SemigroupBasis.CoRoots.S5_870.xhxtx,
      SemigroupBasis.CoRoots.S5_870.xhxt,
      SemigroupBasis.CoRoots.S5_870.xyxy,
      SemigroupBasis.CoRoots.S5_870.xyyx,
      SemigroupBasis.CoRoots.S5_870.xytxy,
      SemigroupBasis.CoRoots.S5_870.xytyx,
      SemigroupBasis.CoRoots.S5_870.xhyxy,
      SemigroupBasis.CoRoots.S5_870.xhyyx,
      SemigroupBasis.CoRoots.S5_870.xhytxy,
      SemigroupBasis.CoRoots.S5_870.xhytyx,
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

/-- Every unrestricted S5_870 derivation survives an arbitrary final guard. -/
theorem liftS5_870UnderGuard
    {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_870.basis left right)
    (guard : Word Nat) (sigma : Nat → Word Nat) :
    Derives targetBasis
      (left.bind sigma ++ guard) (right.bind sigma ++ guard) := by
  induction derivation generalizing guard sigma with
  | fromBasis member =>
      exact liftS5_870AxiomUnderGuard _ member guard sigma
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
theorem liftS5_870UnderGuardIdentity
    {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_870.basis left right)
    (guard : Word Nat) :
    Derives targetBasis (left ++ guard) (right ++ guard) := by
  simpa [bind_singleton] using
    liftS5_870UnderGuard derivation guard Word.singleton

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_870

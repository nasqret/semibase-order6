import SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank027
import SemigroupBasis.CoRoots.S5_848

/-!
# Final-relative `S5_848` transport for the exact rank-027 six-law family

The exact `S5_848` axioms are power, gather, and tail-square promotion. Power
and tail-square promotion occur literally in the target. Its fourth displayed
law `xxyz = xyxz` is the missing gather axiom under an arbitrary nonempty
final guard.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_848

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) :=
  Rank027.basis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def powerIdentity : Identity Nat :=
  ⟨w 0 [0], w 0 [0, 0]⟩

private def gatherRelativeIdentity : Identity Nat :=
  ⟨w 0 [0, 1, 2], w 0 [1, 0, 2]⟩

private def rightDuplicationIdentity : Identity Nat :=
  ⟨w 0 [1, 0], w 0 [1, 0, 0]⟩

private def tailSquareIdentity : Identity Nat :=
  ⟨w 0 [1, 1, 2, 2], w 0 [2, 1, 1, 2]⟩

private theorem targetPower :
    Derives targetBasis powerIdentity.lhs powerIdentity.rhs :=
  Derives.fromBasis (e := powerIdentity) (by decide)

private theorem targetGatherRelative :
    Derives targetBasis
      gatherRelativeIdentity.lhs gatherRelativeIdentity.rhs :=
  Derives.fromBasis (e := gatherRelativeIdentity) (by decide)

private theorem targetRightDuplication :
    Derives targetBasis
      rightDuplicationIdentity.lhs rightDuplicationIdentity.rhs :=
  Derives.fromBasis (e := rightDuplicationIdentity) (by decide)

private theorem targetTailSquare :
    Derives targetBasis tailSquareIdentity.lhs tailSquareIdentity.rhs :=
  Derives.fromBasis (e := tailSquareIdentity) (by decide)

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- Substitute any nonempty word into the literal displayed power law. -/
theorem derivesPower (word : Word Nat) :
    Derives targetBasis (word ++ word) ((word ++ word) ++ word) := by
  have substituted :=
    Derives.subst targetPower
      (instantiateThreeWords word word word)
  simpa [powerIdentity, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
    substituted

/-- Substitute arbitrary nonempty words into the literal final duplication
law `xyx = xyxx`. -/
theorem derivesRightDuplication (word middle : Word Nat) :
    Derives targetBasis
      ((word ++ middle) ++ word)
      (((word ++ middle) ++ word) ++ word) := by
  have substituted :=
    Derives.subst targetRightDuplication
      (instantiateThreeWords word middle middle)
  simpa [rightDuplicationIdentity, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
    substituted

/-- The displayed `xxyz = xyxz` is precisely gather under a nonempty suffix. -/
theorem derivesGatherRelative
    (first second suffix : Word Nat) :
    Derives targetBasis
      (((first ++ first) ++ second) ++ suffix)
      (((first ++ second) ++ first) ++ suffix) := by
  have substituted :=
    Derives.subst targetGatherRelative
      (instantiateThreeWords first second suffix)
  simpa [gatherRelativeIdentity, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
    substituted

/-- All three axioms of the independently complete exact `S5_848` basis
are derivable immediately before an arbitrary nonempty final guard. -/
theorem derivesS5_848AxiomRelative
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_848.basis)
    (suffix : Word Nat) :
    Derives targetBasis
      (identity.lhs ++ suffix) (identity.rhs ++ suffix) := by
  simp only [SemigroupBasis.CoRoots.S5_848.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · simpa [SemigroupBasis.CoRoots.S5_848.powerLaw,
      SemigroupBasis.CoRoots.S5_848.xx,
      SemigroupBasis.CoRoots.S5_848.xxx,
      powerIdentity, w] using
      Derives.appendRight targetPower suffix
  · simpa [SemigroupBasis.CoRoots.S5_848.gatherLaw,
      SemigroupBasis.CoRoots.S5_848.xxy,
      SemigroupBasis.CoRoots.S5_848.xyx,
      Word.singleton, Word.append, Word.append_assoc] using
      derivesGatherRelative (Word.singleton 0) (Word.singleton 1) suffix
  · simpa [SemigroupBasis.CoRoots.S5_848.tailSquarePromotionLaw,
      SemigroupBasis.CoRoots.S5_848.xyyzz,
      SemigroupBasis.CoRoots.S5_848.xzyyz,
      tailSquareIdentity, w] using
      Derives.appendRight targetTailSquare suffix

private def suffixSubstitution
    (sigma : Nat → Word Nat) (suffix : Word Nat) : Nat → Word Nat
  | 3 => suffix
  | letter => sigma letter

/-- Fresh variable `3`, absent from the exact three source axioms, binds the
nonempty suffix during unrestricted whole-word substitution. -/
theorem liftS5_848AxiomUnderSuffix
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_848.basis)
    (suffix : Word Nat) (sigma : Nat → Word Nat) :
    Derives targetBasis
      (identity.lhs.bind sigma ++ suffix)
      (identity.rhs.bind sigma ++ suffix) := by
  have substituted :=
    Derives.subst
      (derivesS5_848AxiomRelative identity member (Word.singleton 3))
      (suffixSubstitution sigma suffix)
  simp only [SemigroupBasis.CoRoots.S5_848.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    simpa [SemigroupBasis.CoRoots.S5_848.powerLaw,
      SemigroupBasis.CoRoots.S5_848.gatherLaw,
      SemigroupBasis.CoRoots.S5_848.tailSquarePromotionLaw,
      SemigroupBasis.CoRoots.S5_848.xx,
      SemigroupBasis.CoRoots.S5_848.xxx,
      SemigroupBasis.CoRoots.S5_848.xxy,
      SemigroupBasis.CoRoots.S5_848.xyx,
      SemigroupBasis.CoRoots.S5_848.xyyzz,
      SemigroupBasis.CoRoots.S5_848.xzyyz,
      suffixSubstitution, Word.bind, Word.singleton,
      Word.append, Word.append_assoc] using substituted

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

/-- Every unrestricted `S5_848` derivation lifts before an arbitrary fixed
nonempty suffix and after an arbitrary nonempty-word substitution. -/
theorem liftS5_848UnderSuffix
    {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_848.basis left right)
    (suffix : Word Nat) (sigma : Nat → Word Nat) :
    Derives targetBasis
      (left.bind sigma ++ suffix) (right.bind sigma ++ suffix) := by
  induction derivation generalizing suffix sigma with
  | fromBasis member =>
      exact liftS5_848AxiomUnderSuffix _ member suffix sigma
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact (induction suffix sigma).symm
  | trans _ _ first second =>
      exact (first suffix sigma).trans (second suffix sigma)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind sigma) (induction suffix sigma)
  | appendRight _ appended induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (appended.bind sigma ++ suffix) sigma
  | subst _ tau induction =>
      simpa [bind_bind] using
        induction suffix (fun letter => (tau letter).bind sigma)

/-- Identity-substitution specialization of the exact final-relative lift. -/
theorem liftS5_848UnderSuffixIdentity
    {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_848.basis left right)
    (suffix : Word Nat) :
    Derives targetBasis (left ++ suffix) (right ++ suffix) := by
  simpa [bind_singleton] using
    liftS5_848UnderSuffix derivation suffix Word.singleton

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_848

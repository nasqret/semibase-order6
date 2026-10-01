import SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank057
import SemigroupBasis.CoRoots.S5_516

/-!
# Final-relative S5_516 transfer for the frozen rank-057 seven-law basis

All seven independently complete S5_516 axioms lift under a nonempty final
guard. The only nonliteral axiom is suffix commutation, supplied by the
association-fixed four-step displayed chain

`xyzt -> xyyzt -> xzyzt -> xzzyt -> xzyt`.

Every word of length at least three can additionally duplicate its final via
the association-fixed three-step chain `xyz -> xyyz -> xyyzz -> xyzz`.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_516

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank057.basis

private def w (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

private def powerIdentity : Identity Nat :=
  ⟨w 0 [0, 0], w 0 [0, 0, 0]⟩

private def prefixContractionIdentity : Identity Nat :=
  ⟨w 0 [0, 0, 1], w 0 [0, 1]⟩

private def squareTailDuplicationIdentity : Identity Nat :=
  ⟨w 0 [0, 1], w 0 [0, 1, 1]⟩

private def initialSwitchIdentity : Identity Nat :=
  ⟨w 0 [0, 1], w 1 [0, 1]⟩

private def gatherRelativeIdentity : Identity Nat :=
  ⟨w 0 [0, 1, 2], w 0 [1, 0, 2]⟩

private def suffixPowerIdentity : Identity Nat :=
  ⟨w 0 [1, 1], w 0 [1, 1, 1]⟩

private def middleContractionIdentity : Identity Nat :=
  ⟨w 0 [1, 1, 2], w 0 [1, 2]⟩

private theorem targetPower :
    Derives targetBasis powerIdentity.lhs powerIdentity.rhs :=
  Derives.fromBasis (e := powerIdentity) (by decide)

private theorem targetPrefixContraction :
    Derives targetBasis
      prefixContractionIdentity.lhs prefixContractionIdentity.rhs :=
  Derives.fromBasis (e := prefixContractionIdentity) (by decide)

private theorem targetSquareTailDuplication :
    Derives targetBasis
      squareTailDuplicationIdentity.lhs
      squareTailDuplicationIdentity.rhs :=
  Derives.fromBasis (e := squareTailDuplicationIdentity) (by decide)

private theorem targetInitialSwitch :
    Derives targetBasis
      initialSwitchIdentity.lhs initialSwitchIdentity.rhs :=
  Derives.fromBasis (e := initialSwitchIdentity) (by decide)

private theorem targetGatherRelative :
    Derives targetBasis
      gatherRelativeIdentity.lhs gatherRelativeIdentity.rhs :=
  Derives.fromBasis (e := gatherRelativeIdentity) (by decide)

private theorem targetSuffixPower :
    Derives targetBasis suffixPowerIdentity.lhs suffixPowerIdentity.rhs :=
  Derives.fromBasis (e := suffixPowerIdentity) (by decide)

private theorem targetMiddleContraction :
    Derives targetBasis
      middleContractionIdentity.lhs middleContractionIdentity.rhs :=
  Derives.fromBasis (e := middleContractionIdentity) (by decide)

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- Displayed law 06 inserts a second copy of any nonempty middle block. -/
theorem derivesMiddleExpansion
    (first second third : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ third)
      (((first ++ second) ++ second) ++ third) := by
  have substituted :=
    Derives.subst targetMiddleContraction.symm
      (instantiateThreeWords first second third)
  simpa [middleContractionIdentity, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
    substituted

/-- Displayed law 02 duplicates the tail after a squared prefix block. -/
theorem derivesSquareTailExpansion
    (first second : Word Nat) :
    Derives targetBasis
      ((first ++ first) ++ second)
      (((first ++ first) ++ second) ++ second) := by
  have substituted :=
    Derives.subst targetSquareTailDuplication
      (instantiateThreeWords first second second)
  simpa [squareTailDuplicationIdentity, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
    substituted

/-- Displayed law 03 switches the initial block of a squared prefix. -/
theorem derivesInitialSwitch
    (first second : Word Nat) :
    Derives targetBasis
      ((first ++ first) ++ second)
      ((second ++ first) ++ second) := by
  have substituted :=
    Derives.subst targetInitialSwitch
      (instantiateThreeWords first second second)
  simpa [initialSwitchIdentity, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
    substituted

/-- Displayed law 04 is exactly lower-order gather under a final guard. -/
theorem derivesGatherRelative
    (first second guard : Word Nat) :
    Derives targetBasis
      (((first ++ first) ++ second) ++ guard)
      (((first ++ second) ++ first) ++ guard) := by
  have substituted :=
    Derives.subst targetGatherRelative
      (instantiateThreeWords first second guard)
  simpa [gatherRelativeIdentity, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
    substituted

/-- The complete S5_516 suffix-commutation axiom is recovered under its
final guard by four association-fixed displayed rewrites. -/
theorem derivesSuffixSwapRelative
    (first second third guard : Word Nat) :
    Derives targetBasis
      (((first ++ second) ++ third) ++ guard)
      (((first ++ third) ++ second) ++ guard) := by
  have duplicate :=
    Derives.appendRight
      (derivesMiddleExpansion first second third) guard
  have switched :=
    Derives.appendRight
      (Derives.prepend first (derivesInitialSwitch second third)) guard
  have gathered :=
    Derives.prepend first
      (derivesGatherRelative third second guard).symm
  have contracted :=
    Derives.appendRight
      (derivesMiddleExpansion first third second).symm guard
  exact Derives.trans
    (by simpa [Word.append_assoc] using duplicate) <|
    Derives.trans
      (by simpa [Word.append_assoc] using switched) <|
      Derives.trans
        (by simpa [Word.append_assoc] using gathered)
        (by simpa [Word.append_assoc] using contracted)

/-- Every word expressed as three nonempty blocks duplicates its final block
using exactly three frozen displayed rewrites. -/
theorem derivesFinalDuplicationTriple
    (first middle final : Word Nat) :
    Derives targetBasis
      ((first ++ middle) ++ final)
      (((first ++ middle) ++ final) ++ final) := by
  have duplicateMiddle :=
    derivesMiddleExpansion first middle final
  have duplicateFinal :=
    Derives.prepend first (derivesSquareTailExpansion middle final)
  have contractMiddle :=
    (derivesMiddleExpansion first middle (final ++ final)).symm
  exact Derives.trans
    (by simpa [Word.append_assoc] using duplicateMiddle) <|
    Derives.trans
      (by simpa [Word.append_assoc] using duplicateFinal)
      (by simpa [Word.append_assoc] using contractMiddle)

/-- Each of the seven exact lower-order axioms lifts under any nonempty
final guard, without a bounded-alphabet or completeness assumption. -/
theorem derivesS5_516AxiomRelative
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_516.basis)
    (guard : Word Nat) :
    Derives targetBasis
      (identity.lhs ++ guard) (identity.rhs ++ guard) := by
  simp only [SemigroupBasis.CoRoots.S5_516.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [SemigroupBasis.CoRoots.S5_516.powerLaw,
      SemigroupBasis.CoRoots.S5_516.xxx,
      SemigroupBasis.CoRoots.S5_516.xxxx, powerIdentity, w] using
      Derives.appendRight targetPower guard
  · simpa [SemigroupBasis.CoRoots.S5_516.gatherLaw,
      SemigroupBasis.CoRoots.S5_516.xxy,
      SemigroupBasis.CoRoots.S5_516.xyx,
      Word.singleton, Word.append, Word.append_assoc] using
      derivesGatherRelative
        (Word.singleton 0) (Word.singleton 1) guard
  · simpa [SemigroupBasis.CoRoots.S5_516.initialSwitchLaw,
      SemigroupBasis.CoRoots.S5_516.xxy,
      SemigroupBasis.CoRoots.S5_516.yxy,
      initialSwitchIdentity, w] using
      Derives.appendRight targetInitialSwitch guard
  · simpa [SemigroupBasis.CoRoots.S5_516.prefixPowerLaw,
      SemigroupBasis.CoRoots.S5_516.xxy,
      SemigroupBasis.CoRoots.S5_516.xxxy,
      prefixContractionIdentity, w] using
      Derives.appendRight targetPrefixContraction.symm guard
  · simpa [SemigroupBasis.CoRoots.S5_516.suffixPowerLaw,
      SemigroupBasis.CoRoots.S5_516.xyy,
      SemigroupBasis.CoRoots.S5_516.xyyy,
      suffixPowerIdentity, w] using
      Derives.appendRight targetSuffixPower guard
  · simpa [SemigroupBasis.CoRoots.S5_516.suffixCommutationLaw,
      SemigroupBasis.CoRoots.S5_516.xyz,
      SemigroupBasis.CoRoots.S5_516.xzy,
      Word.singleton, Word.append, Word.append_assoc] using
      derivesSuffixSwapRelative
        (Word.singleton 0) (Word.singleton 1)
        (Word.singleton 2) guard
  · simpa [SemigroupBasis.CoRoots.S5_516.middleDuplicationLaw,
      SemigroupBasis.CoRoots.S5_516.xyz,
      SemigroupBasis.CoRoots.S5_516.xyyz,
      Word.singleton, Word.append, Word.append_assoc] using
      Derives.appendRight
        (derivesMiddleExpansion
          (Word.singleton 0) (Word.singleton 1) (Word.singleton 2))
        guard

private def guardSubstitution
    (sigma : Nat → Word Nat) (guard : Word Nat) : Nat → Word Nat
  | 3 => guard
  | letter => sigma letter

/-- Fresh literal `3` is absent from all seven S5_516 lower-order axioms. -/
theorem liftS5_516AxiomUnderGuard
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_516.basis)
    (guard : Word Nat) (sigma : Nat → Word Nat) :
    Derives targetBasis
      (identity.lhs.bind sigma ++ guard)
      (identity.rhs.bind sigma ++ guard) := by
  have substituted :=
    Derives.subst
      (derivesS5_516AxiomRelative identity member (Word.singleton 3))
      (guardSubstitution sigma guard)
  simp only [SemigroupBasis.CoRoots.S5_516.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simpa [SemigroupBasis.CoRoots.S5_516.powerLaw,
      SemigroupBasis.CoRoots.S5_516.gatherLaw,
      SemigroupBasis.CoRoots.S5_516.initialSwitchLaw,
      SemigroupBasis.CoRoots.S5_516.prefixPowerLaw,
      SemigroupBasis.CoRoots.S5_516.suffixPowerLaw,
      SemigroupBasis.CoRoots.S5_516.suffixCommutationLaw,
      SemigroupBasis.CoRoots.S5_516.middleDuplicationLaw,
      SemigroupBasis.CoRoots.S5_516.xxx,
      SemigroupBasis.CoRoots.S5_516.xxxx,
      SemigroupBasis.CoRoots.S5_516.xxy,
      SemigroupBasis.CoRoots.S5_516.xyx,
      SemigroupBasis.CoRoots.S5_516.yxy,
      SemigroupBasis.CoRoots.S5_516.xxxy,
      SemigroupBasis.CoRoots.S5_516.xyy,
      SemigroupBasis.CoRoots.S5_516.xyyy,
      SemigroupBasis.CoRoots.S5_516.xyz,
      SemigroupBasis.CoRoots.S5_516.xzy,
      SemigroupBasis.CoRoots.S5_516.xyyz,
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

/-- Structural induction lifts every unrestricted complete S5_516 derivation
under an arbitrary nonempty final guard and whole-word substitution. -/
theorem liftS5_516UnderGuard
    {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_516.basis left right)
    (guard : Word Nat) (sigma : Nat → Word Nat) :
    Derives targetBasis
      (left.bind sigma ++ guard) (right.bind sigma ++ guard) := by
  induction derivation generalizing guard sigma with
  | fromBasis member =>
      exact liftS5_516AxiomUnderGuard _ member guard sigma
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
theorem liftS5_516UnderGuardIdentity
    {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_516.basis left right)
    (guard : Word Nat) :
    Derives targetBasis (left ++ guard) (right ++ guard) := by
  simpa [bind_singleton] using
    liftS5_516UnderGuard derivation guard Word.singleton

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_516

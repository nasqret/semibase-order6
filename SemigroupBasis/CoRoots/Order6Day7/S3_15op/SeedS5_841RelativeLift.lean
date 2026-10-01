import SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank064
import SemigroupBasis.CoRoots.S5_841

/-!
# Final-relative M20/S5_841 transfer for the rank-064 eight-law basis

All twelve independently complete S5_841 axioms are lifted under a nonempty
final guard. Four nonliteral obligations use explicit association-fixed
target-law chains: long rotation (five steps), long context swap (three),
terminal square (three), and short rotation (four). No finite alphabet bound
or semantic shortcut is used.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_841

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank064.basis

private def w (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

private def powerIdentity : Identity Nat := ⟨w 0 [0], w 0 [0, 0]⟩
private def leftDeletionIdentity : Identity Nat :=
  ⟨w 0 [0, 1, 0], w 0 [1, 0]⟩
private def rightExpansionIdentity : Identity Nat :=
  ⟨w 0 [1, 0], w 0 [1, 0, 0]⟩
private def shortSwapIdentity : Identity Nat :=
  ⟨w 0 [1, 0, 1], w 1 [0, 0, 1]⟩
private def alternatingSwapIdentity : Identity Nat :=
  ⟨w 0 [1, 0, 1, 2], w 0 [1, 1, 0, 2]⟩
private def middleDeletionIdentity : Identity Nat :=
  ⟨w 0 [1, 0, 2, 0], w 0 [1, 2, 0]⟩
private def rightContextSwapIdentity : Identity Nat :=
  ⟨w 0 [1, 0, 2, 1], w 1 [0, 0, 2, 1]⟩
private def terminalContextSwapIdentity : Identity Nat :=
  ⟨w 0 [1, 2, 0, 1], w 1 [0, 2, 0, 1]⟩

private theorem targetPower :
    Derives targetBasis powerIdentity.lhs powerIdentity.rhs :=
  Derives.fromBasis (e := powerIdentity) (by decide)

private theorem targetLeftDeletion :
    Derives targetBasis leftDeletionIdentity.lhs leftDeletionIdentity.rhs :=
  Derives.fromBasis (e := leftDeletionIdentity) (by decide)

private theorem targetRightExpansion :
    Derives targetBasis rightExpansionIdentity.lhs rightExpansionIdentity.rhs :=
  Derives.fromBasis (e := rightExpansionIdentity) (by decide)

private theorem targetShortSwap :
    Derives targetBasis shortSwapIdentity.lhs shortSwapIdentity.rhs :=
  Derives.fromBasis (e := shortSwapIdentity) (by decide)

private theorem targetAlternatingSwap :
    Derives targetBasis alternatingSwapIdentity.lhs alternatingSwapIdentity.rhs :=
  Derives.fromBasis (e := alternatingSwapIdentity) (by decide)

private theorem targetMiddleDeletion :
    Derives targetBasis middleDeletionIdentity.lhs middleDeletionIdentity.rhs :=
  Derives.fromBasis (e := middleDeletionIdentity) (by decide)

private theorem targetRightContextSwap :
    Derives targetBasis rightContextSwapIdentity.lhs
      rightContextSwapIdentity.rhs :=
  Derives.fromBasis (e := rightContextSwapIdentity) (by decide)

private theorem targetTerminalContextSwap :
    Derives targetBasis terminalContextSwapIdentity.lhs
      terminalContextSwapIdentity.rhs :=
  Derives.fromBasis (e := terminalContextSwapIdentity) (by decide)

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- Frozen unary power under arbitrary whole-word substitution. -/
theorem derivesPower (first : Word Nat) :
    Derives targetBasis
      (first ++ first) ((first ++ first) ++ first) := by
  have substituted :=
    Derives.subst targetPower
      (instantiateThreeWords first first first)
  simpa [powerIdentity, w, instantiateThreeWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

/-- Frozen deletion of an extra initial copy. -/
theorem derivesLeftDeletion (first second : Word Nat) :
    Derives targetBasis
      (((first ++ first) ++ second) ++ first)
      ((first ++ second) ++ first) := by
  have substituted :=
    Derives.subst targetLeftDeletion
      (instantiateThreeWords first second second)
  simpa [leftDeletionIdentity, w, instantiateThreeWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

/-- Frozen duplication of an already repeated final block. -/
theorem derivesRightExpansion (first second : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ first)
      (((first ++ second) ++ first) ++ first) := by
  have substituted :=
    Derives.subst targetRightExpansion
      (instantiateThreeWords first second second)
  simpa [rightExpansionIdentity, w, instantiateThreeWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

private theorem derivesShortSwap (first second : Word Nat) :
    Derives targetBasis
      (((first ++ second) ++ first) ++ second)
      (((second ++ first) ++ first) ++ second) := by
  have substituted :=
    Derives.subst targetShortSwap
      (instantiateThreeWords first second second)
  simpa [shortSwapIdentity, w, instantiateThreeWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

private theorem derivesAlternatingSwap
    (first second guard : Word Nat) :
    Derives targetBasis
      ((((first ++ second) ++ first) ++ second) ++ guard)
      ((((first ++ second) ++ second) ++ first) ++ guard) := by
  have substituted :=
    Derives.subst targetAlternatingSwap
      (instantiateThreeWords first second guard)
  simpa [alternatingSwapIdentity, w, instantiateThreeWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

private theorem derivesMiddleDeletion
    (first second third : Word Nat) :
    Derives targetBasis
      ((((first ++ second) ++ first) ++ third) ++ first)
      (((first ++ second) ++ third) ++ first) := by
  have substituted :=
    Derives.subst targetMiddleDeletion
      (instantiateThreeWords first second third)
  simpa [middleDeletionIdentity, w, instantiateThreeWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

private theorem derivesRightContextSwap
    (first second third : Word Nat) :
    Derives targetBasis
      ((((first ++ second) ++ first) ++ third) ++ second)
      ((((second ++ first) ++ first) ++ third) ++ second) := by
  have substituted :=
    Derives.subst targetRightContextSwap
      (instantiateThreeWords first second third)
  simpa [rightContextSwapIdentity, w, instantiateThreeWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

private theorem derivesTerminalContextSwap
    (first second third : Word Nat) :
    Derives targetBasis
      ((((first ++ second) ++ third) ++ first) ++ second)
      ((((second ++ first) ++ third) ++ first) ++ second) := by
  have substituted :=
    Derives.subst targetTerminalContextSwap
      (instantiateThreeWords first second third)
  simpa [terminalContextSwapIdentity, w, instantiateThreeWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

/-- Guarded long rotation uses exactly five association-fixed target rewrites. -/
theorem derivesLongRotationRelative
    (first second third fourth guard : Word Nat) :
    Derives targetBasis
      (((((first ++ second) ++ third) ++ fourth) ++ first) ++ third ++ guard)
      (((((first ++ second) ++ third) ++ fourth) ++ third) ++ first ++ guard) := by
  have step1 :=
    Derives.appendRight
      (derivesRightExpansion first ((second ++ third) ++ fourth))
      (third ++ guard)
  have step2 :=
    Derives.prepend (first ++ second) <|
      Derives.appendRight
        (derivesMiddleDeletion third fourth (first ++ first)).symm guard
  have step3 :=
    Derives.prepend (((first ++ second) ++ third) ++ fourth)
      (derivesAlternatingSwap third first guard).symm
  have step4 :=
    Derives.appendRight
      (derivesMiddleDeletion first
        (((second ++ third) ++ fourth) ++ third) third) guard
  have step5 :=
    Derives.prepend (first ++ second) <|
      Derives.appendRight (derivesRightExpansion third fourth).symm
        (first ++ guard)
  exact Derives.trans
    (by simpa [Word.append_assoc] using step1) <|
    Derives.trans
      (by simpa [Word.append_assoc] using step2) <|
      Derives.trans
        (by simpa [Word.append_assoc] using step3) <|
        Derives.trans
          (by simpa [Word.append_assoc] using step4)
          (by simpa [Word.append_assoc] using step5)

/-- Guarded long context swap uses deletion, frozen swap, and contraction. -/
theorem derivesLongContextSwapRelative
    (first second third fourth guard : Word Nat) :
    Derives targetBasis
      (((((first ++ second) ++ third) ++ first) ++ fourth) ++ second ++ guard)
      (((((second ++ first) ++ third) ++ first) ++ fourth) ++ second ++ guard) := by
  have step1 :=
    Derives.prepend first <|
      Derives.appendRight
        (derivesLeftDeletion second ((third ++ first) ++ fourth)).symm
        guard
  have step2 :=
    Derives.appendRight
      (derivesRightContextSwap second first third).symm
      ((fourth ++ second) ++ guard)
  have step3 :=
    Derives.appendRight
      (derivesMiddleDeletion second first ((third ++ first) ++ fourth)) guard
  exact Derives.trans
    (by simpa [Word.append_assoc] using step1) <|
    Derives.trans
      (by simpa [Word.append_assoc] using step2)
      (by simpa [Word.append_assoc] using step3)

/-- Guarded terminal-square rotation uses exactly three displayed rewrites. -/
theorem derivesTerminalSquareRelative
    (first second third guard : Word Nat) :
    Derives targetBasis
      ((((first ++ second) ++ third) ++ first) ++ third ++ guard)
      ((((first ++ second) ++ third) ++ third) ++ first ++ guard) := by
  have step1 :=
    Derives.appendRight
      (derivesRightExpansion first (second ++ third))
      (third ++ guard)
  have step2 :=
    Derives.prepend (first ++ second)
      (derivesAlternatingSwap third first guard).symm
  have step3 :=
    Derives.appendRight
      (derivesMiddleDeletion first (second ++ third) third) guard
  exact Derives.trans
    (by simpa [Word.append_assoc] using step1) <|
    Derives.trans
      (by simpa [Word.append_assoc] using step2)
      (by simpa [Word.append_assoc] using step3)

/-- Guarded short rotation uses four displayed rewrites. -/
theorem derivesShortRotationRelative
    (first third fourth guard : Word Nat) :
    Derives targetBasis
      ((((first ++ third) ++ fourth) ++ first) ++ third ++ guard)
      ((((first ++ third) ++ fourth) ++ third) ++ first ++ guard) := by
  have step1 :=
    Derives.appendRight
      (derivesRightExpansion (first ++ third) fourth) guard
  have step2 :=
    Derives.prepend ((first ++ third) ++ fourth)
      (derivesAlternatingSwap first third guard)
  have step3 :=
    Derives.prepend first <|
      Derives.appendRight
        (derivesRightExpansion third (fourth ++ first)).symm
        (first ++ guard)
  have step4 :=
    Derives.appendRight
      (derivesMiddleDeletion first (third ++ fourth) third) guard
  exact Derives.trans
    (by simpa [Word.append_assoc] using step1) <|
    Derives.trans
      (by simpa [Word.append_assoc] using step2) <|
      Derives.trans
        (by simpa [Word.append_assoc] using step3)
        (by simpa [Word.append_assoc] using step4)

/-- Each exact S5_841/M20 axiom lifts under any nonempty final guard. -/
theorem derivesS5_841AxiomRelative
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_841.basis)
    (guard : Word Nat) :
    Derives targetBasis (identity.lhs ++ guard) (identity.rhs ++ guard) := by
  simp only [SemigroupBasis.CoRoots.S5_841.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [SemigroupBasis.CoRoots.S5_841.powerLaw,
      SemigroupBasis.CoRoots.S5_841.xx,
      SemigroupBasis.CoRoots.S5_841.xxx,
      powerIdentity, w] using
      Derives.appendRight targetPower guard
  · simpa [SemigroupBasis.CoRoots.S5_841.leftDeletionLaw,
      SemigroupBasis.CoRoots.S5_841.xxzx,
      SemigroupBasis.CoRoots.S5_841.xzx,
      Word.singleton, Word.append, Word.append_assoc] using
      Derives.appendRight
        (derivesLeftDeletion (Word.singleton 0) (Word.singleton 2)) guard
  · simpa [SemigroupBasis.CoRoots.S5_841.rightExpansionLaw,
      SemigroupBasis.CoRoots.S5_841.xyx,
      SemigroupBasis.CoRoots.S5_841.xyxx,
      rightExpansionIdentity, w] using
      Derives.appendRight targetRightExpansion guard
  · simpa [SemigroupBasis.CoRoots.S5_841.rightContextSwapLaw,
      SemigroupBasis.CoRoots.S5_841.xyxwy,
      SemigroupBasis.CoRoots.S5_841.yxxwy,
      Word.singleton, Word.append, Word.append_assoc] using
      Derives.appendRight
        (derivesRightContextSwap
          (Word.singleton 0) (Word.singleton 1) (Word.singleton 3)) guard
  · simpa [SemigroupBasis.CoRoots.S5_841.shortSwapLaw,
      SemigroupBasis.CoRoots.S5_841.xyxy,
      SemigroupBasis.CoRoots.S5_841.yxxy,
      shortSwapIdentity, w] using
      Derives.appendRight targetShortSwap guard
  · simpa [SemigroupBasis.CoRoots.S5_841.middleDeletionLaw,
      SemigroupBasis.CoRoots.S5_841.xyxzx,
      SemigroupBasis.CoRoots.S5_841.xyzx,
      Word.singleton, Word.append, Word.append_assoc] using
      Derives.appendRight
        (derivesMiddleDeletion
          (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)) guard
  · simpa [SemigroupBasis.CoRoots.S5_841.longRotationLaw,
      SemigroupBasis.CoRoots.S5_841.xyzwxz,
      SemigroupBasis.CoRoots.S5_841.xyzwzx,
      Word.singleton, Word.append, Word.append_assoc] using
      derivesLongRotationRelative
        (Word.singleton 0) (Word.singleton 1)
        (Word.singleton 2) (Word.singleton 3) guard
  · simpa [SemigroupBasis.CoRoots.S5_841.longContextSwapLaw,
      SemigroupBasis.CoRoots.S5_841.xyzxwy,
      SemigroupBasis.CoRoots.S5_841.yxzxwy,
      Word.singleton, Word.append, Word.append_assoc] using
      derivesLongContextSwapRelative
        (Word.singleton 0) (Word.singleton 1)
        (Word.singleton 2) (Word.singleton 3) guard
  · simpa [SemigroupBasis.CoRoots.S5_841.terminalContextSwapLaw,
      SemigroupBasis.CoRoots.S5_841.xyzxy,
      SemigroupBasis.CoRoots.S5_841.yxzxy,
      terminalContextSwapIdentity, w] using
      Derives.appendRight targetTerminalContextSwap guard
  · simpa [SemigroupBasis.CoRoots.S5_841.terminalSquareLaw,
      SemigroupBasis.CoRoots.S5_841.xyzxz,
      SemigroupBasis.CoRoots.S5_841.xyzzx,
      Word.singleton, Word.append, Word.append_assoc] using
      derivesTerminalSquareRelative
        (Word.singleton 0) (Word.singleton 1) (Word.singleton 2) guard
  · simpa [SemigroupBasis.CoRoots.S5_841.shortRotationLaw,
      SemigroupBasis.CoRoots.S5_841.xzwxz,
      SemigroupBasis.CoRoots.S5_841.xzwzx,
      Word.singleton, Word.append, Word.append_assoc] using
      derivesShortRotationRelative
        (Word.singleton 0) (Word.singleton 2) (Word.singleton 3) guard
  · simpa [SemigroupBasis.CoRoots.S5_841.alternatingSquareLaw,
      SemigroupBasis.CoRoots.S5_841.xzxz,
      SemigroupBasis.CoRoots.S5_841.xzzx,
      Word.singleton, Word.append, Word.append_assoc] using
      derivesAlternatingSwap (Word.singleton 0) (Word.singleton 2) guard

private def guardSubstitution
    (sigma : Nat → Word Nat) (guard : Word Nat) : Nat → Word Nat
  | 4 => guard
  | letter => sigma letter

/-- Fresh literal `4` is absent from all twelve S5_841 axioms. -/
theorem liftS5_841AxiomUnderGuard
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_841.basis)
    (guard : Word Nat) (sigma : Nat → Word Nat) :
    Derives targetBasis
      (identity.lhs.bind sigma ++ guard)
      (identity.rhs.bind sigma ++ guard) := by
  have substituted :=
    Derives.subst
      (derivesS5_841AxiomRelative identity member (Word.singleton 4))
      (guardSubstitution sigma guard)
  simp only [SemigroupBasis.CoRoots.S5_841.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simpa [SemigroupBasis.CoRoots.S5_841.powerLaw,
      SemigroupBasis.CoRoots.S5_841.leftDeletionLaw,
      SemigroupBasis.CoRoots.S5_841.rightExpansionLaw,
      SemigroupBasis.CoRoots.S5_841.rightContextSwapLaw,
      SemigroupBasis.CoRoots.S5_841.shortSwapLaw,
      SemigroupBasis.CoRoots.S5_841.middleDeletionLaw,
      SemigroupBasis.CoRoots.S5_841.longRotationLaw,
      SemigroupBasis.CoRoots.S5_841.longContextSwapLaw,
      SemigroupBasis.CoRoots.S5_841.terminalContextSwapLaw,
      SemigroupBasis.CoRoots.S5_841.terminalSquareLaw,
      SemigroupBasis.CoRoots.S5_841.shortRotationLaw,
      SemigroupBasis.CoRoots.S5_841.alternatingSquareLaw,
      SemigroupBasis.CoRoots.S5_841.xx,
      SemigroupBasis.CoRoots.S5_841.xxx,
      SemigroupBasis.CoRoots.S5_841.xxzx,
      SemigroupBasis.CoRoots.S5_841.xzx,
      SemigroupBasis.CoRoots.S5_841.xyx,
      SemigroupBasis.CoRoots.S5_841.xyxx,
      SemigroupBasis.CoRoots.S5_841.xyxwy,
      SemigroupBasis.CoRoots.S5_841.yxxwy,
      SemigroupBasis.CoRoots.S5_841.xyxy,
      SemigroupBasis.CoRoots.S5_841.yxxy,
      SemigroupBasis.CoRoots.S5_841.xyxzx,
      SemigroupBasis.CoRoots.S5_841.xyzx,
      SemigroupBasis.CoRoots.S5_841.xyzwxz,
      SemigroupBasis.CoRoots.S5_841.xyzwzx,
      SemigroupBasis.CoRoots.S5_841.xyzxwy,
      SemigroupBasis.CoRoots.S5_841.yxzxwy,
      SemigroupBasis.CoRoots.S5_841.xyzxy,
      SemigroupBasis.CoRoots.S5_841.yxzxy,
      SemigroupBasis.CoRoots.S5_841.xyzxz,
      SemigroupBasis.CoRoots.S5_841.xyzzx,
      SemigroupBasis.CoRoots.S5_841.xzwxz,
      SemigroupBasis.CoRoots.S5_841.xzwzx,
      SemigroupBasis.CoRoots.S5_841.xzxz,
      SemigroupBasis.CoRoots.S5_841.xzzx,
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

/-- Structural induction lifts all unrestricted S5_841 derivations under a
nonempty final guard and arbitrary whole-word substitution. -/
theorem liftS5_841UnderGuard
    {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_841.basis left right)
    (guard : Word Nat) (sigma : Nat → Word Nat) :
    Derives targetBasis
      (left.bind sigma ++ guard) (right.bind sigma ++ guard) := by
  induction derivation generalizing guard sigma with
  | fromBasis member =>
      exact liftS5_841AxiomUnderGuard _ member guard sigma
  | refl => exact Derives.refl _
  | symm _ induction => exact (induction guard sigma).symm
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

/-- Identity-substitution specialization of the twelve-law relative lift. -/
theorem liftS5_841UnderGuardIdentity
    {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_841.basis left right)
    (guard : Word Nat) :
    Derives targetBasis (left ++ guard) (right ++ guard) := by
  simpa [bind_singleton] using
    liftS5_841UnderGuard derivation guard Word.singleton

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_841

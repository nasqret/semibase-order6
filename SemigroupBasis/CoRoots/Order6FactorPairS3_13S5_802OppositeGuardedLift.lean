import SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw
import SemigroupBasis.CoRoots.S5_794Family
import SemigroupBasis.Generated.Order6OneLocalFordLord.SharedSevenLawInstances

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802Opposite

open SemigroupBasis

private abbrev sharedBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.basis

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_0b1bf8949e267cbb.basis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def tailPromotionLeft : Word Nat := w 0 [1, 1, 2, 2]
private def tailPromotionRight : Word Nat := w 0 [2, 1, 1, 2]

private def sharedLaws :
    SemigroupBasis.OneLocalFordLord.SharedReach.Laws basis :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.SharedSevenLawInstances.sigma_0b1bf8949e267cbb

private theorem transportShared {left right : Word Nat}
    (derivation : Derives sharedBasis left right) :
    Derives basis left right :=
  derivation.transport sharedLaws.sourceAxiomsDerive

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) :=
  transportShared
    (SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.derivesPowerExpansion u)

theorem derivesLeftDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) :=
  transportShared
    (SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.derivesLeftDuplication u v)

private theorem derivesRightDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) :=
  transportShared
    (SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.derivesRightDuplication u v)

private theorem derivesFirstDeletion (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ u) ++ z) ++ v) :=
  transportShared
    (SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.derivesFirstDeletion u v z)

private theorem derivesMiddleDeletion (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) :=
  transportShared
    (SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.derivesMiddleDeletion u v z)

private theorem derivesSquareGather (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ v)
      ((u ++ u) ++ (v ++ v)) :=
  transportShared
    (SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.derivesL7Square u v)

private theorem derivesDoubledSuffix (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ z)
      ((((u ++ v) ++ z) ++ u) ++ z) :=
  (transportShared
    (SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw.derivesL7Medium u v z)).symm

private theorem basisTailPromotion :
    Derives basis tailPromotionLeft tailPromotionRight :=
  Derives.fromBasis (e := Identity.mk tailPromotionLeft tailPromotionRight)
    (by decide)

private def instantiateThreeWords
    (guard u v : Word Nat) : Nat -> Word Nat
  | 0 => guard
  | 1 => u
  | 2 => v
  | n + 3 => Word.singleton (n + 3)

/-- The eighth displayed law after arbitrary nonempty substitutions. -/
theorem derivesTailPromotion (guard u v : Word Nat) :
    Derives basis
      ((((guard ++ u) ++ u) ++ v) ++ v)
      ((((guard ++ v) ++ u) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisTailPromotion
      (instantiateThreeWords guard u v)
  simpa [tailPromotionLeft, tailPromotionRight, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-! ## Literal opposite source basis -/

private def sourcePower : Identity Nat :=
  Identity.mk (w 0 [0]) (w 0 [0, 0])

private def sourceFirstDeletion : Identity Nat :=
  Identity.mk (w 2 [3, 2, 0, 0]) (w 2 [3, 0, 2, 0])

private def sourceLeftDeletion : Identity Nat :=
  Identity.mk (w 0 [2, 0, 0]) (w 0 [2, 0])

private def sourceSquareInterchange : Identity Nat :=
  Identity.mk (w 2 [2, 0, 0]) (w 2 [0, 2, 0])

private def sourceRightExpansion : Identity Nat :=
  Identity.mk (w 0 [1, 0]) (w 0 [0, 1, 0])

private def sourceMixedDeletion : Identity Nat :=
  Identity.mk (w 2 [3, 2, 0, 1, 0]) (w 2 [3, 0, 2, 1, 0])

private def sourceMiddleDeletion : Identity Nat :=
  Identity.mk (w 0 [2, 0, 1, 0]) (w 0 [2, 1, 0])

private def sourceDoubledSuffix : Identity Nat :=
  Identity.mk (w 2 [2, 0, 1, 0]) (w 2 [0, 2, 1, 0])

private def sourceLongRotation : Identity Nat :=
  Identity.mk (w 2 [0, 3, 2, 1, 0]) (w 0 [2, 3, 2, 1, 0])

private def sourceTerminalSquare : Identity Nat :=
  Identity.mk (w 2 [0, 2, 1, 0]) (w 0 [2, 2, 1, 0])

private def sourceShortRotation : Identity Nat :=
  Identity.mk (w 2 [0, 3, 2, 0]) (w 0 [2, 3, 2, 0])

private def sourceAlternatingSquare : Identity Nat :=
  Identity.mk (w 2 [0, 2, 0]) (w 0 [2, 2, 0])

private def literalOppositeBasis : List (Identity Nat) :=
  [sourcePower, sourceFirstDeletion, sourceLeftDeletion,
    sourceSquareInterchange, sourceRightExpansion, sourceMixedDeletion,
    sourceMiddleDeletion, sourceDoubledSuffix, sourceLongRotation,
    sourceTerminalSquare, sourceShortRotation, sourceAlternatingSquare]

private theorem literalOppositeBasis_eq :
    literalOppositeBasis = SemigroupBasis.CoRoots.S5_794.oppositeBasis := by
  decide

/-! ## Guarded traces for the head-changing source moves -/

private theorem derivesGuardedMixedDeletion
    (guard x y z q : Word Nat) :
    Derives basis
      (guard ++ (((((z ++ q) ++ z) ++ x) ++ y) ++ x))
      (guard ++ (((((z ++ q) ++ x) ++ z) ++ y) ++ x)) := by
  have first :=
    Derives.prepend (((guard ++ z) ++ q) ++ z)
      (derivesLeftDuplication x y)
  have second :=
    Derives.appendRight
      (Derives.prepend guard (derivesDoubledSuffix z q x))
      (y ++ x)
  have third :=
    Derives.prepend ((guard ++ z) ++ q)
      (derivesMiddleDeletion x z y)
  have first' :
      Derives basis
        (guard ++ z ++ q ++ z ++ x ++ y ++ x)
        (guard ++ z ++ q ++ z ++ x ++ x ++ y ++ x) := by
    simpa [Word.append_assoc] using first
  have second' :
      Derives basis
        (guard ++ z ++ q ++ z ++ x ++ x ++ y ++ x)
        (guard ++ z ++ q ++ x ++ z ++ x ++ y ++ x) := by
    simpa [Word.append_assoc] using second
  have third' :
      Derives basis
        (guard ++ z ++ q ++ x ++ z ++ x ++ y ++ x)
        (guard ++ z ++ q ++ x ++ z ++ y ++ x) := by
    simpa [Word.append_assoc] using third
  simpa [Word.append_assoc] using
    first'.trans (second'.trans third')

private theorem derivesGuardedLongRotation
    (guard x y z q : Word Nat) :
    Derives basis
      (guard ++ (((((z ++ x) ++ q) ++ z) ++ y) ++ x))
      (guard ++ (((((x ++ z) ++ q) ++ z) ++ y) ++ x)) := by
  have first :=
    Derives.appendRight
      (Derives.prepend guard
        (derivesLeftDuplication z (x ++ q)))
      (y ++ x)
  have second :=
    Derives.prepend ((guard ++ z) ++ z)
      (derivesLeftDuplication x ((q ++ z) ++ y))
  have third :=
    Derives.appendRight (derivesTailPromotion guard z x)
      (((q ++ z) ++ y) ++ x)
  have fourth :=
    Derives.appendRight
      (Derives.prepend (guard ++ x)
        (derivesLeftDuplication z (x ++ q)).symm)
      (y ++ x)
  have fifth :=
    Derives.prepend guard
      (derivesMiddleDeletion x z ((q ++ z) ++ y))
  have first' :
      Derives basis
        (guard ++ z ++ x ++ q ++ z ++ y ++ x)
        (guard ++ z ++ z ++ x ++ q ++ z ++ y ++ x) := by
    simpa [Word.append_assoc] using first
  have second' :
      Derives basis
        (guard ++ z ++ z ++ x ++ q ++ z ++ y ++ x)
        (guard ++ z ++ z ++ x ++ x ++ q ++ z ++ y ++ x) := by
    simpa [Word.append_assoc] using second
  have third' :
      Derives basis
        (guard ++ z ++ z ++ x ++ x ++ q ++ z ++ y ++ x)
        (guard ++ x ++ z ++ z ++ x ++ q ++ z ++ y ++ x) := by
    simpa [Word.append_assoc] using third
  have fourth' :
      Derives basis
        (guard ++ x ++ z ++ z ++ x ++ q ++ z ++ y ++ x)
        (guard ++ x ++ z ++ x ++ q ++ z ++ y ++ x) := by
    simpa [Word.append_assoc] using fourth
  have fifth' :
      Derives basis
        (guard ++ x ++ z ++ x ++ q ++ z ++ y ++ x)
        (guard ++ x ++ z ++ q ++ z ++ y ++ x) := by
    simpa [Word.append_assoc] using fifth
  simpa [Word.append_assoc] using
    first'.trans
      (second'.trans (third'.trans (fourth'.trans fifth')))

private theorem derivesGuardedTerminalSquare
    (guard x y z : Word Nat) :
    Derives basis
      (guard ++ ((((z ++ x) ++ z) ++ y) ++ x))
      (guard ++ ((((x ++ z) ++ z) ++ y) ++ x)) := by
  have first :=
    Derives.prepend (guard ++ z)
      (derivesLeftDuplication x (z ++ y))
  have second :=
    Derives.appendRight (derivesTailPromotion guard x z).symm
      (y ++ x)
  have third :=
    Derives.prepend guard
      (derivesLeftDuplication x ((z ++ z) ++ y)).symm
  have first' :
      Derives basis
        (guard ++ z ++ x ++ z ++ y ++ x)
        (guard ++ z ++ x ++ x ++ z ++ y ++ x) := by
    simpa [Word.append_assoc] using first
  have second' :
      Derives basis
        (guard ++ z ++ x ++ x ++ z ++ y ++ x)
        (guard ++ x ++ x ++ z ++ z ++ y ++ x) := by
    simpa [Word.append_assoc] using second
  have third' :
      Derives basis
        (guard ++ x ++ x ++ z ++ z ++ y ++ x)
        (guard ++ x ++ z ++ z ++ y ++ x) := by
    simpa [Word.append_assoc] using third
  simpa [Word.append_assoc] using
    first'.trans (second'.trans third')

private theorem derivesGuardedShortRotation
    (guard x z q : Word Nat) :
    Derives basis
      (guard ++ ((((z ++ x) ++ q) ++ z) ++ x))
      (guard ++ ((((x ++ z) ++ q) ++ z) ++ x)) := by
  have first :=
    Derives.appendRight
      (Derives.prepend guard
        (derivesLeftDuplication z (x ++ q))) x
  have second :=
    Derives.prepend ((guard ++ z) ++ z)
      (derivesLeftDuplication x (q ++ z))
  have third :=
    Derives.appendRight (derivesTailPromotion guard z x)
      ((q ++ z) ++ x)
  have fourth :=
    Derives.appendRight
      (Derives.prepend (guard ++ x)
        (derivesLeftDuplication z (x ++ q)).symm) x
  have fifth :=
    Derives.prepend guard
      (derivesMiddleDeletion x z (q ++ z))
  have first' :
      Derives basis
        (guard ++ z ++ x ++ q ++ z ++ x)
        (guard ++ z ++ z ++ x ++ q ++ z ++ x) := by
    simpa [Word.append_assoc] using first
  have second' :
      Derives basis
        (guard ++ z ++ z ++ x ++ q ++ z ++ x)
        (guard ++ z ++ z ++ x ++ x ++ q ++ z ++ x) := by
    simpa [Word.append_assoc] using second
  have third' :
      Derives basis
        (guard ++ z ++ z ++ x ++ x ++ q ++ z ++ x)
        (guard ++ x ++ z ++ z ++ x ++ q ++ z ++ x) := by
    simpa [Word.append_assoc] using third
  have fourth' :
      Derives basis
        (guard ++ x ++ z ++ z ++ x ++ q ++ z ++ x)
        (guard ++ x ++ z ++ x ++ q ++ z ++ x) := by
    simpa [Word.append_assoc] using fourth
  have fifth' :
      Derives basis
        (guard ++ x ++ z ++ x ++ q ++ z ++ x)
        (guard ++ x ++ z ++ q ++ z ++ x) := by
    simpa [Word.append_assoc] using fifth
  simpa [Word.append_assoc] using
    first'.trans
      (second'.trans (third'.trans (fourth'.trans fifth')))

private theorem derivesGuardedAlternatingSquare
    (guard x z : Word Nat) :
    Derives basis
      (guard ++ (((z ++ x) ++ z) ++ x))
      (guard ++ (((x ++ z) ++ z) ++ x)) := by
  have gathered :=
    Derives.prepend guard (derivesSquareGather z x)
  exact gathered.trans <| by
    simpa [Word.append_assoc] using derivesTailPromotion guard z x

/-- Every axiom of the complete opposite-`S5_802` presentation can be
replayed after an arbitrary nonempty prefix.  The first eight source laws use
the shared seven-law calculus.  The four head-changing rotations use the
eighth Sigma law through the explicit traces above. -/
theorem liftOppositeAxiomUnderPrefix
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_794.oppositeBasis)
    (guard : Word Nat) (sigma : Nat -> Word Nat) :
    Derives basis
      (guard ++ identity.lhs.bind sigma)
      (guard ++ identity.rhs.bind sigma) := by
  rw [← literalOppositeBasis_eq] at member
  simp only [literalOppositeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [sourcePower, w, Word.bind, Word.append, Word.singleton,
      Word.append_assoc] using
      Derives.prepend guard (derivesPowerExpansion (sigma 0))
  · simpa [sourceFirstDeletion, w, Word.bind, Word.append,
      Word.singleton, Word.append_assoc] using
      Derives.prepend guard
        (derivesDoubledSuffix (sigma 2) (sigma 3) (sigma 0))
  · simpa [sourceLeftDeletion, w, Word.bind, Word.append,
      Word.singleton, Word.append_assoc] using
      Derives.prepend guard
        (derivesRightDuplication (sigma 0) (sigma 2)).symm
  · simpa [sourceSquareInterchange, w, Word.bind, Word.append,
      Word.singleton, Word.append_assoc] using
      Derives.prepend guard
        (derivesSquareGather (sigma 2) (sigma 0)).symm
  · simpa [sourceRightExpansion, w, Word.bind, Word.append,
      Word.singleton, Word.append_assoc] using
      Derives.prepend guard
        (derivesLeftDuplication (sigma 0) (sigma 1))
  · simpa [sourceMixedDeletion, w, Word.bind, Word.append,
      Word.singleton, Word.append_assoc] using
      derivesGuardedMixedDeletion guard
        (sigma 0) (sigma 1) (sigma 2) (sigma 3)
  · simpa [sourceMiddleDeletion, w, Word.bind, Word.append,
      Word.singleton, Word.append_assoc] using
      Derives.prepend guard
        (derivesMiddleDeletion (sigma 0) (sigma 2) (sigma 1))
  · simpa [sourceDoubledSuffix, w, Word.bind, Word.append,
      Word.singleton, Word.append_assoc] using
      Derives.prepend guard
        (derivesFirstDeletion (sigma 2) (sigma 0) (sigma 1))
  · simpa [sourceLongRotation, w, Word.bind, Word.append,
      Word.singleton, Word.append_assoc] using
      derivesGuardedLongRotation guard
        (sigma 0) (sigma 1) (sigma 2) (sigma 3)
  · simpa [sourceTerminalSquare, w, Word.bind, Word.append,
      Word.singleton, Word.append_assoc] using
      derivesGuardedTerminalSquare guard
        (sigma 0) (sigma 1) (sigma 2)
  · simpa [sourceShortRotation, w, Word.bind, Word.append,
      Word.singleton, Word.append_assoc] using
      derivesGuardedShortRotation guard
        (sigma 0) (sigma 2) (sigma 3)
  · simpa [sourceAlternatingSquare, w, Word.bind, Word.append,
      Word.singleton, Word.append_assoc] using
      derivesGuardedAlternatingSquare guard (sigma 0) (sigma 2)

private theorem bind_append
    (left right : Word Nat) (sigma : Nat -> Word Nat) :
    (left ++ right).bind sigma =
      left.bind sigma ++ right.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (tau sigma : Nat -> Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun letter => (tau letter).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Lift an arbitrary derivation in the complete opposite-`S5_802` basis
behind a fixed nonempty prefix.  This is the reusable relative deduction
theorem needed by the `S3_13` head detector. -/
theorem liftOppositeBasisUnderPrefix
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_794.oppositeBasis left right)
    (guard : Word Nat) (sigma : Nat -> Word Nat) :
    Derives basis
      (guard ++ left.bind sigma)
      (guard ++ right.bind sigma) := by
  induction derivation generalizing guard sigma with
  | fromBasis member =>
      exact liftOppositeAxiomUnderPrefix _ member guard sigma
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact Derives.symm (induction guard sigma)
  | trans _ _ firstInduction secondInduction =>
      exact Derives.trans
        (firstInduction guard sigma) (secondInduction guard sigma)
  | prepend prefixWord _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (guard ++ prefixWord.bind sigma) sigma
  | appendRight _ suffix induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (induction guard sigma) (suffix.bind sigma)
  | subst _ tau induction =>
      simpa [bind_bind] using
        induction guard (fun letter => (tau letter).bind sigma)

theorem liftOppositeBasisUnderPrefixIdentity
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_794.oppositeBasis left right)
    (guard : Word Nat) :
    Derives basis (guard ++ left) (guard ++ right) := by
  simpa [bind_singleton] using
    liftOppositeBasisUnderPrefix derivation guard Word.singleton

end SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802Opposite

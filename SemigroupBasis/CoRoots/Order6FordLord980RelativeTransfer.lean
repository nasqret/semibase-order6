import SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802OppositeGuardedLift
import SemigroupBasis.CoRoots.Order6FactorPairS3_15OppositeWidening
import SemigroupBasis.CoRoots.Order6FordLord980Normal
import SemigroupBasis.CoRoots.Order6SporadicSection14Invariants
import SemigroupBasis.CoRoots.S5_400CanonicalSufficiency
import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S5_400PublishedRoots

set_option maxRecDepth 100000

/-!
# Relative transfer for the `9808750adcf41d94` Ford--Lord system

This module avoids the bespoke snoc normalizer.  It reverses the committed
`S5_794.oppositeBasis` prefix lift to obtain a suffix lift, transports the
eight reversed guard laws into the exact eleven-law `980` basis, extends the
lift across the four additional `S5_400` laws, and applies a final-marker
relative-deduction argument.  The resulting `S2_4^op x S5_840` intersection
is finally widened along the recorded embedding into `S3_15^op`.
-/

namespace SemigroupBasis.CoRoots.Order6FordLord980RelativeTransfer

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev guardBasis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_0b1bf8949e267cbb.basis

private abbrev reversedGuardBasis : List (Identity Nat) :=
  reversedBasis guardBasis

private abbrev targetBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FordLord980.basis

private abbrev shortBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.S5_794.basis

private abbrev sourceBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.S5_400.basis

private abbrev smallLeftFactor :=
  SemigroupBasis.Generated.S2_4.table.semigroup.opposite

private abbrev targetLeftFactor :=
  SemigroupBasis.Generated.S3_15.table.semigroup.opposite

private abbrev rightFactor :=
  SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-! ## Reversed guard-basis transport -/

private def b1 : Identity Nat :=
  Identity.mk (w 0 [0]) (w 0 [0, 0])

private def b2 : Identity Nat :=
  Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0])

private def b3 : Identity Nat :=
  Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])

private def b4 : Identity Nat :=
  Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1])

private def b5 : Identity Nat :=
  Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0])

private def b6 : Identity Nat :=
  Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0])

private def b7 : Identity Nat :=
  Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2])

private def b8 : Identity Nat :=
  Identity.mk (w 0 [1, 1, 2, 2]) (w 0 [2, 1, 1, 2])

private theorem guardBasis_eq :
    guardBasis = [b1, b2, b3, b4, b5, b6, b7, b8] := by
  decide

/-- Every reversed guard axiom is an exact block instance of a `980` law. -/
private theorem reversedGuardAxiomsDeriveTarget :
    forall identity : Identity Nat, identity ∈ reversedGuardBasis ->
      Derives targetBasis identity.lhs identity.rhs := by
  intro identity member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  rw [guardBasis_eq] at sourceMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at sourceMember
  rcases sourceMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [b1, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLord980.derivesPower
        (Word.singleton 0))
  · simpa [b2, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLord980.derivesRightDuplication
        (Word.singleton 0) (Word.singleton 1)).symm
  · simpa [b3, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLord980.derivesInterleave
        (Word.singleton 1) (Word.singleton 0))
  · simpa [b4, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLord980.derivesTailTransport
        (Word.singleton 1) (Word.singleton 2) (Word.singleton 0))
  · simpa [b5, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLord980.derivesLeftCollapse
        (Word.singleton 0) (Word.singleton 1)).symm
  · simpa [b6, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLord980.derivesMiddleCollapse
        (Word.singleton 0) (Word.singleton 2) (Word.singleton 1))
  · simpa [b7, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLord980.derivesLeftTransport
        (Word.singleton 2) (Word.singleton 0) (Word.singleton 1))
  · simpa [b8, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLord980.derivesPlasmaLordForget
        (Word.singleton 2) (Word.singleton 1) (Word.singleton 0))

/-- Reverse the committed opposite-`S5_794` prefix lift into a direct
`S5_794` suffix lift, then transport its reversed guard axioms to `980`. -/
theorem liftS5_794UnderSuffixIdentity
    {left right : Word Nat}
    (derivation : Derives shortBasis left right)
    (suffix : Word Nat) :
    Derives targetBasis (left ++ suffix) (right ++ suffix) := by
  have oppositeDerivation :
      Derives SemigroupBasis.CoRoots.S5_794.oppositeBasis
        left.reverse right.reverse := by
    simpa [SemigroupBasis.CoRoots.S5_794.oppositeBasis] using
      derivation.reverse
  have prefixed :=
    SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802Opposite.liftOppositeBasisUnderPrefixIdentity
      oppositeDerivation suffix.reverse
  have reversed :
      Derives reversedGuardBasis
        (left ++ suffix) (right ++ suffix) := by
    simpa [reversedGuardBasis, guardBasis] using prefixed.reverse
  exact reversed.transport reversedGuardAxiomsDeriveTarget

/-! ## Extension from `S5_794` to the complete `S5_400` basis -/

private def shortBasisView : List (Identity Nat) :=
  [SemigroupBasis.CoRoots.S5_400.powerLaw,
    SemigroupBasis.CoRoots.S5_400.firstDeletionLaw,
    SemigroupBasis.CoRoots.S5_400.leftDeletionLaw,
    SemigroupBasis.CoRoots.S5_400.squareInterchangeLaw,
    SemigroupBasis.CoRoots.S5_400.rightExpansionLaw,
    SemigroupBasis.CoRoots.S5_400.mixedDeletionLaw,
    SemigroupBasis.CoRoots.S5_400.middleDeletionLaw,
    SemigroupBasis.CoRoots.S5_400.doubledSuffixLaw,
    SemigroupBasis.CoRoots.S5_400.longRotationLaw,
    SemigroupBasis.CoRoots.S5_400.terminalSquareLaw,
    SemigroupBasis.CoRoots.S5_400.shortRotationLaw,
    SemigroupBasis.CoRoots.S5_400.alternatingSquareLaw]

private theorem shortBasisView_eq : shortBasisView = shortBasis := by
  decide

private def s5RightContextSwapLaw : Identity Nat :=
  Identity.mk (w 0 [1, 0, 3, 1]) (w 1 [0, 0, 3, 1])

private def s5ShortSwapLaw : Identity Nat :=
  Identity.mk (w 0 [1, 0, 1]) (w 1 [0, 0, 1])

private def s5LongContextSwapLaw : Identity Nat :=
  Identity.mk (w 0 [1, 2, 0, 3, 1]) (w 1 [0, 2, 0, 3, 1])

private def s5TerminalContextSwapLaw : Identity Nat :=
  Identity.mk (w 0 [1, 2, 0, 1]) (w 1 [0, 2, 0, 1])

private theorem s5RightContextSwapLaw_eq :
    SemigroupBasis.CoRoots.S5_400.rightContextSwapLaw =
      s5RightContextSwapLaw := by
  decide

private theorem s5ShortSwapLaw_eq :
    SemigroupBasis.CoRoots.S5_400.shortSwapLaw = s5ShortSwapLaw := by
  decide

private theorem s5LongContextSwapLaw_eq :
    SemigroupBasis.CoRoots.S5_400.longContextSwapLaw =
      s5LongContextSwapLaw := by
  decide

private theorem s5TerminalContextSwapLaw_eq :
    SemigroupBasis.CoRoots.S5_400.terminalContextSwapLaw =
      s5TerminalContextSwapLaw := by
  decide

private theorem derivesS5RightContextSwap :
    Derives targetBasis s5RightContextSwapLaw.lhs
      s5RightContextSwapLaw.rhs := by
  have first :=
    (SemigroupBasis.CoRoots.Order6FordLord980.derivesLeftTransport
      (Word.singleton 0) (Word.singleton 1) (Word.singleton 3)).symm
  have second :=
    SemigroupBasis.CoRoots.Order6FordLord980.derivesHeadForgetTransport
      (Word.singleton 0) (Word.singleton 1) (Word.singleton 3)
  simpa [s5RightContextSwapLaw, w, Word.singleton, Word.append,
    Word.append_assoc] using first.trans second

private theorem derivesS5ShortSwap :
    Derives targetBasis s5ShortSwapLaw.lhs s5ShortSwapLaw.rhs := by
  have first :=
    (SemigroupBasis.CoRoots.Order6FordLord980.derivesInterleave
      (Word.singleton 0) (Word.singleton 1)).symm
  have second :=
    SemigroupBasis.CoRoots.Order6FordLord980.derivesPlasmaFordForget
      (Word.singleton 0) (Word.singleton 1)
  simpa [s5ShortSwapLaw, w, Word.singleton, Word.append,
    Word.append_assoc] using first.trans second

private theorem derivesS5LongContextSwap :
    Derives targetBasis s5LongContextSwapLaw.lhs
      s5LongContextSwapLaw.rhs := by
  have first :=
    Derives.appendRight
      (SemigroupBasis.CoRoots.Order6FordLord980.derivesLeftCollapse
        (Word.singleton 0)
        (Word.singleton 1 ++ Word.singleton 2)).symm
      (Word.singleton 3 ++ Word.singleton 1)
  have second :=
    SemigroupBasis.CoRoots.Order6FordLord980.derivesHeadForgetTransport
      (Word.singleton 0) (Word.singleton 1)
      ((Word.singleton 2 ++ Word.singleton 0) ++ Word.singleton 3)
  have third :=
    Derives.appendRight
      (Derives.prepend (Word.singleton 1)
        (SemigroupBasis.CoRoots.Order6FordLord980.derivesLeftCollapse
          (Word.singleton 0) (Word.singleton 2)))
      (Word.singleton 3 ++ Word.singleton 1)
  simpa [s5LongContextSwapLaw, w, Word.singleton, Word.append,
    Word.append_assoc] using first.trans (second.trans third)

private theorem derivesS5TerminalContextSwap :
    Derives targetBasis s5TerminalContextSwapLaw.lhs
      s5TerminalContextSwapLaw.rhs := by
  simpa [s5TerminalContextSwapLaw, w, Word.singleton, Word.append,
    Word.append_assoc] using
    (SemigroupBasis.CoRoots.Order6FordLord980.derivesLateHeadForget
      (Word.singleton 0) (Word.singleton 1) (Word.singleton 2))

private theorem liftShortAxiomUnderSuffix
    (identity : Identity Nat) (member : identity ∈ shortBasisView)
    (suffix : Word Nat) (sigma : Nat -> Word Nat) :
    Derives targetBasis
      (identity.lhs.bind sigma ++ suffix)
      (identity.rhs.bind sigma ++ suffix) := by
  have sourceMember : identity ∈ shortBasis := by
    rw [← shortBasisView_eq]
    exact member
  exact liftS5_794UnderSuffixIdentity
    (Derives.subst (Derives.fromBasis sourceMember) sigma) suffix

private theorem liftS5_400AxiomUnderSuffix
    (identity : Identity Nat) (member : identity ∈ sourceBasis)
    (suffix : Word Nat) (sigma : Nat -> Word Nat) :
    Derives targetBasis
      (identity.lhs.bind sigma ++ suffix)
      (identity.rhs.bind sigma ++ suffix) := by
  simp only [SemigroupBasis.CoRoots.S5_400.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact liftShortAxiomUnderSuffix _ (by simp [shortBasisView]) suffix sigma
  · exact liftShortAxiomUnderSuffix _ (by simp [shortBasisView]) suffix sigma
  · exact liftShortAxiomUnderSuffix _ (by simp [shortBasisView]) suffix sigma
  · exact liftShortAxiomUnderSuffix _ (by simp [shortBasisView]) suffix sigma
  · exact liftShortAxiomUnderSuffix _ (by simp [shortBasisView]) suffix sigma
  · rw [s5RightContextSwapLaw_eq]
    exact Derives.appendRight
      (Derives.subst derivesS5RightContextSwap sigma) suffix
  · rw [s5ShortSwapLaw_eq]
    exact Derives.appendRight
      (Derives.subst derivesS5ShortSwap sigma) suffix
  · exact liftShortAxiomUnderSuffix _ (by simp [shortBasisView]) suffix sigma
  · exact liftShortAxiomUnderSuffix _ (by simp [shortBasisView]) suffix sigma
  · exact liftShortAxiomUnderSuffix _ (by simp [shortBasisView]) suffix sigma
  · exact liftShortAxiomUnderSuffix _ (by simp [shortBasisView]) suffix sigma
  · rw [s5LongContextSwapLaw_eq]
    exact Derives.appendRight
      (Derives.subst derivesS5LongContextSwap sigma) suffix
  · rw [s5TerminalContextSwapLaw_eq]
    exact Derives.appendRight
      (Derives.subst derivesS5TerminalContextSwap sigma) suffix
  · exact liftShortAxiomUnderSuffix _ (by simp [shortBasisView]) suffix sigma
  · exact liftShortAxiomUnderSuffix _ (by simp [shortBasisView]) suffix sigma
  · exact liftShortAxiomUnderSuffix _ (by simp [shortBasisView]) suffix sigma

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

/-- Every derivation in the complete `S5_400` basis remains derivable
immediately before an arbitrary fixed nonempty suffix. -/
theorem liftS5_400UnderSuffix
    {left right : Word Nat}
    (derivation : Derives sourceBasis left right)
    (suffix : Word Nat) (sigma : Nat -> Word Nat) :
    Derives targetBasis
      (left.bind sigma ++ suffix) (right.bind sigma ++ suffix) := by
  induction derivation generalizing suffix sigma with
  | fromBasis member =>
      exact liftS5_400AxiomUnderSuffix _ member suffix sigma
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

theorem liftS5_400UnderSuffixIdentity
    {left right : Word Nat}
    (derivation : Derives sourceBasis left right)
    (suffix : Word Nat) :
    Derives targetBasis (left ++ suffix) (right ++ suffix) := by
  simpa [bind_singleton] using
    liftS5_400UnderSuffix derivation suffix Word.singleton

/-! ## Exact factor soundness -/

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def oppositeFiniteTable (table : FiniteTable) : FiniteTable where
  order := table.order
  mul := fun left right => table.mul right left
  assoc := fun left middle right =>
    (table.assoc right middle left).symm

private theorem oppositeFiniteTable_semigroup (table : FiniteTable) :
    (oppositeFiniteTable table).semigroup =
      table.semigroup.opposite := by
  rfl

theorem modelsS2_4Opposite : Models smallLeftFactor targetBasis := by
  change Models
    SemigroupBasis.Generated.S2_4.table.semigroup.opposite targetBasis
  rw [← oppositeFiniteTable_semigroup SemigroupBasis.Generated.S2_4.table]
  exact FiniteCertificate.checkModels_sound
    (oppositeFiniteTable SemigroupBasis.Generated.S2_4.table)
    targetBasis toFinThree (by decide)

theorem modelsS3_15Opposite : Models targetLeftFactor targetBasis := by
  change Models
    SemigroupBasis.Generated.S3_15.table.semigroup.opposite targetBasis
  rw [← oppositeFiniteTable_semigroup SemigroupBasis.Generated.S3_15.table]
  exact FiniteCertificate.checkModels_sound
    (oppositeFiniteTable SemigroupBasis.Generated.S3_15.table)
    targetBasis toFinThree (by decide)

theorem modelsS5_840 : Models rightFactor targetBasis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_840.table
    targetBasis toFinThree (by decide)

/-! ## Final-marker syntax and semantics -/

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

private theorem split_final_eq (word : Word Nat) :
    (splitPrefixFinal word).2 = word.final := by
  have reconstructed := congrArg Word.final (wordOfPrefixFinal_split word)
  rw [final_wordOfPrefixFinal] at reconstructed
  exact reconstructed

private theorem toList_eq_splitPrefixFinal (word : Word Nat) :
    word.toList =
      (splitPrefixFinal word).1 ++ [(splitPrefixFinal word).2] := by
  have reconstructed :=
    congrArg Word.toList (wordOfPrefixFinal_split word)
  rw [toList_wordOfPrefixFinal] at reconstructed
  exact reconstructed.symm

private theorem splitFinal_not_mem_prefix_of_count_one
    (word : Word Nat)
    (countOne : word.toList.count word.final = 1) :
    (splitPrefixFinal word).2 ∉ (splitPrefixFinal word).1 := by
  have finalEq := split_final_eq word
  have countOne' :
      word.toList.count (splitPrefixFinal word).2 = 1 := by
    simpa [finalEq] using countOne
  rw [toList_eq_splitPrefixFinal, List.count_append] at countOne'
  simp only [List.count_singleton_self] at countOne'
  have prefixCount :
      (splitPrefixFinal word).1.count (splitPrefixFinal word).2 = 0 := by
    omega
  exact List.count_eq_zero.mp prefixCount

private theorem splitFinal_mem_prefix_of_count_ne_one
    (word : Word Nat)
    (countNotOne : word.toList.count word.final ≠ 1) :
    (splitPrefixFinal word).2 ∈ (splitPrefixFinal word).1 := by
  have finalEq := split_final_eq word
  have countNotOne' :
      word.toList.count (splitPrefixFinal word).2 ≠ 1 := by
    simpa [finalEq] using countNotOne
  have countShape :
      word.toList.count (splitPrefixFinal word).2 =
        (splitPrefixFinal word).1.count (splitPrefixFinal word).2 + 1 := by
    rw [toList_eq_splitPrefixFinal, List.count_append]
    simp
  have positive :
      0 < (splitPrefixFinal word).1.count (splitPrefixFinal word).2 := by
    omega
  exact List.count_pos_iff.mp positive

private theorem sameCanonicalSupport
    {left right : Word Nat}
    (same : SemigroupBasis.CoRoots.S5_400.SameCanonicalSignature left right)
    (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := by
  have absent : letter ∉ left.toList ↔ letter ∉ right.toList := by
    rw [← List.count_eq_zero, ← List.count_eq_zero,
      ← SemigroupBasis.CoRoots.S5_107.cappedMultiplicity_eq_zero_iff,
      ← SemigroupBasis.CoRoots.S5_107.cappedMultiplicity_eq_zero_iff,
      same.capped letter]
  simpa using not_congr absent

private theorem finalCountOneIff
    {left right : Word Nat}
    (same : SemigroupBasis.CoRoots.S5_400.SameCanonicalSignature left right)
    (finalEq : left.final = right.final) :
    left.toList.count left.final = 1 ↔
      right.toList.count right.final = 1 := by
  rw [← SemigroupBasis.CoRoots.S5_107.cappedMultiplicity_eq_one_iff,
    ← SemigroupBasis.CoRoots.S5_107.cappedMultiplicity_eq_one_iff,
    ← finalEq, same.capped left.final]

private theorem splitPrefix_nil_of_sameCanonical
    {left right : Word Nat}
    (same : SemigroupBasis.CoRoots.S5_400.SameCanonicalSignature left right)
    (finalEq : left.final = right.final)
    (leftSimple : left.toList.count left.final = 1)
    (rightSimple : right.toList.count right.final = 1)
    (leftPrefixEmpty : (splitPrefixFinal left).1 = []) :
    (splitPrefixFinal right).1 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter rightPrefixMember
  have rightMember : letter ∈ right.toList := by
    rw [toList_eq_splitPrefixFinal]
    exact List.mem_append_left _ rightPrefixMember
  have leftMember : letter ∈ left.toList :=
    (sameCanonicalSupport same letter).2 rightMember
  have letterIsLeftFinal : letter = (splitPrefixFinal left).2 := by
    rw [toList_eq_splitPrefixFinal, leftPrefixEmpty] at leftMember
    simpa using leftMember
  have splitFinals :
      (splitPrefixFinal left).2 = (splitPrefixFinal right).2 :=
    (split_final_eq left).trans <|
      finalEq.trans (split_final_eq right).symm
  have letterIsRightFinal : letter = (splitPrefixFinal right).2 :=
    letterIsLeftFinal.trans splitFinals
  have rightFinalAbsent :=
    splitFinal_not_mem_prefix_of_count_one right rightSimple
  exact rightFinalAbsent (letterIsRightFinal ▸ rightPrefixMember)

private theorem splitPrefix_nil_iff_of_sameCanonical
    {left right : Word Nat}
    (same : SemigroupBasis.CoRoots.S5_400.SameCanonicalSignature left right)
    (finalEq : left.final = right.final)
    (leftSimple : left.toList.count left.final = 1)
    (rightSimple : right.toList.count right.final = 1) :
    (splitPrefixFinal left).1 = [] ↔
      (splitPrefixFinal right).1 = [] := by
  constructor
  · exact splitPrefix_nil_of_sameCanonical
      same finalEq leftSimple rightSimple
  · exact splitPrefix_nil_of_sameCanonical
      same.symm finalEq.symm rightSimple leftSimple

private theorem foldl_eval_congr
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat -> S) :
    forall (letters : List Nat) (initial : S),
      (forall letter, letter ∈ letters ->
        leftValuation letter = rightValuation letter) ->
      letters.foldl
          (fun value letter =>
            semigroup.mul value (leftValuation letter))
          initial =
        letters.foldl
          (fun value letter =>
            semigroup.mul value (rightValuation letter))
          initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (List.Mem.head rest)]
      apply foldl_eval_congr semigroup
      intro tested member
      exact agree tested (List.Mem.tail letter member)

private theorem eval_congr_on_support
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat -> S)
    (word : Word Nat)
    (agree :
      forall letter, letter ∈ word.toList ->
        leftValuation letter = rightValuation letter) :
    semigroup.eval leftValuation word =
      semigroup.eval rightValuation word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [agree head (by simp [Word.toList])]
      apply foldl_eval_congr semigroup
      intro letter member
      exact agree letter (List.Mem.tail head member)

private theorem rightFactor_right_identity (value : Fin 5) :
    rightFactor.mul value (4 : Fin 5) = value := by
  apply Fin.ext
  revert value
  decide

/-- Assigning a globally simple final variable to the identity of `S5_840`
strips it and exposes a valid prefix identity. -/
private theorem right_prefix_valid
    (final : Nat) (left right : Word Nat)
    (finalNotLeft : final ∉ left.toList)
    (finalNotRight : final ∉ right.toList)
    (wholeValid :
      (Identity.mk
        (left ++ Word.singleton final)
        (right ++ Word.singleton final)).SatisfiedBy rightFactor) :
    (Identity.mk left right).SatisfiedBy rightFactor := by
  intro valuation
  let lifted : Nat -> Fin 5 :=
    fun letter => if letter = final then 4 else valuation letter
  have leftAgree :
      rightFactor.eval valuation left =
        rightFactor.eval lifted left := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ final := by
      intro equal
      subst letter
      exact finalNotLeft member
    simp [lifted, different]
  have rightAgree :
      rightFactor.eval valuation right =
        rightFactor.eval lifted right := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ final := by
      intro equal
      subst letter
      exact finalNotRight member
    simp [lifted, different]
  have evaluated := wholeValid lifted
  simp only [Semigroup.eval_append, Semigroup.eval_singleton] at evaluated
  have liftedFinal : lifted final = (4 : Fin 5) := by
    simp [lifted]
  rw [liftedFinal, rightFactor_right_identity,
    rightFactor_right_identity] at evaluated
  exact leftAgree.trans <| evaluated.trans rightAgree.symm

private theorem listWordOfCons_append_final
    (head : Nat) (tail : List Nat) (final : Nat) :
    SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail ++
        Word.singleton final =
      wordOfPrefixFinal (head :: tail) final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal]
  rfl

/-! ## Duplicating a repeated final marker -/

private abbrev ListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis

private theorem derives_of_listDerives_toList
    (left right : Word Nat)
    (derivation : ListDerives left.toList right.toList) :
    Derives targetBasis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord derivation

private theorem listDerivesPowerExpansion (letter : Nat) :
    ListDerives [letter, letter] [letter, letter, letter] := by
  simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
    Word.singleton, Word.append, Word.append_assoc] using
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (SemigroupBasis.CoRoots.Order6FordLord980.derivesPower
        (Word.singleton letter)))

private theorem listDerivesRightDuplication
    (letter gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([letter] ++ (gapHead :: gapTail) ++ [letter])
      ([letter] ++ (gapHead :: gapTail) ++ [letter, letter]) := by
  simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
    Word.singleton, Word.append, Word.append_assoc,
    List.append_assoc] using
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (SemigroupBasis.CoRoots.Order6FordLord980.derivesRightDuplication
        (Word.singleton letter)
        (SemigroupBasis.CoRoots.S5_107.listWordOfCons gapHead gapTail)))

private theorem listDerivesDuplicateFinal
    (stem : List Nat) (final : Nat) (seen : final ∈ stem) :
    ListDerives (stem ++ [final]) (stem ++ [final, final]) := by
  obtain ⟨before, gap, shape⟩ := List.mem_iff_append.mp seen
  cases gap with
  | nil =>
      simpa [shape, List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.prepend before
          (listDerivesPowerExpansion final))
  | cons gapHead gapTail =>
      simpa [shape, List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.prepend before
          (listDerivesRightDuplication final gapHead gapTail))

private theorem derivesDuplicateFinal
    (word : Word Nat)
    (seen : word.final ∈ (splitPrefixFinal word).1) :
    Derives targetBasis word
      (word ++ Word.singleton word.final) := by
  have listed :=
    listDerivesDuplicateFinal
      (splitPrefixFinal word).1 word.final seen
  apply derives_of_listDerives_toList
  rw [Word.toList_append, Word.toList_singleton,
    toList_eq_splitPrefixFinal, split_final_eq]
  simpa [List.append_assoc] using listed

/-! ## Relative deduction over the final marker -/

/-- Completeness first for the embedded right-zero detector and `S5_840`.
The only branching datum is whether the common final variable is globally
simple. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy smallLeftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs := by
  have sourceDerivation :=
    SemigroupBasis.Generated.S5_400PublishedRoots.S5_840.representativeBasisFor.2
      identity rightValid
  have same :=
    SemigroupBasis.CoRoots.S5_400.sameCanonicalSignature_of_derives
      sourceDerivation
  have finalEq : identity.lhs.final = identity.rhs.final :=
    SemigroupBasis.CoRoots.Order6SporadicSection14.rightZeroValid_final_eq
      identity leftValid
  have countIff := finalCountOneIff same finalEq
  by_cases leftSimple :
      identity.lhs.toList.count identity.lhs.final = 1
  · have rightSimple :
        identity.rhs.toList.count identity.rhs.final = 1 :=
      countIff.mp leftSimple
    have prefixesEmpty :=
      splitPrefix_nil_iff_of_sameCanonical
        same finalEq leftSimple rightSimple
    cases leftPrefix : (splitPrefixFinal identity.lhs).1 with
    | nil =>
        have rightPrefix : (splitPrefixFinal identity.rhs).1 = [] :=
          prefixesEmpty.mp leftPrefix
        have leftReconstructed := wordOfPrefixFinal_split identity.lhs
        have rightReconstructed := wordOfPrefixFinal_split identity.rhs
        rw [leftPrefix] at leftReconstructed
        rw [rightPrefix] at rightReconstructed
        simp only [wordOfPrefixFinal_nil] at leftReconstructed
        simp only [wordOfPrefixFinal_nil] at rightReconstructed
        have splitFinals :
            (splitPrefixFinal identity.lhs).2 =
              (splitPrefixFinal identity.rhs).2 :=
          (split_final_eq identity.lhs).trans <|
            finalEq.trans (split_final_eq identity.rhs).symm
        rw [← leftReconstructed, ← rightReconstructed, splitFinals]
        exact Derives.refl _
    | cons leftHead leftTail =>
        cases rightPrefix : (splitPrefixFinal identity.rhs).1 with
        | nil =>
            have impossible := prefixesEmpty.mpr rightPrefix
            rw [leftPrefix] at impossible
            contradiction
        | cons rightHead rightTail =>
            let leftPrefixWord :=
              SemigroupBasis.CoRoots.S5_107.listWordOfCons
                leftHead leftTail
            let rightPrefixWord :=
              SemigroupBasis.CoRoots.S5_107.listWordOfCons
                rightHead rightTail
            let final := (splitPrefixFinal identity.lhs).2
            have splitFinals :
                (splitPrefixFinal identity.lhs).2 =
                  (splitPrefixFinal identity.rhs).2 :=
              (split_final_eq identity.lhs).trans <|
                finalEq.trans (split_final_eq identity.rhs).symm
            have leftFinalAbsentRaw :=
              splitFinal_not_mem_prefix_of_count_one
                identity.lhs leftSimple
            rw [leftPrefix] at leftFinalAbsentRaw
            have leftFinalAbsent : final ∉ leftPrefixWord.toList := by
              simpa [final, leftPrefixWord,
                SemigroupBasis.CoRoots.S5_107.listWordOfCons,
                Word.toList] using leftFinalAbsentRaw
            have rightFinalAbsentRaw :=
              splitFinal_not_mem_prefix_of_count_one
                identity.rhs rightSimple
            rw [rightPrefix] at rightFinalAbsentRaw
            have rightFinalAbsent : final ∉ rightPrefixWord.toList := by
              simpa [final, splitFinals, rightPrefixWord,
                SemigroupBasis.CoRoots.S5_107.listWordOfCons,
                Word.toList] using rightFinalAbsentRaw
            have leftShape :
                leftPrefixWord ++ Word.singleton final = identity.lhs := by
              calc
                leftPrefixWord ++ Word.singleton final =
                    wordOfPrefixFinal (leftHead :: leftTail) final := by
                  simpa [leftPrefixWord] using
                    listWordOfCons_append_final leftHead leftTail final
                _ = wordOfPrefixFinal
                    (splitPrefixFinal identity.lhs).1
                    (splitPrefixFinal identity.lhs).2 := by
                  rw [leftPrefix]
                _ = identity.lhs := wordOfPrefixFinal_split identity.lhs
            have rightShape :
                rightPrefixWord ++ Word.singleton final = identity.rhs := by
              calc
                rightPrefixWord ++ Word.singleton final =
                    rightPrefixWord ++ Word.singleton
                      (splitPrefixFinal identity.rhs).2 := by
                  simp only [final, splitFinals]
                _ = wordOfPrefixFinal
                    (rightHead :: rightTail)
                    (splitPrefixFinal identity.rhs).2 := by
                  simpa [rightPrefixWord] using
                    listWordOfCons_append_final rightHead rightTail
                      (splitPrefixFinal identity.rhs).2
                _ = wordOfPrefixFinal
                    (splitPrefixFinal identity.rhs).1
                    (splitPrefixFinal identity.rhs).2 := by
                  rw [rightPrefix]
                _ = identity.rhs := wordOfPrefixFinal_split identity.rhs
            have wholeValid :
                (Identity.mk
                  (leftPrefixWord ++ Word.singleton final)
                  (rightPrefixWord ++ Word.singleton final)).SatisfiedBy
                    rightFactor := by
              simpa only [leftShape, rightShape] using rightValid
            have prefixValid :=
              right_prefix_valid final leftPrefixWord rightPrefixWord
                leftFinalAbsent rightFinalAbsent wholeValid
            have prefixDerivation :=
              SemigroupBasis.Generated.S5_400PublishedRoots.S5_840.representativeBasisFor.2
                (Identity.mk leftPrefixWord rightPrefixWord) prefixValid
            have lifted :=
              liftS5_400UnderSuffixIdentity prefixDerivation
                (Word.singleton final)
            simpa only [leftShape, rightShape] using lifted
  · have rightNotSimple :
        identity.rhs.toList.count identity.rhs.final ≠ 1 := by
      intro rightSimple
      exact leftSimple (countIff.mpr rightSimple)
    have leftFinalSeen :
        identity.lhs.final ∈ (splitPrefixFinal identity.lhs).1 := by
      simpa only [split_final_eq] using
        splitFinal_mem_prefix_of_count_ne_one identity.lhs leftSimple
    have rightFinalSeen :
        identity.rhs.final ∈ (splitPrefixFinal identity.rhs).1 := by
      simpa only [split_final_eq] using
        splitFinal_mem_prefix_of_count_ne_one identity.rhs rightNotSimple
    have leftDuplicate :=
      derivesDuplicateFinal identity.lhs leftFinalSeen
    have rightDuplicate :=
      derivesDuplicateFinal identity.rhs rightFinalSeen
    have lifted :=
      liftS5_400UnderSuffixIdentity sourceDerivation
        (Word.singleton identity.lhs.final)
    have guarded :
        Derives targetBasis
          (identity.lhs ++ Word.singleton identity.lhs.final)
          (identity.rhs ++ Word.singleton identity.rhs.final) := by
      simpa [finalEq] using lifted
    exact leftDuplicate.trans <| guarded.trans rightDuplicate.symm

def smallIntersectionBasis :
    IntersectionBasis smallLeftFactor rightFactor targetBasis where
  leftModels := modelsS2_4Opposite
  rightModels := modelsS5_840
  complete := derivesOfFactorValid

/-! ## Widening to the requested order-three detector -/

private def widenLeftFactor
    {A : Type u} {B : Type v} {C : Type w} {X : Type z}
    {sourceLeft : Semigroup A} {targetLeft : Semigroup B}
    {fixedRight : Semigroup C}
    {candidate : List (Identity X)}
    (source : IntersectionBasis sourceLeft fixedRight candidate)
    (targetModels : Models targetLeft candidate)
    (into : Embedding sourceLeft targetLeft) :
    IntersectionBasis targetLeft fixedRight candidate where
  leftModels := targetModels
  rightModels := source.rightModels
  complete := by
    intro identity targetValid rightValid
    exact source.complete identity
      (into.pullback_identity identity targetValid) rightValid

def factorIntersectionBasis :
    IntersectionBasis targetLeftFactor rightFactor targetBasis :=
  widenLeftFactor smallIntersectionBasis modelsS3_15Opposite
    SemigroupBasis.CoRoots.Order6FactorPairS3_15OppositeWidening.s2_4OppositeEmbeddingS3_15Opposite

/-- The exact intersection object requested by the generated order-six
wrapper, stated with the authoritative displayed-basis constant. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup
      SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_9808750adcf41d94.basis := by
  simpa only [targetBasis,
    SemigroupBasis.CoRoots.Order6FordLord980.basis_eq_displayed] using
    factorIntersectionBasis

end SemigroupBasis.CoRoots.Order6FordLord980RelativeTransfer

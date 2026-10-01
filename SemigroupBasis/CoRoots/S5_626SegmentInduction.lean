import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_626Normalization

namespace SemigroupBasis.CoRoots.S5_626

open SemigroupBasis
open SemigroupBasis.Examples

abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons :=
  S5_107.listWordOfCons

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

/-- The neutral pair installed before the original word.  Since the original
word starts with `word.head`, this is the protected initial triple followed
by the unchanged original tail. -/
def protectedInitialExpansion (word : Word Nat) : Word Nat :=
  (Word.singleton word.head ++ Word.singleton word.head) ++ word

@[simp]
theorem protectedInitialExpansion_toList (word : Word Nat) :
    (protectedInitialExpansion word).toList =
      word.head :: word.head :: word.toList := by
  simp [protectedInitialExpansion, Word.toList]

/-- Install a neutral initial pair as soon as any later occurrence of the
initial letter is available.  If that occurrence is adjacent, `x² = x⁴`
does the job.  Otherwise `x u x = x³ u x` installs the pair before the
entire nonempty intervening block.  In both cases every later marker remains
in its original order. -/
theorem listDerivesProtectedInitialExpansion
    (initial : Nat) (tail : List Nat)
    (repeated : initial ∈ tail) :
    ListDerives
      (initial :: tail)
      (initial :: initial :: initial :: tail) := by
  obtain ⟨before, after, split⟩ :=
    List.mem_iff_append.mp repeated
  cases before with
  | nil =>
      have core :=
        S5_107.ListDerives.ofWord
          (derivesSquareExpansion (Word.singleton initial))
      simpa [split, Word.singleton, Word.append,
        List.append_assoc] using core.append after
  | cons middleHead middleTail =>
      have core :=
        S5_107.ListDerives.ofWord
          (derivesInitialTripleLift
            (Word.singleton initial)
            (listWordOfCons middleHead middleTail))
      simpa [split, listWordOfCons, Word.singleton, Word.append,
        List.append_assoc] using core.append after

theorem derivesProtectedInitialExpansion
    (word : Word Nat) (repeated : word.head ∈ word.tail) :
    Derives basis word (protectedInitialExpansion word) := by
  cases word with
  | mk head tail =>
      have expanded :=
        listDerivesProtectedInitialExpansion head tail repeated
      have asWords := S5_107.ListDerives.toWord expanded
      simpa [listWordOfCons, protectedInitialExpansion,
        Word.singleton, Word.append] using asWords

theorem derivesProtectedInitialContraction
    (word : Word Nat) (repeated : word.head ∈ word.tail) :
    Derives basis (protectedInitialExpansion word) word :=
  Derives.symm (derivesProtectedInitialExpansion word repeated)

theorem initialRepeated_of_needsInitialRepair
    (word : Word Nat) (repair : needsInitialRepair word) :
    word.head ∈ word.tail := by
  simpa [InitialOccursExactlyOnce] using repair.1

theorem segmentedBaseRepeated_of_repeated_noRepair
    (word : Word Nat) (repeated : word.head ∈ word.tail)
    (noRepair : ¬ needsInitialRepair word) :
    (segmentedParityBaseWord word).head ∈
      (segmentedParityBaseWord word).tail := by
  have sourceRepeated :
      ¬ InitialOccursExactlyOnce word := by
    simpa [InitialOccursExactlyOnce] using repeated
  have baseRepeated :
      ¬ InitialOccursExactlyOnce
        (segmentedParityBaseWord word) := by
    intro baseSimple
    exact noRepair ⟨sourceRepeated, baseSimple⟩
  simpa [InitialOccursExactlyOnce] using baseRepeated

/-- Replay an arbitrary derivation in the complete reversed affine basis
behind a fixed nonempty prefix.  The three generator cases are respectively
`p x = p x³`, `p x y x² = p x y`, and
`p x y² x = p x y x y`.  Consequently every recursive context and
substitution step remains behind `prefix`; no first-occurrence marker in the
prefix is crossed. -/
theorem liftAffineOppositeUnderPrefix
    {left right : Word Nat}
    (derivation :
      Derives affineParityFourOppositeBasis left right)
    (stem : Word Nat) (sigma : Nat → Word Nat) :
    Derives basis
      (stem ++ left.bind sigma)
      (stem ++ right.bind sigma) := by
  induction derivation generalizing stem sigma with
  | fromBasis member =>
      change _ ∈ reversedBasis affineParityFourBasis at member
      obtain ⟨direct, directMember, rfl⟩ := List.mem_map.mp member
      simp only [affineParityFourBasis, List.mem_cons,
        List.not_mem_nil, or_false] at directMember
      rcases directMember with rfl | rfl | rfl
      · simpa [affineParityPowerLaw, affineParityX,
          affineParityXXX, Identity.reversed, Word.reverse,
          Word.reverseAux, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using
          derivesTailCube stem (sigma 0)
      · simpa [affineParitySquareReturnLaw,
          affineParityXXYX, affineParityYX, Identity.reversed,
          Word.reverse, Word.reverseAux, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using
          (derivesMarkerSquareLift
            stem (sigma 0) (sigma 1)).symm
      · simpa [affineParityMiddleSquareLaw,
          affineParityXYYX, affineParityYXYX, Identity.reversed,
          Word.reverse, Word.reverseAux, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using
          Derives.prepend stem
            (derivesSystemThreeSwap (sigma 0) (sigma 1)).symm
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact Derives.symm (induction stem sigma)
  | trans _ _ firstIH secondIH =>
      exact Derives.trans
        (firstIH stem sigma) (secondIH stem sigma)
  | prepend pre _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (stem ++ pre.bind sigma) sigma
  | appendRight _ post induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (induction stem sigma) (post.bind sigma)
  | subst _ tau induction =>
      simpa [bind_bind] using
        induction stem
          (fun letter => (tau letter).bind sigma)

/-- Factor validity is enough to replay the corresponding affine derivation
behind any protected prefix.  This is a derivation simulation, not a transfer
of the factor's completeness endpoint to `S5_626`. -/
theorem derivesAffineEquivalentUnderPrefix
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        affineParityFactorTable.semigroup.opposite)
    (stem : Word Nat) :
    Derives basis
      (stem ++ identity.lhs)
      (stem ++ identity.rhs) := by
  have factorDerivation :=
    affineFactorDerivesOfValid identity valid
  have lifted :=
    liftAffineOppositeUnderPrefix
      factorDerivation stem Word.singleton
  simpa [bind_singleton] using lifted

/-- The repeated-initial branch is reduced to one pure semantic bridge.  Once
`word` and the chosen segmented base are known to agree in the affine
opposite factor, the initial pair is installed before all markers and the
entire affine derivation runs behind that pair. -/
theorem derivesRepeatedInitialToProtectedBase
    (word base : Word Nat)
    (repeated : word.head ∈ word.tail)
    (affineValid :
      (Identity.mk word base).SatisfiedBy
        affineParityFactorTable.semigroup.opposite) :
    Derives basis word
      ((Word.singleton word.head ++ Word.singleton word.head) ++ base) := by
  exact (derivesProtectedInitialExpansion word repeated).trans <|
    derivesAffineEquivalentUnderPrefix
      (Identity.mk word base) affineValid
      (Word.singleton word.head ++ Word.singleton word.head)

/-- If the target base still repeats its initial variable, the protected pair
can be removed after the factor derivation.  This is the no-repair repeated
branch of the eventual normalizer, parameterized only by the still-missing
affine validity of the segmented base. -/
theorem derivesRepeatedInitialToRepeatedBase
    (word base : Word Nat)
    (repeated : word.head ∈ word.tail)
    (sameHead : base.head = word.head)
    (baseRepeated : base.head ∈ base.tail)
    (affineValid :
      (Identity.mk word base).SatisfiedBy
        affineParityFactorTable.semigroup.opposite) :
    Derives basis word base := by
  have protectedDerivation :=
    derivesRepeatedInitialToProtectedBase
      word base repeated affineValid
  have contraction :=
    derivesProtectedInitialContraction base baseRepeated
  change Derives basis
    ((Word.singleton base.head ++ Word.singleton base.head) ++ base)
    base at contraction
  rw [sameHead] at contraction
  exact protectedDerivation.trans contraction

theorem derivesRepairBranchToProtectedBase
    (word : Word Nat) (repair : needsInitialRepair word)
    (affineValid :
      (Identity.mk word (segmentedParityBaseWord word)).SatisfiedBy
        affineParityFactorTable.semigroup.opposite) :
    Derives basis word
      ((Word.singleton word.head ++ Word.singleton word.head) ++
        segmentedParityBaseWord word) :=
  derivesRepeatedInitialToProtectedBase word
    (segmentedParityBaseWord word)
    (initialRepeated_of_needsInitialRepair word repair)
    affineValid

theorem derivesRepeatedNoRepairToSegmentedBase
    (word : Word Nat) (repeated : word.head ∈ word.tail)
    (noRepair : ¬ needsInitialRepair word)
    (affineValid :
      (Identity.mk word (segmentedParityBaseWord word)).SatisfiedBy
        affineParityFactorTable.semigroup.opposite) :
    Derives basis word (segmentedParityBaseWord word) :=
  derivesRepeatedInitialToRepeatedBase word
    (segmentedParityBaseWord word) repeated
    (segmentedParityBaseWord_head word)
    (segmentedBaseRepeated_of_repeated_noRepair
      word repeated noRepair)
    affineValid

/-- All repeated-initial words reach the actual segmented normal target once
the pure affine validity of the base word is supplied.  The repair case keeps
the protected pair; the no-repair case removes it because the base itself
still repeats the initial variable. -/
theorem derivesRepeatedInitialToSegmentedNormal
    (word : Word Nat) (repeated : word.head ∈ word.tail)
    (affineValid :
      (Identity.mk word (segmentedParityBaseWord word)).SatisfiedBy
        affineParityFactorTable.semigroup.opposite) :
    Derives basis word (segmentedParityNormalWord word) := by
  by_cases repair : needsInitialRepair word
  · have normalized :=
      derivesRepairBranchToProtectedBase word repair affineValid
    rw [segmentedParityNormalWord_of_repair_target word repair]
    exact normalized
  · have normalized :=
      derivesRepeatedNoRepairToSegmentedBase
        word repeated repair affineValid
    rw [segmentedParityNormalWord_of_no_repair word repair]
    exact normalized

/- The extraction and context-uniform derivation induction stop at an explicit
affine-validity parameter.  `S5_626AffineBridge` discharges that parameter;
`S5_626Completeness` handles the globally simple branch separately. -/

end SemigroupBasis.CoRoots.S5_626

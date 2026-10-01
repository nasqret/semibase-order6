import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank047
import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_353Opposite
import SemigroupBasis.CoRoots.Order6GenericCASSubdirectS4_11Family

/-!
# An unrestricted `S3_16 × S4_11` family seed

The right factor is the independently certified cyclic semigroup `C(4,1)`,
which separates word lengths into the exact one-, two-, three-, and
at-least-four strata.  The already kernel-green rank-018 seed identifies the
actual left factor with the complete first-occurrence left regular band.

For long words the frozen `xxyzt = xyzt` first inserts a duplicate initial
block.  Three applications of the independently displayed `xxy = xyy` then
transport that duplicate across any three nonempty context blocks.  This
replays left-regular-band idempotence behind every three-block prefix; the
separate displayed `xxy = xyx` similarly replays regularity.  Consequently the
entire existing unrestricted left-regular-band derivation lifts behind three
copies of the common initial variable.  The copies are inserted and removed
using only the long displayed law.  Exact short-word normal forms use the two
displayed three-letter laws directly.

No finite-window argument, unrecorded cross-family owner seed, or unrestricted
premise is used.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank047.Seed

open SemigroupBasis
open SemigroupBasis.Examples

universe u v

private def instantiateFour
    (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | letter + 4 => Word.singleton (letter + 4)

/-- Frozen law 00 moves a repeated block across the next nonempty block. -/
theorem derivesDuplicateReassociate (first second : Word Nat) :
    Derives basis
      ((first ++ first) ++ second)
      ((first ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1]) (Word.mk 0 [1, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateFour first second second second)
  simpa [instantiateFour, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 01 transfers a duplicated block to the next block. -/
theorem derivesDuplicateTransfer (first second : Word Nat) :
    Derives basis
      ((first ++ first) ++ second)
      ((first ++ second) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1]) (Word.mk 0 [1, 1]) :=
    Derives.fromBasis (e := law01) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateFour first second second second)
  simpa [instantiateFour, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 02 cancels one duplicated initial block before three blocks. -/
theorem derivesLongHeadContraction
    (first second third fourth : Word Nat) :
    Derives basis
      ((((first ++ first) ++ second) ++ third) ++ fourth)
      (((first ++ second) ++ third) ++ fourth) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 2, 3]) (Word.mk 0 [1, 2, 3]) :=
    Derives.fromBasis (e := law02) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateFour first second third fourth)
  simpa [instantiateFour, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- A duplicated head walks across three blocks, making the next block
idempotent behind every genuine three-block context. -/
theorem derivesThreePrefixIdempotence
    (first second third block : Word Nat) :
    Derives basis
      (((first ++ second) ++ third) ++ block)
      (((first ++ second) ++ third) ++ (block ++ block)) := by
  have insert :=
    (derivesLongHeadContraction first second third block).symm
  have firstShift :
      Derives basis
        ((((first ++ first) ++ second) ++ third) ++ block)
        ((((first ++ second) ++ second) ++ third) ++ block) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesDuplicateTransfer first second) (third ++ block)
  have secondShift :
      Derives basis
        ((((first ++ second) ++ second) ++ third) ++ block)
        ((((first ++ second) ++ third) ++ third) ++ block) := by
    simpa [Word.append_assoc] using
      Derives.prepend first <|
        Derives.appendRight
          (derivesDuplicateTransfer second third) block
  have thirdShift :
      Derives basis
        ((((first ++ second) ++ third) ++ third) ++ block)
        (((first ++ second) ++ third) ++ (block ++ block)) := by
    simpa [Word.append_assoc] using
      Derives.prepend (first ++ second)
        (derivesDuplicateTransfer third block)
  exact insert.trans
    (firstShift.trans (secondShift.trans thirdShift))

/-- The other displayed three-letter law replays left-regular-band regularity
behind the same arbitrary three-block context. -/
theorem derivesThreePrefixRegularity
    (first second third block next : Word Nat) :
    Derives basis
      (((first ++ second) ++ third) ++ (block ++ next))
      (((first ++ second) ++ third) ++ ((block ++ next) ++ block)) := by
  have duplicate :
      Derives basis
        ((((first ++ second) ++ third) ++ block) ++ next)
        ((((first ++ second) ++ third) ++ (block ++ block)) ++ next) :=
    Derives.appendRight
      (derivesThreePrefixIdempotence first second third block) next
  have reassociate :
      Derives basis
        ((((first ++ second) ++ third) ++ (block ++ block)) ++ next)
        (((first ++ second) ++ third) ++ ((block ++ next) ++ block)) := by
    simpa [Word.append_assoc] using
      Derives.prepend ((first ++ second) ++ third)
        (derivesDuplicateReassociate block next)
  simpa [Word.append_assoc] using duplicate.trans reassociate

private theorem bind_append
    (first second : Word Nat) (substitution : Nat → Word Nat) :
    (first ++ second).bind substitution =
      first.bind substitution ++ second.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp

/-- Replay the complete left-regular-band derivation behind any three
nonempty context blocks, retaining arbitrary simultaneous substitutions. -/
theorem liftLeftRegularBand
    {left right : Word Nat}
    (derivation : Derives leftRegularBandThreeBasis left right)
    (first second third : Word Nat)
    (substitution : Nat → Word Nat) :
    Derives basis
      (((first ++ second) ++ third) ++ left.bind substitution)
      (((first ++ second) ++ third) ++ right.bind substitution) := by
  induction derivation generalizing first second third substitution with
  | fromBasis member =>
      simp only [leftRegularBandThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [lrbIdempotenceLaw, lrbX, lrbXX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          derivesThreePrefixIdempotence
            first second third (substitution 0)
      · simpa [lrbRegularLaw, lrbXY, lrbXYX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          derivesThreePrefixRegularity
            first second third (substitution 0) (substitution 1)
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact Derives.symm
        (induction first second third substitution)
  | trans _ _ initial final =>
      exact (initial first second third substitution).trans
        (final first second third substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction first second
          (third ++ stem.bind substitution) substitution
  | appendRight _ suffix induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (induction first second third substitution)
          (suffix.bind substitution)
  | subst _ next induction =>
      simpa [bind_bind] using
        induction first second third
          (fun letter => (next letter).bind substitution)

/-- Every word in the long `C(4,1)` stratum accepts one extra initial copy. -/
theorem derivesHeadInsertion
    (word : Word Nat) (long : 4 ≤ word.toList.length) :
    Derives basis word (Word.singleton word.head ++ word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil => simp [Word.toList] at long
          | cons third remaining =>
              cases remaining with
              | nil => simp [Word.toList] at long
              | cons fourth suffix =>
                  simpa [Word.singleton, Word.append,
                    Word.append_assoc] using
                    (derivesLongHeadContraction
                      (Word.singleton head)
                      (Word.singleton second)
                      (Word.singleton third)
                      (Word.mk fourth suffix)).symm

/-- Reapply the same displayed insertion in increasingly prefixed contexts. -/
theorem derivesTripleHeadInsertion
    (word : Word Nat) (long : 4 ≤ word.toList.length) :
    Derives basis word
      (((Word.singleton word.head ++ Word.singleton word.head) ++
          Word.singleton word.head) ++ word) := by
  let headWord := Word.singleton word.head
  have first := derivesHeadInsertion word long
  have second := Derives.prepend headWord first
  have third := Derives.prepend (headWord ++ headWord) first
  simpa [headWord, Word.append_assoc] using
    first.trans (second.trans third)

/-- Canonical three-letter representative determined solely by the complete
first-occurrence sequence. -/
private def canonicalThree (fallback : Nat) : List Nat → Word Nat
  | [] => Word.mk fallback [fallback, fallback]
  | [first] => Word.mk first [first, first]
  | [first, second] => Word.mk first [first, second]
  | first :: second :: third :: _ => Word.mk first [second, third]

/-- Displayed laws 00 and 01 identify precisely the three possible
two-support, three-letter words `xxy`, `xyx`, and `xyy`. -/
theorem derivesThreeCanonical (first second third : Nat) :
    Derives basis (Word.mk first [second, third])
      (canonicalThree first
        (firstOccurrenceSequence [first, second, third])) := by
  by_cases secondEqual : second = first
  · subst second
    by_cases thirdEqual : third = first
    · subst third
      simpa [canonicalThree, firstOccurrenceSequence] using
        (Derives.refl (basis := basis)
          (Word.mk first [first, first]))
    · simpa [canonicalThree, firstOccurrenceSequence, thirdEqual] using
        (Derives.refl (basis := basis)
          (Word.mk first [first, third]))
  · by_cases thirdEqual : third = first
    · subst third
      simpa [canonicalThree, firstOccurrenceSequence, secondEqual,
        Word.singleton, Word.append] using
          (derivesDuplicateReassociate
            (Word.singleton first) (Word.singleton second)).symm
    · by_cases sameTail : third = second
      · subst third
        simpa [canonicalThree, firstOccurrenceSequence, secondEqual,
          Word.singleton, Word.append] using
            (derivesDuplicateTransfer
              (Word.singleton first) (Word.singleton second)).symm
      · simpa [canonicalThree, firstOccurrenceSequence, secondEqual,
          thirdEqual, sameTail] using
            (Derives.refl (basis := basis)
              (Word.mk first [second, third]))

/-- The already independently kernel-green rank-018 owner identifies this
literal left factor with the complete first-occurrence detector. -/
theorem firstOccurrences_of_leftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank018.Seed.firstOccurrences_of_leftValid
    identity valid

/-- The exact same reviewed embedding supplies a genuine unrestricted
left-regular-band derivation without any owner premise. -/
theorem leftValid_leftRegularBand
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    Derives leftRegularBandThreeBasis identity.lhs identity.rhs :=
  leftRegularBandThreeBasis_complete.2 identity <|
    SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank018.Seed.canonicalLeftIntoActual.pullback_identity
      identity valid

/-- Independent unrestricted completeness for the exact authenticated
three-law `S3_16 × S4_11` package. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have order := firstOccurrences_of_leftValid identity leftValid
  have lower := leftValid_leftRegularBand identity leftValid
  have strata :=
      SemigroupBasis.CoRoots.Order6GenericCASSubdirectS4_11Family.lengthShape
        identity rightValid
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  change
    firstOccurrenceSequence (leftHead :: leftTail) =
      firstOccurrenceSequence (rightHead :: rightTail) at order
  have heads : leftHead = rightHead := by
    have equal := congrArg List.head? order
    simpa [firstOccurrenceSequence] using equal
  subst rightHead
  rcases strata with
    ⟨leftOne, rightOne⟩ |
    ⟨leftTwo, rightTwo⟩ |
    ⟨leftThree, rightThree⟩ |
    ⟨leftLong, rightLong⟩
  · cases leftTail with
    | nil =>
      cases rightTail with
      | nil => exact Derives.refl _
      | cons _ _ => simp [Word.toList] at rightOne
    | cons _ _ => simp [Word.toList] at leftOne
  · cases leftTail with
    | nil => simp [Word.toList] at leftTwo
    | cons leftSecond leftRest =>
      cases leftRest with
      | cons _ _ => simp [Word.toList] at leftTwo
      | nil =>
        cases rightTail with
        | nil => simp [Word.toList] at rightTwo
        | cons rightSecond rightRest =>
          cases rightRest with
          | cons _ _ => simp [Word.toList] at rightTwo
          | nil =>
            by_cases leftRepeated : leftSecond = leftHead
            · subst leftSecond
              by_cases rightRepeated : rightSecond = leftHead
              · subst rightSecond
                exact Derives.refl _
              · simp [firstOccurrenceSequence, rightRepeated] at order
            · by_cases rightRepeated : rightSecond = leftHead
              · subst rightSecond
                simp [firstOccurrenceSequence, leftRepeated] at order
              · have tails : leftSecond = rightSecond := by
                  simpa [firstOccurrenceSequence,
                    leftRepeated, rightRepeated] using order
                subst rightSecond
                exact Derives.refl _
  · cases leftTail with
    | nil => simp [Word.toList] at leftThree
    | cons leftSecond leftRest =>
      cases leftRest with
      | nil => simp [Word.toList] at leftThree
      | cons leftThird leftRemaining =>
        cases leftRemaining with
        | cons _ _ => simp [Word.toList] at leftThree
        | nil =>
          cases rightTail with
          | nil => simp [Word.toList] at rightThree
          | cons rightSecond rightRest =>
            cases rightRest with
            | nil => simp [Word.toList] at rightThree
            | cons rightThird rightRemaining =>
              cases rightRemaining with
              | cons _ _ => simp [Word.toList] at rightThree
              | nil =>
                have leftNormal :=
                  derivesThreeCanonical leftHead leftSecond leftThird
                have rightNormal :=
                  derivesThreeCanonical leftHead rightSecond rightThird
                have sameNormal :
                    canonicalThree leftHead
                        (firstOccurrenceSequence
                          [leftHead, leftSecond, leftThird]) =
                      canonicalThree leftHead
                        (firstOccurrenceSequence
                          [leftHead, rightSecond, rightThird]) := by
                  exact congrArg (canonicalThree leftHead) order
                rw [sameNormal] at leftNormal
                exact leftNormal.trans rightNormal.symm
  · let headWord := Word.singleton leftHead
    have lifted :=
      liftLeftRegularBand lower headWord headWord headWord
        Word.singleton
    rw [bind_singleton, bind_singleton] at lifted
    have leftInserted :=
      derivesTripleHeadInsertion
        (Word.mk leftHead leftTail) leftLong
    have rightInserted :=
      derivesTripleHeadInsertion
        (Word.mk leftHead rightTail) rightLong
    exact leftInserted.trans (lifted.trans rightInserted.symm)

/-- Construct the pair structure only after its unrestricted factor proof. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Reusable reviewed quotient normalizer for both authenticated classes. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_5683_representative_basis :
    BasisFor S6_5683.table.semigroup basis :=
  S6_5683.representative_basis_of_normalizer normalizer

theorem s6_5683_opposite_basis :
    BasisFor S6_5683.table.semigroup.opposite (reversedBasis basis) :=
  S6_5683.opposite_basis_of_normalizer normalizer

theorem s6_5733_representative_basis :
    BasisFor S6_5733.table.semigroup basis :=
  S6_5733.representative_basis_of_normalizer normalizer

theorem s6_5733_opposite_basis :
    BasisFor S6_5733.table.semigroup.opposite (reversedBasis basis) :=
  S6_5733.opposite_basis_of_normalizer normalizer

/-- Subsequent transport retains explicit law derivations and both genuinely
proved unrestricted factor-theory implications. -/
noncomputable def transportedNormalizer
    {A : Type u} {B : Type v}
    {targetLeft : Semigroup A} {targetRight : Semigroup B}
    {targetBasis : List (Identity Nat)}
    (lawDerivations :
      ∀ law : Identity Nat,
        law ∈ basis → Derives targetBasis law.lhs law.rhs)
    (leftTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetLeft →
          identity.SatisfiedBy leftTable.semigroup)
    (rightTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetRight →
          identity.SatisfiedBy rightTable.semigroup) :
    IntersectionNormalizer targetLeft targetRight targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer lawDerivations leftTheory rightTheory

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank047.Seed

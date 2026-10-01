import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_303
import SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank039
import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090
import SemigroupBasis.CoRoots.S5_402SignatureBridge

/-!
# Exact rank-039 cyclic-parity/simple-successor owner boundary

The independently complete thirteen-law `S5_402` calculus begins with three
occurrence-parity-changing axioms.  Its remaining ten axioms occur literally
in the frozen sixteen-law `S2_2 × S5_402` basis.  All thirteen lower axioms
can nevertheless be lifted BETWEEN WHOLE SQUARES, and the standard C1
structural induction transports every arbitrary context and substitution.

Consequently every identity valid in the actual complete right factor has an
unconditional displayed derivation between its whole-word squares.  Cancelling
those squares still requires an explicit owner proof preserving BOTH genuine
cyclic occurrence parity and the complete `S5_402` simple-successor signature.
That missing premise is kept explicit in every class endpoint.

Three tempting unrestricted shortcuts are formally refuted: the prior rank-038
basis is false on `S5_402`, the first three complete lower axioms are false on
the actual cyclic factor, and cyclic-two validity does not imply rank-090's
`S3_16` left-factor validity.  No finite-table separation, unconditional
intersection, recording receipt, acceptance, or seal is asserted.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank039.ParitySuccessorBridge

open SemigroupBasis
open SemigroupBasis.Examples

abbrev SameOccurrenceParity :=
  SemigroupBasis.CoRoots.S5_441Invariant.SameOccurrenceParity

/-- The ACTUAL lower factor contributes its complete head/capped/simple-
successor signature; the ACTUAL cyclic factor contributes every parity. -/
structure SameFactorSignature (left right : Word Nat) : Prop where
  successor : SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature left right
  parity : SameOccurrenceParity left right

/-- Both actual factors independently provide their genuine invariant. -/
theorem sameFactorSignature_of_factorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    SameFactorSignature identity.lhs identity.rhs where
  successor := SemigroupBasis.CoRoots.S5_402.sameSignature_of_valid
    identity rightValid
  parity := SemigroupBasis.CoRoots.S5_441Invariant.sameOccurrenceParity_of_s2_2_valid
    identity leftValid

/-- The complete lower power law changes an ACTUAL cyclic occurrence parity. -/
theorem lowerPower_not_leftValid :
    ¬ SemigroupBasis.CoRoots.S5_402.powerLaw.SatisfiedBy
      leftTable.semigroup := by
  intro valid
  have witness := valid (fun _ => (1 : Fin 2))
  change (0 : Fin 2) = 1 at witness
  omega

/-- The complete lower left-duplication law changes the same cyclic parity. -/
theorem lowerLeftDuplication_not_leftValid :
    ¬ SemigroupBasis.CoRoots.S5_402.leftDuplicationLaw.SatisfiedBy
      leftTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter => if letter = 0 then (1 : Fin 2) else (0 : Fin 2))
  change (0 : Fin 2) = 1 at witness
  omega

/-- The complete lower right-duplication law also changes cyclic parity. -/
theorem lowerRightDuplication_not_leftValid :
    ¬ SemigroupBasis.CoRoots.S5_402.rightDuplicationLaw.SatisfiedBy
      leftTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter => if letter = 0 then (1 : Fin 2) else (0 : Fin 2))
  change (0 : Fin 2) = 1 at witness
  omega

/-- Therefore unrestricted direct transport of the complete lower calculus
into the displayed intersection is mathematically impossible. -/
theorem fullLowerLawTransport_refuted :
    ¬ (∀ law : Identity Nat,
      law ∈ SemigroupBasis.CoRoots.S5_402.basis →
        Derives basis law.lhs law.rhs) := by
  intro transport
  have derived := transport
    SemigroupBasis.CoRoots.S5_402.powerLaw
    (by simp [SemigroupBasis.CoRoots.S5_402.basis])
  exact lowerPower_not_leftValid (derived.sound leftModels)

/-- Rank-038's protected-prefix contraction is false on ACTUAL `S5_402`. -/
theorem rank038TriplePrefix_not_rightValid :
    ¬ SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank038.law01.SatisfiedBy
      rightTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter => if letter = 0 then (1 : Fin 5) else (4 : Fin 5))
  change (0 : Fin 5) = 2 at witness
  omega

/-- Rank-038's head-changing rotation is false on ACTUAL `S5_402`. -/
theorem rank038Rotation_not_rightValid :
    ¬ SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank038.law02.SatisfiedBy
      rightTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter => if letter = 0 then (3 : Fin 5) else (4 : Fin 5))
  change (3 : Fin 5) = 4 at witness
  omega

/-- Rank-038's closed swap changes an ACTUAL globally-simple successor. -/
theorem rank038InteriorSwap_not_rightValid :
    ¬ SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank038.law03.SatisfiedBy
      rightTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter =>
      if letter = 0 then (3 : Fin 5) else
        if letter = 1 then (1 : Fin 5) else (4 : Fin 5))
  change (2 : Fin 5) = 0 at witness
  omega

/-- The independently green rank-038 normalizer cannot be transported into
rank 039 because three of its displayed source laws fail in the real target. -/
theorem rank038DisplayedLawTransport_refuted :
    ¬ (∀ law : Identity Nat,
      law ∈ SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank038.basis →
        Derives basis law.lhs law.rhs) := by
  intro transport
  have derived := transport
    SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank038.law01
    (by simp [SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank038.basis])
  exact rank038TriplePrefix_not_rightValid (derived.sound rightModels)

/-- Cyclic-two commutativity is genuinely valid on the ACTUAL target left. -/
theorem cyclicCommutativity_leftValid :
    cyclicCommutativityLaw.SatisfiedBy leftTable.semigroup := by
  change cyclicCommutativityLaw.SatisfiedBy
    SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup
  rw [SemigroupBasis.CoRoots.S5_441Invariant.catalogueS2_2_table_eq_cyclicTwo]
  exact cyclicTwoBasis_models cyclicCommutativityLaw
    (by simp [cyclicTwoBasis])

/-- The exact same cyclic law fails on the earlier rank-090 left detector. -/
theorem cyclicCommutativity_not_rank090LeftValid :
    ¬ cyclicCommutativityLaw.SatisfiedBy
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.leftTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter => if letter = 0 then (2 : Fin 3) else (0 : Fin 3))
  change (2 : Fin 3) = 0 at witness
  omega

/-- The green `S3_16 × S5_402` seed cannot supply the independently required
left-factor implication of `transportNormalizer`. -/
theorem rank090LeftTheoryImplication_refuted :
    ¬ (∀ identity : Identity Nat,
      identity.SatisfiedBy leftTable.semigroup →
        identity.SatisfiedBy
          SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.leftTable.semigroup) := by
  intro implication
  exact cyclicCommutativity_not_rank090LeftValid
    (implication cyclicCommutativityLaw cyclicCommutativity_leftValid)

/-- Exactly the ten parity-neutral laws after the lower owner's false prefix. -/
def lowerBalancedTail : List (Identity Nat) :=
  [SemigroupBasis.CoRoots.S5_402.squareAlternationLaw,
   SemigroupBasis.CoRoots.S5_402.squareCrossingLaw,
   SemigroupBasis.CoRoots.S5_402.factorLeftLaw,
   SemigroupBasis.CoRoots.S5_402.factorMiddleLeftLaw,
   SemigroupBasis.CoRoots.S5_402.factorMiddleRightLaw,
   SemigroupBasis.CoRoots.S5_402.factorSwapLaw,
   SemigroupBasis.CoRoots.S5_402.factorRightLaw,
   SemigroupBasis.CoRoots.S5_402.simpleBlockSwapLaw,
   SemigroupBasis.CoRoots.S5_402.successorShiftLaw,
   SemigroupBasis.CoRoots.S5_402.successorReverseLaw]

/-- The safe tail is the literal complete owner's basis with three laws cut. -/
theorem lowerBalancedTail_matches :
    lowerBalancedTail = SemigroupBasis.CoRoots.S5_402.basis.drop 3 := by
  decide

/-- Every parity-neutral lower axiom is already a literal frozen target law. -/
theorem lowerBalancedLawDerives
    (law : Identity Nat) (member : law ∈ lowerBalancedTail) :
    Derives basis law.lhs law.rhs := by
  simp only [lowerBalancedTail, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact Derives.fromBasis (e := law04) (by simp [basis])
  · exact Derives.fromBasis (e := law05) (by simp [basis])
  · exact Derives.fromBasis (e := law07) (by simp [basis])
  · exact Derives.fromBasis (e := law08) (by simp [basis])
  · exact Derives.fromBasis (e := law09) (by simp [basis])
  · exact Derives.fromBasis (e := law10) (by simp [basis])
  · exact Derives.fromBasis (e := law11) (by simp [basis])
  · exact Derives.fromBasis (e := law13) (by simp [basis])
  · exact Derives.fromBasis (e := law14) (by simp [basis])
  · exact Derives.fromBasis (e := law15) (by simp [basis])

/-- Structural transport of the ENTIRE safe tail, without either parity-
changing lower duplication or any independent completeness assumption. -/
theorem transportLowerBalancedTail
    {left right : Word Nat}
    (derivation :
      Derives (SemigroupBasis.CoRoots.S5_402.basis.drop 3) left right) :
    Derives basis left right := by
  rw [← lowerBalancedTail_matches] at derivation
  exact Derives.transport lowerBalancedLawDerives derivation

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- Exact frozen pair insertion `u² = u⁴`, not the false `u = u²`. -/
theorem derivesPairExpansion (source : Word Nat) :
    Derives basis
      (source ++ source)
      ((source ++ source) ++ (source ++ source)) := by
  have primitive :
      Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree source source source)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen square factorization `(uv)² = u²v²`. -/
theorem derivesSquareFactorization (first second : Word Nat) :
    Derives basis
      ((first ++ second) ++ (first ++ second))
      ((first ++ first) ++ (second ++ second)) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 0, 1]) :=
    Derives.fromBasis (e := law04) (by simp [basis])
  have substituted :=
    Derives.subst primitive.symm (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Three independent blocks normalize to the ordered product of squares. -/
theorem derivesTripleSquareFactorization
    (first second third : Word Nat) :
    Derives basis
      (((first ++ second) ++ third) ++ ((first ++ second) ++ third))
      (((first ++ first) ++ (second ++ second)) ++ (third ++ third)) := by
  exact (derivesSquareFactorization (first ++ second) third).trans <|
    Derives.appendRight (derivesSquareFactorization first second)
      (third ++ third)

/-- Lower `u² = u³` survives exactly BETWEEN WHOLE SQUARES. -/
theorem derivesLowerPowerSquared (source : Word Nat) :
    Derives basis
      ((source ++ source) ++ (source ++ source))
      (((source ++ source) ++ source) ++
        ((source ++ source) ++ source)) := by
  simpa [Word.append_assoc] using
    Derives.prepend (source ++ source) (derivesPairExpansion source)

/-- Lower `uvu = uuvu` survives between squares via a balanced leading pair. -/
theorem derivesLowerLeftDuplicationSquared
    (first second : Word Nat) :
    Derives basis
      (((first ++ second) ++ first) ++ ((first ++ second) ++ first))
      ((((first ++ first) ++ second) ++ first) ++
        (((first ++ first) ++ second) ++ first)) := by
  have sourceNormal :=
    derivesTripleSquareFactorization first second first
  have targetNormal :=
    derivesTripleSquareFactorization (first ++ first) second first
  have expand :
      Derives basis
        (((first ++ first) ++ (second ++ second)) ++ (first ++ first))
        ((((first ++ first) ++ (first ++ first)) ++
          (second ++ second)) ++ (first ++ first)) :=
    Derives.appendRight
      (Derives.appendRight (derivesPairExpansion first)
        (second ++ second))
      (first ++ first)
  simpa [Word.append_assoc] using
    sourceNormal.trans (expand.trans targetNormal.symm)

/-- Lower `uvu = uvuu` survives between squares via a balanced final pair. -/
theorem derivesLowerRightDuplicationSquared
    (first second : Word Nat) :
    Derives basis
      (((first ++ second) ++ first) ++ ((first ++ second) ++ first))
      (((first ++ second) ++ (first ++ first)) ++
        ((first ++ second) ++ (first ++ first))) := by
  have sourceNormal :=
    derivesTripleSquareFactorization first second first
  have targetNormal :=
    derivesTripleSquareFactorization first second (first ++ first)
  have expand :
      Derives basis
        (((first ++ first) ++ (second ++ second)) ++ (first ++ first))
        (((first ++ first) ++ (second ++ second)) ++
          ((first ++ first) ++ (first ++ first))) :=
    Derives.prepend
      ((first ++ first) ++ (second ++ second))
      (derivesPairExpansion first)
  simpa [Word.append_assoc] using
    sourceNormal.trans (expand.trans targetNormal.symm)

/-- Any already-safe derivation lifts to its entire whole-word square. -/
theorem squareOfDisplayedDerivation
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    Derives basis (left ++ left) (right ++ right) :=
  (Derives.appendRight derivation left).trans <|
    Derives.prepend right derivation

/-- All THIRTEEN lower axioms lift between squares; exactly three need the
new pair insertions, while the other ten transport literally. -/
theorem lowerAxiomSquared
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_402.basis)
    (substitution : Nat → Word Nat) :
    Derives basis
      (identity.lhs.bind substitution ++ identity.lhs.bind substitution)
      (identity.rhs.bind substitution ++ identity.rhs.bind substitution) := by
  simp only [SemigroupBasis.CoRoots.S5_402.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | balanced
  · change
      Derives basis
        ((substitution 0 ++ substitution 0) ++
          (substitution 0 ++ substitution 0))
        (((substitution 0 ++ substitution 0) ++ substitution 0) ++
          ((substitution 0 ++ substitution 0) ++ substitution 0))
    exact derivesLowerPowerSquared (substitution 0)
  · change
      Derives basis
        (((substitution 0 ++ substitution 1) ++ substitution 0) ++
          ((substitution 0 ++ substitution 1) ++ substitution 0))
        ((((substitution 0 ++ substitution 0) ++ substitution 1) ++
            substitution 0) ++
          (((substitution 0 ++ substitution 0) ++ substitution 1) ++
            substitution 0))
    exact derivesLowerLeftDuplicationSquared
      (substitution 0) (substitution 1)
  · change
      Derives basis
        (((substitution 0 ++ substitution 1) ++ substitution 0) ++
          ((substitution 0 ++ substitution 1) ++ substitution 0))
        ((((substitution 0 ++ substitution 1) ++ substitution 0) ++
            substitution 0) ++
          (((substitution 0 ++ substitution 1) ++ substitution 0) ++
            substitution 0))
    simpa [Word.append_assoc] using
      derivesLowerRightDuplicationSquared
        (substitution 0) (substitution 1)
  · have safeMember : identity ∈ lowerBalancedTail := by
      simpa [lowerBalancedTail] using balanced
    exact squareOfDisplayedDerivation <|
      Derives.subst (lowerBalancedLawDerives identity safeMember)
        substitution

private theorem bind_append
    (first second : Word Nat) (substitution : Nat → Word Nat) :
    (first ++ second).bind substitution =
      first.bind substitution ++ second.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (source : Word Nat) (first second : Nat → Word Nat) :
    (source.bind first).bind second =
      source.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (source : Word Nat) :
    source.bind Word.singleton = source := by
  apply Word.toList_injective
  simp

private theorem squareLiftPrepend
    (front : Word Nat) {left right : Word Nat}
    (middle : Derives basis (left ++ left) (right ++ right)) :
    Derives basis
      ((front ++ left) ++ (front ++ left))
      ((front ++ right) ++ (front ++ right)) :=
  (derivesSquareFactorization front left).trans <|
    (Derives.prepend (front ++ front) middle).trans <|
      (derivesSquareFactorization front right).symm

private theorem squareLiftAppend
    {left right : Word Nat} (suffix : Word Nat)
    (middle : Derives basis (left ++ left) (right ++ right)) :
    Derives basis
      ((left ++ suffix) ++ (left ++ suffix))
      ((right ++ suffix) ++ (right ++ suffix)) :=
  (derivesSquareFactorization left suffix).trans <|
    (Derives.appendRight middle (suffix ++ suffix)).trans <|
      (derivesSquareFactorization right suffix).symm

/-- The COMPLETE lower calculus lifts with arbitrary substitutions and both
arbitrary contexts, but only between honest whole-word squares. -/
theorem liftLowerDerivationSquared
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_402.basis left right)
    (substitution : Nat → Word Nat) :
    Derives basis
      (left.bind substitution ++ left.bind substitution)
      (right.bind substitution ++ right.bind substitution) := by
  induction derivation generalizing substitution with
  | fromBasis member =>
      exact lowerAxiomSquared _ member substitution
  | refl => exact Derives.refl _
  | symm _ hypothesis => exact (hypothesis substitution).symm
  | trans _ _ first second =>
      exact (first substitution).trans (second substitution)
  | prepend front _ hypothesis =>
      simpa [bind_append] using
        squareLiftPrepend (front.bind substitution)
          (hypothesis substitution)
  | appendRight _ suffix hypothesis =>
      simpa [bind_append] using
        squareLiftAppend (suffix.bind substitution)
          (hypothesis substitution)
  | subst _ first hypothesis =>
      simpa [bind_bind] using
        hypothesis (fun letter => (first letter).bind substitution)

/-- Independent COMPLETE `S5_402` normalization supplies unrestricted
whole-square derivability for every identity valid in the actual right factor. -/
theorem derivesSquares_of_rightValid
    (identity : Identity Nat)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis
      (identity.lhs ++ identity.lhs)
      (identity.rhs ++ identity.rhs) := by
  have lower := SemigroupBasis.CoRoots.S5_402.basisFor.2
    identity rightValid
  simpa only [bind_singleton] using
    liftLowerDerivationSquared lower Word.singleton

/-- In particular BOTH actual factors jointly yield the proved whole squares;
this is not square cancellation or unrestricted intersection completeness. -/
theorem derivesSquares_of_targetPairValid
    (identity : Identity Nat)
    (_leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis
      (identity.lhs ++ identity.lhs)
      (identity.rhs ++ identity.rhs) :=
  derivesSquares_of_rightValid identity rightValid

/-- Reconstruct genuine cyclic-two validity from the complete parity vector
using the already kernel-green cyclic normalizer. -/
theorem leftValid_of_sameOccurrenceParity
    (identity : Identity Nat)
    (parity : SameOccurrenceParity identity.lhs identity.rhs) :
    identity.SatisfiedBy leftTable.semigroup := by
  have reducedPermutation :
      (parityReduce identity.lhs.toList).Perm
        (parityReduce identity.rhs.toList) :=
    parityReduce_perm_of_parity_eq parity
  have leftNormal := cyclicDerivesNormal identity.lhs
  have rightNormal := cyclicDerivesNormal identity.rhs
  have derivation :
      Derives cyclicTwoBasis identity.lhs identity.rhs := by
    cases leftShape : parityReduce identity.lhs.toList with
    | nil =>
        rw [leftShape] at reducedPermutation
        have rightShape : parityReduce identity.rhs.toList = [] :=
          reducedPermutation.nil_eq.symm
        rw [leftShape] at leftNormal
        rw [rightShape] at rightNormal
        exact leftNormal.trans <|
          (cyclicDerivesCommonSquare
            (Word.singleton identity.lhs.head)
            (Word.singleton identity.rhs.head)).trans
            rightNormal.symm
    | cons first rest =>
        cases rightShape : parityReduce identity.rhs.toList with
        | nil =>
            rw [leftShape, rightShape] at reducedPermutation
            exact False.elim (List.not_perm_cons_nil reducedPermutation)
        | cons second remaining =>
            rw [leftShape] at leftNormal
            rw [rightShape] at rightNormal
            rw [leftShape, rightShape] at reducedPermutation
            exact leftNormal.trans <|
              (cyclicDerivesPermutation
                (Word.mk first rest)
                (Word.mk second remaining)
                reducedPermutation).trans rightNormal.symm
  have cyclicValid : identity.SatisfiedBy cyclicTwo.semigroup :=
    derivation.sound cyclicTwoBasis_models
  rw [← SemigroupBasis.CoRoots.S5_441Invariant.catalogueS2_2_table_eq_cyclicTwo]
    at cyclicValid
  exact cyclicValid

/-- Genuine complete successor-signature agreement reconstructs lower-factor
validity without bounded finite-table inference. -/
theorem rightValid_of_sameSimpleSuccessorSignature
    (identity : Identity Nat)
    (same : SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature
      identity.lhs identity.rhs) :
    identity.SatisfiedBy rightTable.semigroup :=
  (SemigroupBasis.CoRoots.S5_402.derivesOfSameSimpleSuccessorSignature same).sound
    SemigroupBasis.CoRoots.S5_402.models

/-- Exact missing owner proof: preserve the ACTUAL complete successor/head
signature AND occurrence parity in the displayed rank-039 derivation. -/
def ParitySuccessorLift : Prop :=
  ∀ identity : Identity Nat,
    SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature
      identity.lhs identity.rhs →
    SameOccurrenceParity identity.lhs identity.rhs →
      Derives basis identity.lhs identity.rhs

/-- Equivalent missing cancellation, limited to identities independently valid
on BOTH actual target factors. No unguarded cancellation is asserted. -/
def PairValidSquareCancellation : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup →
    identity.SatisfiedBy rightTable.semigroup →
    Derives basis
      (identity.lhs ++ identity.lhs)
      (identity.rhs ++ identity.rhs) →
        Derives basis identity.lhs identity.rhs

/-- The precise owner signature lift is EQUIVALENT to target-pair-valid
whole-square cancellation; neither implication manufactures the owner proof. -/
theorem ownerLift_iff_pairValidSquareCancellation :
    ParitySuccessorLift ↔ PairValidSquareCancellation := by
  constructor
  · intro owner identity leftValid rightValid _
    exact owner identity
      (sameFactorSignature_of_factorValid identity leftValid rightValid).successor
      (sameFactorSignature_of_factorValid identity leftValid rightValid).parity
  · intro cancellation identity successor parity
    have leftValid := leftValid_of_sameOccurrenceParity identity parity
    have rightValid := rightValid_of_sameSimpleSuccessorSignature
      identity successor
    exact cancellation identity leftValid rightValid
      (derivesSquares_of_rightValid identity rightValid)

/-- A supplied independent owner proof yields the target intersection; the
owner premise remains explicit and is NEVER filled by stamping. -/
def intersectionBasis_of_ownerLift
    (owner : ParitySuccessorLift) :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := by
    intro identity leftValid rightValid
    exact owner identity
      (sameFactorSignature_of_factorValid identity leftValid rightValid).successor
      (sameFactorSignature_of_factorValid identity leftValid rightValid).parity

/-- Exact equivalence between the unrestricted target intersection and the
genuinely missing parity/simple-successor owner lift. -/
theorem targetIntersection_iff_ownerLift :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis ↔
      ParitySuccessorLift := by
  constructor
  · intro intersection identity successor parity
    exact intersection.complete identity
      (leftValid_of_sameOccurrenceParity identity parity)
      (rightValid_of_sameSimpleSuccessorSignature identity successor)
  · exact intersectionBasis_of_ownerLift

/-- The reviewed quotient normalizer remains strictly CONDITIONAL. -/
noncomputable def normalizer_of_ownerLift
    (owner : ParitySuccessorLift) :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    (intersectionBasis_of_ownerLift owner)

/-- Conditional first class; no unrestricted owner lift is asserted. -/
theorem s6_4091_representative_basis_of_ownerLift
    (owner : ParitySuccessorLift) :
    BasisFor S6_4091.table.semigroup basis :=
  S6_4091.representative_basis_of_normalizer
    (normalizer_of_ownerLift owner)

/-- Conditional opposite orientation of the first class. -/
theorem s6_4091_opposite_basis_of_ownerLift
    (owner : ParitySuccessorLift) :
    BasisFor S6_4091.table.semigroup.opposite (reversedBasis basis) :=
  S6_4091.opposite_basis_of_normalizer
    (normalizer_of_ownerLift owner)

/-- Conditional second class; the exact same explicit owner premise remains. -/
theorem s6_4297_representative_basis_of_ownerLift
    (owner : ParitySuccessorLift) :
    BasisFor S6_4297.table.semigroup basis :=
  S6_4297.representative_basis_of_normalizer
    (normalizer_of_ownerLift owner)

/-- Conditional opposite orientation of the second class. -/
theorem s6_4297_opposite_basis_of_ownerLift
    (owner : ParitySuccessorLift) :
    BasisFor S6_4297.table.semigroup.opposite (reversedBasis basis) :=
  S6_4297.opposite_basis_of_normalizer
    (normalizer_of_ownerLift owner)

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank039.ParitySuccessorBridge

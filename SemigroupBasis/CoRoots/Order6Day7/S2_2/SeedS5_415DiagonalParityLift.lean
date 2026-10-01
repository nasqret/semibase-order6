import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415NormalizedInverse

/-!
# Rank040: the exact diagonal reduction, with two genuine inverse witnesses

The broad ambient-class and first-letter-square suggestions in msg-0368
fail in the actual Brandt factor. The corrected cut below retains the
FULL intrinsic Brandt signature and zero parity. Its exact reduction uses
the two already-proved inverses separately, and NEVER assumes a common
inverse or unrestricted factor completeness in an intermediate step.

DiagonalParityLift itself remains OPEN. Its equivalence to the full lift
does not assert the comparison field. The bounded screens are not imports.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.DiagonalComparison

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_415
open BrandtParityBridge RepeatedCellRegularity ExposureReplay NormalizedInverse HeadRetargetBoundary

theorem zeroParitySquare (word : Word Nat) : ZeroParity (word ++ word) := by
  intro letter
  simp only [Word.toList_append, List.count_append]
  omega

theorem zeroParityAppend {left right : Word Nat} (first : ZeroParity left) (second : ZeroParity right) :
    ZeroParity (left ++ right) := by
  intro letter
  have leftZero := first letter
  have rightZero := second letter
  simp only [Word.toList_append, List.count_append]
  omega

/-- OPEN comparison at a full intrinsic diagonal signature. The right
word inherits BOTH zero parity and diagonality by the preceding module's
proved transport lemmas. No support or compatibility information is lost. -/
def DiagonalParityLift : Prop :=
  ∀ left right : Word Nat, Nonempty (RankInverse left) → Nonempty (RankInverse right) →
    SameFactorSignature left right → ZeroParity left → DiagonalBrandt left →
      Derives Rank040.basis left right

/-- Let r invert u and s invert v. Compare u r with v r, and r u with
s v. These are two actual diagonal comparisons, and their composition is
u = u r u = v r u = v s v = v. A common inverse is NEVER assumed. -/
theorem regularPairParityLift_of_diagonalParityLift (owner : DiagonalParityLift) :
    RegularPairParityLift := by
  intro left right leftRegular rightRegular same
  obtain ⟨leftWitness⟩ := leftRegular
  obtain ⟨rightWitness⟩ := rightRegular
  let leftReverse := reverseWitness leftWitness
  let rightReverse := reverseWitness rightWitness
  have inverseSame := sameFactorSignatureInverse leftWitness rightWitness same
  have firstSignature : SameFactorSignature (left ++ leftWitness.inverse) (right ++ leftWitness.inverse) :=
    sameFactorSignatureAppend same (signature_of_derives (Derives.refl leftWitness.inverse))
  have secondSignature : SameFactorSignature (leftWitness.inverse ++ left) (rightWitness.inverse ++ right) :=
    sameFactorSignatureAppend inverseSame same
  have firstComparison : Derives Rank040.basis
      (left ++ leftWitness.inverse) (right ++ leftWitness.inverse) :=
    owner _ _ ⟨leftWitness.append leftReverse⟩ ⟨rightWitness.append leftReverse⟩ firstSignature
      (zeroParityInverseProduct leftWitness) (diagonalBrandtInverseProduct leftWitness)
  have secondComparison : Derives Rank040.basis
      (leftWitness.inverse ++ left) (rightWitness.inverse ++ right) :=
    owner _ _ ⟨leftReverse.append leftWitness⟩ ⟨rightReverse.append rightWitness⟩ secondSignature
      (zeroParityReverseInverseProduct leftWitness) (diagonalBrandtReverseInverseProduct leftWitness)
  have middle : Derives Rank040.basis
      ((right ++ leftWitness.inverse) ++ left) ((right ++ rightWitness.inverse) ++ right) := by
    simpa only [Word.append_assoc] using Derives.prepend right secondComparison
  exact leftWitness.word_inverse_word.symm.trans
    ((Derives.appendRight firstComparison left).trans
      (middle.trans rightWitness.word_inverse_word))

theorem regularPairParityLift_iff_diagonalParityLift : RegularPairParityLift ↔ DiagonalParityLift :=
  ⟨fun owner left right first second same _ _ => owner left right first second same,
    regularPairParityLift_of_diagonalParityLift⟩

theorem brandtParityLift_iff_diagonalParityLift : BrandtParityLift ↔ DiagonalParityLift :=
  brandtParityLift_iff_regularPairParityLift.trans regularPairParityLift_iff_diagonalParityLift

theorem fixedHeadParityLift_iff_diagonalParityLift :
    RetargetCoverage.FixedHeadParityLift ↔ DiagonalParityLift :=
  fixedHeadParityLift_iff_regularPairParityLift.trans regularPairParityLift_iff_diagonalParityLift

/-- Actual two-sided common inverse evidence already forces equality in
the frozen-law quotient; it is not a free consequence of factor semantics. -/
theorem derives_of_commonInverse {left right inverse : Word Nat}
    (leftWitness : RankInverse left) (rightWitness : RankInverse right)
    (leftInverse : leftWitness.inverse = inverse) (rightInverse : rightWitness.inverse = inverse) :
    Derives Rank040.basis left right := by
  apply (termClass_eq_iff_derives Rank040.basis).mp
  have first := leftWitness.termInverse.symm
  have second := rightWitness.termInverse.symm
  rw [leftInverse] at first
  rw [rightInverse] at second
  exact Semigroup.IdempotentsCommute.inverse_unique
    (modelIdempotentsCommute (termSemigroup Rank040.basis) (termSemigroup_models Rank040.basis))
    first second

def counterWalk : Word Nat := Word.mk 0 [1, 0, 1]
def counterAmbient : Word Nat := Word.mk 0 [0, 1, 1]
def counterHeadSquare : Word Nat := Word.mk 0 [0]

def counterValuation : Nat → Fin 5 :=
  fun letter => if letter = 0 then 1 else if letter = 1 then 2 else 0

def counterWalkWitness : RankInverse counterWalk :=
  squareInverseWitness (Word.mk 0 [1])

def counterAmbientWitness : RankInverse counterAmbient :=
  (squareInverseWitness (Word.singleton 0)).append (squareInverseWitness (Word.singleton 1))

theorem counterWalkZeroParity : ZeroParity counterWalk :=
  zeroParitySquare (Word.mk 0 [1])

theorem counterAmbientZeroParity : ZeroParity counterAmbient :=
  zeroParityAppend (zeroParitySquare (Word.singleton 0)) (zeroParitySquare (Word.singleton 1))

theorem counterSameSupport :
    ∀ letter, letter ∈ counterWalk.toList ↔ letter ∈ counterAmbient.toList := by
  intro letter
  simp [counterWalk, counterAmbient, Word.toList, or_left_comm, or_comm]

private theorem ambientEdge00 : BrandtEndpointConnected counterAmbient
    (BrandtEndpoint.outgoing 0) (BrandtEndpoint.incoming 0) :=
  BrandtEndpointConnected.adjacency (by decide)

private theorem ambientEdge01 : BrandtEndpointConnected counterAmbient
    (BrandtEndpoint.outgoing 0) (BrandtEndpoint.incoming 1) :=
  BrandtEndpointConnected.adjacency (by decide)

private theorem ambientEdge11 : BrandtEndpointConnected counterAmbient
    (BrandtEndpoint.outgoing 1) (BrandtEndpoint.incoming 1) :=
  BrandtEndpointConnected.adjacency (by decide)

private theorem ambientReturn : BrandtEndpointConnected counterAmbient
    (BrandtEndpoint.outgoing 1) (BrandtEndpoint.incoming 0) :=
  ambientEdge11.trans (ambientEdge01.symm.trans ambientEdge00)

/-- The counterexample meets the actual ambient ClosedReturnWord type,
not merely a separately implemented Boolean graph screen. -/
theorem counterWalkClosedInAmbient : ClosedReturnWord counterAmbient counterWalk where
  support := fun letter member => (counterSameSupport letter).mp member
  initial := BrandtEndpointConnected.refl _
  internal := by
    intro source target member
    have possibilities : (source = 0 ∧ target = 1) ∨ (source = 1 ∧ target = 0) := by
      simpa [counterWalk, Word.adjacentPairs, Word.adjacentPairsFrom, or_assoc, or_left_comm, or_comm]
        using member
    rcases possibilities with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ambientEdge01
    · exact ambientReturn
  returns := ambientReturn

theorem counterAmbientClosedInAmbient : ClosedReturnWord counterAmbient counterAmbient where
  support := fun _ member => member
  initial := BrandtEndpointConnected.refl _
  internal := fun _ _ member => BrandtEndpointConnected.adjacency member
  returns := ambientReturn

theorem counterWalkClosedInSelf : ClosedReturnWord counterWalk counterWalk where
  support := fun _ member => member
  initial := BrandtEndpointConnected.refl _
  internal := fun _ _ member => BrandtEndpointConnected.adjacency member
  returns := BrandtEndpointConnected.adjacency (by decide)

theorem diagonalCountervaluation :
    rightTable.semigroup.eval counterValuation counterWalk = (3 : Fin 5) ∧
    rightTable.semigroup.eval counterValuation counterAmbient = (0 : Fin 5) ∧
    rightTable.semigroup.eval counterValuation counterHeadSquare = (0 : Fin 5) := by
  decide

theorem counterFullSignaturesDiffer : ¬ SameFactorSignature counterWalk counterAmbient := by
  intro same
  have equality := rightValid_of_sameBrandtSignature (Identity.mk counterWalk counterAmbient)
    same.brandt counterValuation
  change (3 : Fin 5) = 0 at equality
  exact (by decide : (3 : Fin 5) ≠ 0) equality

theorem counterAmbientNotDerivable : ¬ Derives Rank040.basis counterWalk counterAmbient := by
  intro derived
  exact counterFullSignaturesDiffer (signature_of_derives derived)

theorem counterHeadSquareNotDerivable : ¬ Derives Rank040.basis counterWalk counterHeadSquare := by
  intro derived
  have equality := derived.sound rightModels counterValuation
  change (3 : Fin 5) = 0 at equality
  exact (by decide : (3 : Fin 5) ≠ 0) equality

/-- Even adding equal SUPPORT does not repair ambient-class-only equality.
The full intrinsic compatibility signature is indispensable. -/
theorem ambientClassDiagonalLift_refuted :
    ¬ (∀ ambient left right : Word Nat,
      ClosedReturnWord ambient left → ClosedReturnWord ambient right →
      Nonempty (RankInverse left) → Nonempty (RankInverse right) →
      ZeroParity left → ZeroParity right →
      (∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList) →
      Derives Rank040.basis left right) := by
  intro owner
  exact counterAmbientNotDerivable
    (owner counterAmbient counterWalk counterAmbient
      counterWalkClosedInAmbient counterAmbientClosedInAmbient
      ⟨counterWalkWitness⟩ ⟨counterAmbientWitness⟩
      counterWalkZeroParity counterAmbientZeroParity counterSameSupport)

/-- The suggested first-LETTER square is not a canonical diagonal word:
the first letter of a return word need not itself be a return loop. -/
theorem firstLetterSquareDiagonal_refuted :
    ¬ (∀ word : Word Nat, ClosedReturnWord word word →
      Nonempty (RankInverse word) → ZeroParity word →
      Derives Rank040.basis word ((Word.singleton word.head) ++ Word.singleton word.head)) := by
  intro owner
  exact counterHeadSquareNotDerivable
    (owner counterWalk counterWalkClosedInSelf ⟨counterWalkWitness⟩ counterWalkZeroParity)

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.DiagonalComparison

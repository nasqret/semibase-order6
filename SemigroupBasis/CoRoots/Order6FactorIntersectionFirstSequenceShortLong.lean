import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.CoRoots.S5_523Normalization
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_16
import SemigroupBasis.Generated.S4_2
import SemigroupBasis.Generated.S4_3
import SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorIntersectionFirstSequenceShortLong

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def xyy : Word Nat := w 0 [1, 1]
def xyz : Word Nat := w 0 [1, 2]
def xxyz : Word Nat := w 0 [0, 1, 2]

def yxx : Word Nat := w 1 [0, 0]
def yyx : Word Nat := w 1 [1, 0]
def zyx : Word Nat := w 2 [1, 0]
def zyxx : Word Nat := w 2 [1, 0, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def gatherLaw : Identity Nat := ⟨xxy, xyx⟩
def transferLaw : Identity Nat := ⟨xxy, xyy⟩
def longContractionLaw : Identity Nat := ⟨xxyz, xyz⟩

/-- The direct first-sequence/short-long basis, in contract order. -/
def basis : List (Identity Nat) :=
  [powerLaw, gatherLaw, transferLaw, longContractionLaw]

/-- The exact opposite presentation recorded by the order-six packet. -/
def oppositeBasis : List (Identity Nat) :=
  [⟨xx, xxx⟩, ⟨yxx, xyx⟩, ⟨yxx, yyx⟩, ⟨zyxx, zyx⟩]

theorem reversedBasis_eq_oppositeBasis :
    reversedBasis basis = oppositeBasis := by
  rfl

def candidateBasisUpToOppositeSHA256 : String :=
  "98ec26c0f28e6fde03469e70cd42bc7401e94e49c05da39ab3b9ecc2add2ff48"

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem s3_16_models :
    Models SemigroupBasis.Generated.S3_16.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_16.table basis toFinThree (by decide)

theorem s4_2_models :
    Models SemigroupBasis.Generated.S4_2.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_2.table basis toFinThree (by decide)

theorem s4_3_models :
    Models SemigroupBasis.Generated.S4_3.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_3.table basis toFinThree (by decide)

private theorem directPowerDerives : Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

private theorem s5_523AxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_523.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_523.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · have extended :=
      Derives.appendRight directPowerDerives (Word.singleton 0)
    simpa [SemigroupBasis.CoRoots.S5_523.powerLaw,
      SemigroupBasis.CoRoots.S5_523.xxx,
      SemigroupBasis.CoRoots.S5_523.xxxx, powerLaw, xx, xxx, w,
      Word.append, Word.singleton] using extended
  · simpa [SemigroupBasis.CoRoots.S5_523.gatherLaw,
      SemigroupBasis.CoRoots.S5_523.xxy,
      SemigroupBasis.CoRoots.S5_523.xyx, gatherLaw, xxy, xyx, w] using
      (Derives.fromBasis (basis := basis) (e := gatherLaw) (by
        simp [basis]))
  · simpa [SemigroupBasis.CoRoots.S5_523.transferLaw,
      SemigroupBasis.CoRoots.S5_523.xxy,
      SemigroupBasis.CoRoots.S5_523.xyy, transferLaw, xxy, xyy, w] using
      (Derives.fromBasis (basis := basis) (e := transferLaw) (by
        simp [basis]))
  · have extended :=
      Derives.appendRight directPowerDerives (Word.singleton 1)
    simpa [SemigroupBasis.CoRoots.S5_523.prefixCapLaw,
      SemigroupBasis.CoRoots.S5_523.xxy,
      SemigroupBasis.CoRoots.S5_523.xxxy, powerLaw, xx, xxx, xxy, w,
      Word.append, Word.singleton] using extended
  · simpa [SemigroupBasis.CoRoots.S5_523.longInsertionLaw,
      SemigroupBasis.CoRoots.S5_523.xyz,
      SemigroupBasis.CoRoots.S5_523.xxyz, longContractionLaw,
      xyz, xxyz, w] using
      (Derives.fromBasis (basis := basis) (e := longContractionLaw) (by
        simp [basis])).symm

private def instantiateOneWord (u : Word Nat) : Nat → Word Nat
  | 0 => u
  | n + 1 => Word.singleton (n + 1)

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst directPowerDerives (instantiateOneWord u)
  simpa [powerLaw, xx, xxx, w, instantiateOneWord,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem satisfiedBy_of_table_eq
    {source target : FiniteTable} (tableEq : source = target)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy source.semigroup) :
    identity.SatisfiedBy target.semigroup := by
  cases tableEq
  exact valid

private theorem s3_16_firstOccurrences
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_16.table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
    identity <|
      satisfiedBy_of_table_eq
        SemigroupBasis.Generated.S3_16.table_eq_catalogue_model
        identity valid

private theorem derives_firstOccurrences_eq
    {left right : Word Nat} (derivation : Derives basis left right) :
    firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList :=
  s3_16_firstOccurrences ⟨left, right⟩
    (derivation.sound s3_16_models)

private theorem longNormalList_eq_of_firstOccurrences
    (left right : List Nat)
    (leftLong : 3 ≤ left.length)
    (rightLong : 3 ≤ right.length)
    (firstOccurrences :
      firstOccurrenceSequence left = firstOccurrenceSequence right) :
    SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList left =
      SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList right := by
  cases left with
  | nil => simp at leftLong
  | cons leftHead leftTail =>
      cases leftTail with
      | nil => simp at leftLong
      | cons leftSecond leftRest =>
          cases leftRest with
          | nil => simp at leftLong
          | cons leftThird leftMore =>
              cases right with
              | nil => simp at rightLong
              | cons rightHead rightTail =>
                  cases rightTail with
                  | nil => simp at rightLong
                  | cons rightSecond rightRest =>
                      cases rightRest with
                      | nil => simp at rightLong
                      | cons rightThird rightMore =>
                          simp only [
                            SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList]
                          rw [firstOccurrences]

private theorem derivesLongOfFirstOccurrences
    (left right : Word Nat)
    (leftLong : 3 ≤ left.toList.length)
    (rightLong : 3 ≤ right.toList.length)
    (firstOccurrences :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    Derives basis left right := by
  have old : Derives SemigroupBasis.CoRoots.S5_523.basis left right :=
    SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceDerivationalCompleteness
      left right <| by
        exact longNormalList_eq_of_firstOccurrences
          left.toList right.toList leftLong rightLong firstOccurrences
  exact old.transport s5_523AxiomDerives

private abbrev IsBulk :=
  SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap.IsBulk

private theorem bulk_has_long_representative
    (word : Word Nat) (bulk : IsBulk word) :
    ∃ longWord,
      Derives basis word longWord ∧ 3 ≤ longWord.toList.length := by
  rcases bulk with ⟨letter, rfl⟩ | long
  · refine ⟨w letter [letter, letter], ?_, ?_⟩
    · simpa [
        SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap.wordOfCons,
        w, Word.singleton, Word.append, Word.append_assoc] using
        derivesPowerExpansion (Word.singleton letter)
    · simp [w, Word.toList]
  · exact ⟨word, Derives.refl _, long⟩

private theorem derivesBulkPair
    (identity : Identity Nat)
    (sequenceValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_16.table.semigroup)
    (bulk : IsBulk identity.lhs ∧ IsBulk identity.rhs) :
    Derives basis identity.lhs identity.rhs := by
  obtain ⟨leftNormal, leftDerivation, leftLong⟩ :=
    bulk_has_long_representative identity.lhs bulk.1
  obtain ⟨rightNormal, rightDerivation, rightLong⟩ :=
    bulk_has_long_representative identity.rhs bulk.2
  have normalFirstOccurrences :
      firstOccurrenceSequence leftNormal.toList =
        firstOccurrenceSequence rightNormal.toList :=
    (derives_firstOccurrences_eq leftDerivation).symm.trans <|
      (s3_16_firstOccurrences identity sequenceValid).trans
        (derives_firstOccurrences_eq rightDerivation)
  exact leftDerivation.trans <|
    (derivesLongOfFirstOccurrences leftNormal rightNormal
      leftLong rightLong normalFirstOccurrences).trans
        (Derives.symm rightDerivation)

theorem derives_of_s3_16_s4_2_valid
    (identity : Identity Nat)
    (sequenceValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_16.table.semigroup)
    (shortValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_2.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  rcases
      SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap.shortClass_of_valid
        identity shortValid with equal | bulk
  · rw [equal]
    exact Derives.refl _
  · exact derivesBulkPair identity sequenceValid bulk

private theorem commutativeShape_common_iff_bulk (word : Word Nat) :
    commutativeCommonSquareShape word =
        CommutativeCommonSquareShape.common ↔
      IsBulk word := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [commutativeCommonSquareShape,
            SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap.IsBulk,
            SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap.wordOfCons,
            Word.toList]
      | cons next rest =>
          cases rest with
          | nil =>
              by_cases diagonal : head = next
              · subst next
                simp [commutativeCommonSquareShape,
                  SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap.IsBulk,
                  SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap.wordOfCons,
                  Word.toList]
              · simp [commutativeCommonSquareShape, diagonal, Ne.symm diagonal,
                  SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap.IsBulk,
                  SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap.wordOfCons,
                  Word.toList]
          | cons third more =>
              simp [commutativeCommonSquareShape,
                SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap.IsBulk,
                Word.toList]

private theorem firstOccurrences_eq_self_of_not_bulk
    (word : Word Nat) (notBulk : ¬ IsBulk word) :
    firstOccurrenceSequence word.toList = word.toList := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList, firstOccurrenceSequence]
      | cons next rest =>
          cases rest with
          | nil =>
              have different : next ≠ head := by
                intro equal
                apply notBulk
                left
                subst next
                exact ⟨head, rfl⟩
              simp [Word.toList, firstOccurrenceSequence,
                different, Ne.symm different]
          | cons third more =>
              exact False.elim <| notBulk <| Or.inr <| by
                simp [Word.toList]

private theorem eq_of_not_bulk_and_firstOccurrences
    (left right : Word Nat)
    (leftNotBulk : ¬ IsBulk left)
    (rightNotBulk : ¬ IsBulk right)
    (firstOccurrences :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    left = right := by
  apply Word.toList_injective
  rw [← firstOccurrences_eq_self_of_not_bulk left leftNotBulk,
    firstOccurrences,
    firstOccurrences_eq_self_of_not_bulk right rightNotBulk]

theorem derives_of_s3_16_s4_3_valid
    (identity : Identity Nat)
    (sequenceValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_16.table.semigroup)
    (shortValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_3.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have shortValid' : identity.SatisfiedBy
      commutativeCommonSquareThreeNilpotentFour.semigroup :=
    satisfiedBy_of_table_eq
      SemigroupBasis.Generated.S4_3.table_eq_catalogue_model
      identity shortValid
  have shapeEq :=
    commutativeCommonSquareShape_eq_of_valid identity shortValid'
  have firstOccurrences := s3_16_firstOccurrences identity sequenceValid
  by_cases leftCommon :
      commutativeCommonSquareShape identity.lhs =
        CommutativeCommonSquareShape.common
  · have rightCommon :
        commutativeCommonSquareShape identity.rhs =
          CommutativeCommonSquareShape.common := by
      rw [← shapeEq]
      exact leftCommon
    exact derivesBulkPair identity sequenceValid
      ⟨(commutativeShape_common_iff_bulk identity.lhs).mp leftCommon,
        (commutativeShape_common_iff_bulk identity.rhs).mp rightCommon⟩
  · have rightNotCommon :
        commutativeCommonSquareShape identity.rhs ≠
          CommutativeCommonSquareShape.common := by
      intro rightCommon
      apply leftCommon
      rw [shapeEq]
      exact rightCommon
    have leftNotBulk : ¬ IsBulk identity.lhs := by
      intro bulk
      exact leftCommon <|
        (commutativeShape_common_iff_bulk identity.lhs).mpr bulk
    have rightNotBulk : ¬ IsBulk identity.rhs := by
      intro bulk
      exact rightNotCommon <|
        (commutativeShape_common_iff_bulk identity.rhs).mpr bulk
    have equal :=
      eq_of_not_bulk_and_firstOccurrences identity.lhs identity.rhs
        leftNotBulk rightNotBulk firstOccurrences
    rw [equal]
    exact Derives.refl _

def s3_16_s4_2_intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.S4_2.table.semigroup basis where
  leftModels := s3_16_models
  rightModels := s4_2_models
  complete := derives_of_s3_16_s4_2_valid

def s3_16_s4_3_intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.S4_3.table.semigroup basis where
  leftModels := s3_16_models
  rightModels := s4_3_models
  complete := derives_of_s3_16_s4_3_valid

end SemigroupBasis.CoRoots.Order6FactorIntersectionFirstSequenceShortLong

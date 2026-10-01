import SemigroupBasis.CoRoots.S5_196
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.Generated.S4_2
import SemigroupBasis.Generated.S4_3
import SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def xyy : Word Nat := w 0 [1, 1]
def yxx : Word Nat := w 1 [0, 0]
def yyx : Word Nat := w 1 [1, 0]
def xyz : Word Nat := w 0 [1, 2]
def xxyz : Word Nat := w 0 [0, 1, 2]
def yxz : Word Nat := w 1 [0, 2]
def zxy : Word Nat := w 2 [0, 1]
def zyx : Word Nat := w 2 [1, 0]
def zyxx : Word Nat := w 2 [1, 0, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def copyLaw : Identity Nat := ⟨xyx, xyy⟩
def rotateLaw : Identity Nat := ⟨xyx, yxx⟩
def longInsertionLaw : Identity Nat := ⟨xyz, xxyz⟩
def prefixCommutationLaw : Identity Nat := ⟨xyz, yxz⟩

/-- The direct intersection basis, in the contract order. -/
def basis : List (Identity Nat) :=
  [powerLaw, copyLaw, rotateLaw, longInsertionLaw,
    prefixCommutationLaw]

/-- The recorded opposite-oriented candidate, including its exact law order
and side orientations. -/
def recordedOppositeBasis : List (Identity Nat) :=
  [⟨xx, xxx⟩, ⟨xxy, xyx⟩, ⟨xyx, yyx⟩,
    ⟨zxy, zyx⟩, ⟨zyx, zyxx⟩]

def candidateBasisUpToOppositeSHA256 : String :=
  "56d95b7dba50a8ecc791533711bc0da6587d0867037856cf9ecbbf206b6bd694"

def expectedReversedBasis : List (Identity Nat) :=
  [⟨xx, xxx⟩, ⟨xyx, yyx⟩, ⟨xyx, xxy⟩,
    ⟨zyx, zyxx⟩, ⟨zyx, zxy⟩]

theorem reversedBasis_eq_expected :
    reversedBasis basis = expectedReversedBasis := by
  rfl

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem s3_6_models :
    Models SemigroupBasis.Generated.S3_6.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_6.table basis toFinThree (by decide)

theorem s4_2_models :
    Models SemigroupBasis.Generated.S4_2.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_2.table basis toFinThree (by decide)

theorem s4_3_models :
    Models SemigroupBasis.Generated.S4_3.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_3.table basis toFinThree (by decide)

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have base : Derives basis xx xxx :=
    Derives.fromBasis (e := powerLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesCopy (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((u ++ v) ++ v) := by
  have base : Derives basis xyx xyy :=
    Derives.fromBasis (e := copyLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [copyLaw, xyx, xyy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesRotate (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((v ++ u) ++ u) := by
  have base : Derives basis xyx yxx :=
    Derives.fromBasis (e := rotateLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [rotateLaw, xyx, yxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesLongInsertion (u v z : Word Nat) :
    Derives basis ((u ++ v) ++ z) (((u ++ u) ++ v) ++ z) := by
  have base : Derives basis xyz xxyz :=
    Derives.fromBasis (e := longInsertionLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [longInsertionLaw, xyz, xxyz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesPrefixSwap (u v suffix : Word Nat) :
    Derives basis ((u ++ v) ++ suffix) ((v ++ u) ++ suffix) := by
  have base : Derives basis xyz yxz :=
    Derives.fromBasis (e := prefixCommutationLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v suffix)
  simpa [prefixCommutationLaw, xyz, yxz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem s5_196AxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_196.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_196.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have expanded :=
      Derives.appendRight
        (derivesPowerExpansion (Word.singleton 0))
        (Word.singleton 0)
    change Derives basis (w 0 [0, 0]) (w 0 [0, 0, 0])
    simpa [w, Word.singleton, Word.append, Word.append_assoc] using
      expanded
  · change Derives basis (w 0 [0, 1]) (w 0 [0, 0, 1])
    simpa [w, Word.singleton, Word.append, Word.append_assoc] using
      derivesLongInsertion
        (Word.singleton 0) (Word.singleton 0) (Word.singleton 1)
  · change Derives basis (w 0 [1, 0]) (w 0 [1, 1])
    simpa [w, Word.singleton, Word.append, Word.append_assoc] using
      derivesCopy (Word.singleton 0) (Word.singleton 1)
  · change Derives basis (w 0 [1, 0]) (w 1 [0, 0])
    simpa [w, Word.singleton, Word.append, Word.append_assoc] using
      derivesRotate (Word.singleton 0) (Word.singleton 1)
  · change Derives basis (w 0 [1, 0]) (w 0 [0, 1, 0])
    simpa [w, Word.singleton, Word.append, Word.append_assoc] using
      derivesLongInsertion
        (Word.singleton 0) (Word.singleton 1) (Word.singleton 0)
  · change Derives basis (w 0 [1, 2]) (w 1 [0, 2])
    simpa [w, Word.singleton, Word.append, Word.append_assoc] using
      derivesPrefixSwap
        (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)
  · change Derives basis (w 0 [1, 2]) (w 0 [0, 1, 2])
    simpa [w, Word.singleton, Word.append, Word.append_assoc] using
      derivesLongInsertion
        (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)

theorem derivesLongOfSignature
    (left right : Word Nat)
    (leftLong : 3 ≤ left.toList.length)
    (rightLong : 3 ≤ right.toList.length)
    (support : SemigroupBasis.CoRoots.S5_196.SameSupport left right)
    (simple : SemigroupBasis.CoRoots.S5_196.SameSimpleFinal left right) :
    Derives basis left right :=
  (SemigroupBasis.CoRoots.S5_196.derivesLongOfSignature
    left right leftLong rightLong support simple).transport
      s5_196AxiomDerives

private theorem literalAxiomDerivesRecorded
    (identity : Identity Nat)
    (member : identity ∈ reversedBasis basis) :
    Derives recordedOppositeBasis identity.lhs identity.rhs := by
  rw [reversedBasis_eq_expected] at member
  simp only [expectedReversedBasis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact Derives.fromBasis (e := ⟨xx, xxx⟩)
      (by simp [recordedOppositeBasis])
  · exact Derives.fromBasis (e := ⟨xyx, yyx⟩)
      (by simp [recordedOppositeBasis])
  · exact (Derives.fromBasis (e := ⟨xxy, xyx⟩)
      (by simp [recordedOppositeBasis])).symm
  · exact Derives.fromBasis (e := ⟨zyx, zyxx⟩)
      (by simp [recordedOppositeBasis])
  · exact (Derives.fromBasis (e := ⟨zxy, zyx⟩)
      (by simp [recordedOppositeBasis])).symm

private theorem recordedAxiomDerivesLiteral
    (identity : Identity Nat)
    (member : identity ∈ recordedOppositeBasis) :
    Derives (reversedBasis basis) identity.lhs identity.rhs := by
  simp only [recordedOppositeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact Derives.fromBasis (e := ⟨xx, xxx⟩) (by
      rw [reversedBasis_eq_expected]
      simp [expectedReversedBasis])
  · exact (Derives.fromBasis (e := ⟨xyx, xxy⟩) (by
      rw [reversedBasis_eq_expected]
      simp [expectedReversedBasis])).symm
  · exact Derives.fromBasis (e := ⟨xyx, yyx⟩) (by
      rw [reversedBasis_eq_expected]
      simp [expectedReversedBasis])
  · exact (Derives.fromBasis (e := ⟨zyx, zxy⟩) (by
      rw [reversedBasis_eq_expected]
      simp [expectedReversedBasis])).symm
  · exact Derives.fromBasis (e := ⟨zyx, zyxx⟩) (by
      rw [reversedBasis_eq_expected]
      simp [expectedReversedBasis])

/-- Convert the literal reversed presentation to the exact recorded
opposite-oriented candidate. -/
theorem recordedOppositeBasisFor
    {S : Type} {G : Semigroup S}
    (direct : BasisFor G basis) :
    BasisFor G.opposite recordedOppositeBasis := by
  have literal : BasisFor G.opposite (reversedBasis basis) :=
    direct.oppositeReversed
  refine literal.replace ?_ literalAxiomDerivesRecorded
  intro identity member
  exact (recordedAxiomDerivesLiteral identity member).sound literal.1

private theorem satisfiedBy_of_table_eq
    {source target : FiniteTable} (tableEq : source = target)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy source.semigroup) :
    identity.SatisfiedBy target.semigroup := by
  cases tableEq
  exact valid

private theorem s3_6_support
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_6.table.semigroup) :
    SemigroupBasis.CoRoots.S5_196.SameSupport
      identity.lhs identity.rhs :=
  SemigroupBasis.CoRoots.S5_196.finalMarkerValid_support identity <|
    satisfiedBy_of_table_eq
      SemigroupBasis.Generated.S3_6.table_eq_catalogue_model
      identity valid

private theorem s3_6_simpleFinal
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_6.table.semigroup) :
    SemigroupBasis.CoRoots.S5_196.SameSimpleFinal
      identity.lhs identity.rhs :=
  SemigroupBasis.CoRoots.S5_196.finalMarkerValid_simpleFinal identity <|
    satisfiedBy_of_table_eq
      SemigroupBasis.Generated.S3_6.table_eq_catalogue_model
      identity valid

private theorem derivesViaLong
    (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_6.table.semigroup)
    (leftNormal rightNormal : Word Nat)
    (leftDerivation : Derives basis identity.lhs leftNormal)
    (rightDerivation : Derives basis identity.rhs rightNormal)
    (leftLong : 3 ≤ leftNormal.toList.length)
    (rightLong : 3 ≤ rightNormal.toList.length) :
    Derives basis identity.lhs identity.rhs := by
  let normalized : Identity Nat := ⟨leftNormal, rightNormal⟩
  have normalizedValid : normalized.SatisfiedBy
      SemigroupBasis.Generated.S3_6.table.semigroup := by
    intro valuation
    exact (leftDerivation.sound s3_6_models valuation).symm.trans <|
      (markerValid valuation).trans
        (rightDerivation.sound s3_6_models valuation)
  have middle :=
    derivesLongOfSignature leftNormal rightNormal leftLong rightLong
      (s3_6_support normalized normalizedValid)
      (s3_6_simpleFinal normalized normalizedValid)
  exact leftDerivation.trans <|
    middle.trans (Derives.symm rightDerivation)

private theorem bulk_has_long_representative
    (word : Word Nat)
    (bulk :
      SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap.IsBulk
        word) :
    ∃ longWord,
      Derives basis word longWord ∧ 3 ≤ longWord.toList.length := by
  rcases bulk with ⟨letter, rfl⟩ | long
  · refine ⟨w letter [letter, letter], ?_, ?_⟩
    · simpa [SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap.wordOfCons,
        w, Word.singleton, Word.append, Word.append_assoc] using
        derivesPowerExpansion (Word.singleton letter)
    · simp [w, Word.toList]
  · exact ⟨word, Derives.refl _, long⟩

theorem derives_of_s3_6_s4_2_valid
    (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_6.table.semigroup)
    (shortValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_2.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  rcases
      SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap.shortClass_of_valid
        identity shortValid with equal | bulk
  · rw [equal]
    exact Derives.refl _
  · obtain ⟨leftNormal, leftDerivation, leftLong⟩ :=
      bulk_has_long_representative identity.lhs bulk.1
    obtain ⟨rightNormal, rightDerivation, rightLong⟩ :=
      bulk_has_long_representative identity.rhs bulk.2
    exact derivesViaLong identity markerValid
      leftNormal rightNormal leftDerivation rightDerivation
      leftLong rightLong

/-- Expand a diagonal quadratic word to length three. Other words are
unchanged, so precisely the common `S4_3` class becomes long. -/
private def commonize : Word Nat → Word Nat
  | ⟨head, next :: []⟩ =>
      if head = next then w head [head, head] else w head [next]
  | word => word

private theorem derivesCommonize (word : Word Nat) :
    Derives basis word (commonize word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => exact Derives.refl _
      | cons next rest =>
          cases rest with
          | nil =>
              by_cases diagonal : head = next
              · subst next
                simpa [commonize, w, Word.singleton, Word.append,
                  Word.append_assoc] using
                    derivesPowerExpansion (Word.singleton head)
              · simpa [commonize, diagonal, w] using
                  (Derives.refl (w head [next]) :
                    Derives basis (w head [next]) (w head [next]))
          | cons third more => exact Derives.refl _

private theorem commonize_long_of_shape_common
    (word : Word Nat)
    (common : commutativeCommonSquareShape word =
      CommutativeCommonSquareShape.common) :
    3 ≤ (commonize word).toList.length := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [commutativeCommonSquareShape] at common
      | cons next rest =>
          cases rest with
          | nil =>
              by_cases diagonal : head = next
              · subst next
                simp [commonize, w, Word.toList]
              · simp [commutativeCommonSquareShape, diagonal] at common
          | cons third more =>
              simp [commonize, Word.toList]

private theorem length_lt_three_of_shape_ne_common
    (word : Word Nat)
    (notCommon : commutativeCommonSquareShape word ≠
      CommutativeCommonSquareShape.common) :
    word.toList.length < 3 := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList]
      | cons next rest =>
          cases rest with
          | nil => simp [Word.toList]
          | cons third more =>
              simp [commutativeCommonSquareShape] at notCommon

private theorem short_length_eq_of_shape_eq
    (left right : Word Nat)
    (shapeEq : commutativeCommonSquareShape left =
      commutativeCommonSquareShape right)
    (leftNotCommon : commutativeCommonSquareShape left ≠
      CommutativeCommonSquareShape.common) :
    left.toList.length = right.toList.length := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          cases leftTail with
          | nil =>
              cases rightTail with
              | nil => rfl
              | cons rightNext rightRest =>
                  cases rightRest with
                  | nil =>
                      by_cases diagonal : rightHead = rightNext
                      · simp [commutativeCommonSquareShape, diagonal]
                          at shapeEq
                      · simp [commutativeCommonSquareShape, diagonal]
                          at shapeEq
                  | cons rightThird rightMore =>
                      simp [commutativeCommonSquareShape] at shapeEq
          | cons leftNext leftRest =>
              cases leftRest with
              | nil =>
                  cases rightTail with
                  | nil =>
                      by_cases diagonal : leftHead = leftNext
                      · simp [commutativeCommonSquareShape, diagonal]
                          at leftNotCommon
                      · simp [commutativeCommonSquareShape, diagonal]
                          at shapeEq
                  | cons rightNext rightRest =>
                      cases rightRest with
                      | nil => rfl
                      | cons rightThird rightMore =>
                          by_cases diagonal : leftHead = leftNext
                          · simp [commutativeCommonSquareShape, diagonal]
                              at leftNotCommon
                          · simp [commutativeCommonSquareShape, diagonal]
                              at shapeEq
              | cons leftThird leftMore =>
                  simp [commutativeCommonSquareShape] at leftNotCommon

private theorem wordLengthPositive (word : Word Nat) :
    1 ≤ word.toList.length := by
  cases word
  simp [Word.toList]

theorem derives_of_s3_6_s4_3_valid
    (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_6.table.semigroup)
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
  by_cases leftCommon :
      commutativeCommonSquareShape identity.lhs =
        CommutativeCommonSquareShape.common
  · have rightCommon :
        commutativeCommonSquareShape identity.rhs =
          CommutativeCommonSquareShape.common := by
      rw [← shapeEq]
      exact leftCommon
    exact derivesViaLong identity markerValid
      (commonize identity.lhs) (commonize identity.rhs)
      (derivesCommonize identity.lhs) (derivesCommonize identity.rhs)
      (commonize_long_of_shape_common identity.lhs leftCommon)
      (commonize_long_of_shape_common identity.rhs rightCommon)
  · have rightNotCommon :
        commutativeCommonSquareShape identity.rhs ≠
          CommutativeCommonSquareShape.common := by
      intro rightCommon
      apply leftCommon
      rw [shapeEq]
      exact rightCommon
    have leftShort :=
      length_lt_three_of_shape_ne_common identity.lhs leftCommon
    have rightShort :=
      length_lt_three_of_shape_ne_common identity.rhs rightNotCommon
    have lengthEq :=
      short_length_eq_of_shape_eq
        identity.lhs identity.rhs shapeEq leftCommon
    have support := s3_6_support identity markerValid
    by_cases leftOne : identity.lhs.toList.length = 1
    · have rightOne : identity.rhs.toList.length = 1 := by
        omega
      have equal :=
        SemigroupBasis.CoRoots.S5_196.lengthOne_eq_of_support
          identity.lhs identity.rhs leftOne rightOne support
      rw [equal]
      exact Derives.refl _
    · have leftTwo : identity.lhs.toList.length = 2 := by
        have positive := wordLengthPositive identity.lhs
        omega
      have rightTwo : identity.rhs.toList.length = 2 := by
        have positive := wordLengthPositive identity.rhs
        omega
      have equal :=
        SemigroupBasis.CoRoots.S5_196.lengthTwo_eq_of_signature
          identity.lhs identity.rhs leftTwo rightTwo support
          (s3_6_simpleFinal identity markerValid)
      rw [equal]
      exact Derives.refl _

def s3_6_s4_2_intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.S4_2.table.semigroup basis where
  leftModels := s3_6_models
  rightModels := s4_2_models
  complete := derives_of_s3_6_s4_2_valid

def s3_6_s4_3_intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.S4_3.table.semigroup basis where
  leftModels := s3_6_models
  rightModels := s4_3_models
  complete := derives_of_s3_6_s4_3_valid

end SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong

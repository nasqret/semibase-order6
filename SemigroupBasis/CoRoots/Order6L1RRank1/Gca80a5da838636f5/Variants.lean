import SemigroupBasis.CoRoots.Order6L1RRank1.Gca80a5da838636f5.FrozenHeadStratifiedCompleteness
import SemigroupBasis.CoRoots.S5_1092Factors
import SemigroupBasis.CoRoots.S5_381Invariant
import SemigroupBasis.Generated.S3_6

/-!
# Frozen-head factor routes for L1R group `ca80a5da838636f5`

Three members use the selected `S4_116op x S4_73` factor pair.  The five
remaining members use four authenticated theory-equal pairs:

* `S6_12885`: `S3_6op x S5_1135`;
* `S6_13664` and `S6_13698`: `S3_6op x S5_1092`;
* `S6_14252`: `S3_6op x S5_1092op`;
* `S6_14253`: `S3_6op x S5_1135op`.

The order-five coordinate supplies both occurrence orders.  The opposite
final-marker coordinate supplies the repeated-head stratum.  These three
coordinates determine the public `frozenHeadEndpoint`, so the alternate
routes reuse the fresh leaf's public contextual frozen-path normalization
without importing the retired compiler, semantic, normalization, canonical,
or old completeness layers.

Static source draft only: it is conditional on the imported frozen-head route
becoming kernel-green on Helios and is not itself kernel evidence.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gca80a5da838636f5

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots
open SemigroupBasis.CoRoots.Order6L1RRank1

/-! ## Exact alternate factor tables -/

abbrev s3_6 : FiniteTable :=
  SemigroupBasis.Generated.S3_6.table

abbrev s5_1092 : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_1092.table

abbrev s5_1135 : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_1135.table

/-- Exact opposite orientation used by all five alternate witnesses. -/
def s3_6op : FiniteTable :=
  FactorTables.oppositeTable s3_6

/-- Exact opposite orientation used by `S6_14252`. -/
def s5_1092op : FiniteTable :=
  FactorTables.oppositeTable s5_1092

/-- Exact opposite orientation used by `S6_14253`. -/
def s5_1135op : FiniteTable :=
  FactorTables.oppositeTable s5_1135

theorem s3_6op_semigroup :
    s3_6op.semigroup = s3_6.semigroup.opposite :=
  FactorTables.oppositeTable_semigroup s3_6

theorem s5_1092op_semigroup :
    s5_1092op.semigroup = s5_1092.semigroup.opposite :=
  FactorTables.oppositeTable_semigroup s5_1092

theorem s5_1135op_semigroup :
    s5_1135op.semigroup = s5_1135.semigroup.opposite :=
  FactorTables.oppositeTable_semigroup s5_1135

/-! ## Mechanical soundness of the displayed eight-law basis -/

theorem basis_s3_6op_models :
    Models s3_6op.semigroup basis :=
  FiniteCertificate.checkModels_sound
    s3_6op basis toFinThree (by decide)

theorem basis_s5_1092_models :
    Models s5_1092.semigroup basis :=
  FiniteCertificate.checkModels_sound
    s5_1092 basis toFinThree (by decide)

theorem basis_s5_1135_models :
    Models s5_1135.semigroup basis :=
  FiniteCertificate.checkModels_sound
    s5_1135 basis toFinThree (by decide)

theorem basis_s5_1092op_models :
    Models s5_1092op.semigroup basis :=
  FiniteCertificate.checkModels_sound
    s5_1092op basis toFinThree (by decide)

theorem basis_s5_1135op_models :
    Models s5_1135op.semigroup basis :=
  FiniteCertificate.checkModels_sound
    s5_1135op basis toFinThree (by decide)

/-! ## Opposite final-marker coordinate -/

private theorem simpleInitial_head_iff_not_mem_tail
    (word : Word Nat) :
    S5_107.SimpleInitial word word.head ↔
      word.head ∉ word.tail := by
  cases word with
  | mk head tail =>
      simp [S5_107.SimpleInitial, S5_107.SimpleIn, Word.toList,
        List.count_eq_zero]

/-- Validity in the exact `S3_6op` table preserves globally simple initial
variables. -/
private theorem s3_6opValid_simpleInitial_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s3_6op.semigroup)
    (letter : Nat) :
    S5_107.SimpleInitial identity.lhs letter ↔
      S5_107.SimpleInitial identity.rhs letter := by
  have markerValid :
      identity.SatisfiedBy
        SemigroupBasis.Examples.finalMarkerThree.semigroup.opposite := by
    simpa only [s3_6op_semigroup,
      SemigroupBasis.Generated.S3_6.table_eq_catalogue_model] using valid
  exact
    S5_381Invariant.oppositeFinalMarkerValid_simpleInitial_iff
      identity markerValid letter

/-- Once the occurrence coordinate identifies the two heads, simple-initial
preservation is exactly preservation of the repeated-head stratum. -/
private theorem s3_6opValid_initialRepeated_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s3_6op.semigroup)
    (heads : identity.lhs.head = identity.rhs.head) :
    (identity.lhs.head ∈ identity.lhs.tail) ↔
      (identity.rhs.head ∈ identity.rhs.tail) := by
  have simpleInitial :=
    s3_6opValid_simpleInitial_iff
      identity valid identity.lhs.head
  have absent :
      (identity.lhs.head ∉ identity.lhs.tail) ↔
        (identity.rhs.head ∉ identity.rhs.tail) := by
    calc
      identity.lhs.head ∉ identity.lhs.tail ↔
          S5_107.SimpleInitial identity.lhs identity.lhs.head :=
        (simpleInitial_head_iff_not_mem_tail identity.lhs).symm
      _ ↔ S5_107.SimpleInitial identity.rhs identity.lhs.head :=
        simpleInitial
      _ ↔ S5_107.SimpleInitial identity.rhs identity.rhs.head := by
        rw [heads]
      _ ↔ identity.rhs.head ∉ identity.rhs.tail :=
        simpleInitial_head_iff_not_mem_tail identity.rhs
  constructor
  · intro leftRepeated
    by_cases rightRepeated : identity.rhs.head ∈ identity.rhs.tail
    · exact rightRepeated
    · exact False.elim ((absent.mpr rightRepeated) leftRepeated)
  · intro rightRepeated
    by_cases leftRepeated : identity.lhs.head ∈ identity.lhs.tail
    · exact leftRepeated
    · exact False.elim ((absent.mp leftRepeated) rightRepeated)

/-! ## Opposite order-five occurrence coordinates -/

private theorem s5_1092opValid_reversed
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s5_1092op.semigroup) :
    identity.reversed.SatisfiedBy s5_1092.semigroup := by
  have oppositeValid :
      identity.SatisfiedBy s5_1092.semigroup.opposite := by
    simpa only [s5_1092op_semigroup] using valid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed
      identity s5_1092.semigroup).mp oppositeValid

private theorem s5_1135opValid_reversed
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s5_1135op.semigroup) :
    identity.reversed.SatisfiedBy s5_1135.semigroup := by
  have oppositeValid :
      identity.SatisfiedBy s5_1135.semigroup.opposite := by
    simpa only [s5_1135op_semigroup] using valid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed
      identity s5_1135.semigroup).mp oppositeValid

private theorem s5_1092opValid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s5_1092op.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList := by
  have reversedLast :=
    SemigroupBasis.CoRoots.S5_1092Factors.S5_1092.valid_lastOccurrenceSequence_eq
      identity.reversed (s5_1092opValid_reversed identity valid)
  have reversedFirst :
      (firstOccurrenceSequence identity.lhs.toList).reverse =
        (firstOccurrenceSequence identity.rhs.toList).reverse := by
    simpa [Identity.reversed,
      S5_1092.lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence]
      using reversedLast
  have restored := congrArg List.reverse reversedFirst
  simpa using restored

private theorem s5_1092opValid_lastOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s5_1092op.semigroup) :
    S5_1092.lastOccurrenceSequence identity.lhs.toList =
      S5_1092.lastOccurrenceSequence identity.rhs.toList := by
  have reversedFirst :=
    SemigroupBasis.CoRoots.S5_1092Factors.S5_1092.valid_firstOccurrenceSequence_eq
      identity.reversed (s5_1092opValid_reversed identity valid)
  have reversedEquality := congrArg List.reverse reversedFirst
  simpa [Identity.reversed,
    S5_1092.lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence] using
      reversedEquality

private theorem s5_1135opValid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s5_1135op.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList := by
  have reversedLast :=
    SemigroupBasis.CoRoots.S5_1092Factors.S5_1135.valid_lastOccurrenceSequence_eq
      identity.reversed (s5_1135opValid_reversed identity valid)
  have reversedFirst :
      (firstOccurrenceSequence identity.lhs.toList).reverse =
        (firstOccurrenceSequence identity.rhs.toList).reverse := by
    simpa [Identity.reversed,
      S5_1092.lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence]
      using reversedLast
  have restored := congrArg List.reverse reversedFirst
  simpa using restored

private theorem s5_1135opValid_lastOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s5_1135op.semigroup) :
    S5_1092.lastOccurrenceSequence identity.lhs.toList =
      S5_1092.lastOccurrenceSequence identity.rhs.toList := by
  have reversedFirst :=
    SemigroupBasis.CoRoots.S5_1092Factors.S5_1135.valid_firstOccurrenceSequence_eq
      identity.reversed (s5_1135opValid_reversed identity valid)
  have reversedEquality := congrArg List.reverse reversedFirst
  simpa [Identity.reversed,
    S5_1092.lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence] using
      reversedEquality

/-! ## Fresh frozen-head compatibility -/

private theorem variant_head_eq_of_firstOccurrenceSequence_eq
    {left right : Word Nat}
    (same :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    left.head = right.head := by
  have heads := congrArg List.head? same
  simpa [Word.toList, firstOccurrenceSequence] using heads

private theorem variant_firstOccurrenceSequence_cons_of_not_mem
    (head : Nat) (tail : List Nat) (absent : head ∉ tail) :
    firstOccurrenceSequence (head :: tail) =
      head :: firstOccurrenceSequence tail := by
  rw [firstOccurrenceSequence]
  congr 1
  apply List.filter_eq_self.mpr
  intro selected member
  have selectedInTail : selected ∈ tail :=
    (mem_firstOccurrenceSequence_iff selected tail).mp member
  have different : selected ≠ head := by
    intro equal
    subst selected
    exact absent selectedInTail
  simp [different]

private theorem variant_lastOccurrenceSequence_cons_of_not_mem
    (head : Nat) (tail : List Nat) (absent : head ∉ tail) :
    S5_1092.lastOccurrenceSequence (head :: tail) =
      head :: S5_1092.lastOccurrenceSequence tail := by
  simp [S5_1092.lastOccurrenceSequence, absent]

/-- Source-local copy of the fresh leaf's private coordinate-extensionality
argument.  It mentions only the leaf's public endpoint definition. -/
private theorem variant_frozenHeadEndpoint_eq_of_coordinates
    {left right : Word Nat}
    (firstOccurrences :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (lastOccurrences :
      S5_1092.lastOccurrenceSequence left.toList =
        S5_1092.lastOccurrenceSequence right.toList)
    (initialRepeated :
      (left.head ∈ left.tail) ↔ (right.head ∈ right.tail)) :
    frozenHeadEndpoint left = frozenHeadEndpoint right := by
  have heads : left.head = right.head :=
    variant_head_eq_of_firstOccurrenceSequence_eq firstOccurrences
  by_cases leftRepeated : left.head ∈ left.tail
  · have rightRepeated : right.head ∈ right.tail :=
      initialRepeated.mp leftRepeated
    have normalizedTail :
        S5_1092.regularBandNormalList left.toList =
          S5_1092.regularBandNormalList right.toList := by
      unfold S5_1092.regularBandNormalList
      exact
        (congrArg
          (fun initial : List Nat =>
            initial ++ S5_1092.lastOccurrenceSequence left.toList)
          firstOccurrences).trans
          (congrArg
            (fun final : List Nat =>
              firstOccurrenceSequence right.toList ++ final)
            lastOccurrences)
    have endpointHeads :
        Word.mk left.head
            (S5_1092.regularBandNormalList left.toList) =
          Word.mk right.head
            (S5_1092.regularBandNormalList left.toList) :=
      congrArg
        (fun initial : Nat =>
          Word.mk initial (S5_1092.regularBandNormalList left.toList))
        heads
    have endpointTails :
        Word.mk right.head
            (S5_1092.regularBandNormalList left.toList) =
          Word.mk right.head
            (S5_1092.regularBandNormalList right.toList) :=
      congrArg (Word.mk right.head) normalizedTail
    simpa only [frozenHeadEndpoint, leftRepeated, rightRepeated,
      ite_true, ite_false] using endpointHeads.trans endpointTails
  · have rightSimple : right.head ∉ right.tail := by
      intro repeated
      exact leftRepeated (initialRepeated.mpr repeated)
    have leftFirst :=
      variant_firstOccurrenceSequence_cons_of_not_mem
        left.head left.tail leftRepeated
    have rightFirst :=
      variant_firstOccurrenceSequence_cons_of_not_mem
        right.head right.tail rightSimple
    have firstCons :
        left.head :: firstOccurrenceSequence left.tail =
          right.head :: firstOccurrenceSequence right.tail :=
      leftFirst.symm.trans <| firstOccurrences.trans rightFirst
    have tailFirst :
        firstOccurrenceSequence left.tail =
          firstOccurrenceSequence right.tail := by
      simpa using congrArg List.tail firstCons
    have leftLast :=
      variant_lastOccurrenceSequence_cons_of_not_mem
        left.head left.tail leftRepeated
    have rightLast :=
      variant_lastOccurrenceSequence_cons_of_not_mem
        right.head right.tail rightSimple
    have lastCons :
        left.head :: S5_1092.lastOccurrenceSequence left.tail =
          right.head :: S5_1092.lastOccurrenceSequence right.tail :=
      leftLast.symm.trans <| lastOccurrences.trans rightLast
    have tailLast :
        S5_1092.lastOccurrenceSequence left.tail =
          S5_1092.lastOccurrenceSequence right.tail := by
      simpa using congrArg List.tail lastCons
    have normalizedTail :
        S5_1092.regularBandNormalList left.tail =
          S5_1092.regularBandNormalList right.tail := by
      unfold S5_1092.regularBandNormalList
      exact
        (congrArg
          (fun initial : List Nat =>
            initial ++ S5_1092.lastOccurrenceSequence left.tail)
          tailFirst).trans
          (congrArg
            (fun final : List Nat =>
              firstOccurrenceSequence right.tail ++ final)
            tailLast)
    have endpointHeads :
        Word.mk left.head (S5_1092.regularBandNormalList left.tail) =
          Word.mk right.head (S5_1092.regularBandNormalList left.tail) :=
      congrArg
        (fun initial : Nat =>
          Word.mk initial (S5_1092.regularBandNormalList left.tail))
        heads
    have endpointTails :
        Word.mk right.head (S5_1092.regularBandNormalList left.tail) =
          Word.mk right.head (S5_1092.regularBandNormalList right.tail) :=
      congrArg (Word.mk right.head) normalizedTail
    simpa only [frozenHeadEndpoint, leftRepeated, rightSimple,
      ite_true, ite_false] using endpointHeads.trans endpointTails

private theorem derivesOf_s3_6op_and_occurrences
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy s3_6op.semigroup)
    (first :
      firstOccurrenceSequence identity.lhs.toList =
        firstOccurrenceSequence identity.rhs.toList)
    (last :
      S5_1092.lastOccurrenceSequence identity.lhs.toList =
        S5_1092.lastOccurrenceSequence identity.rhs.toList) :
    Derives basis identity.lhs identity.rhs := by
  have heads :=
    variant_head_eq_of_firstOccurrenceSequence_eq first
  have endpoints :
      frozenHeadEndpoint identity.lhs =
        frozenHeadEndpoint identity.rhs :=
    variant_frozenHeadEndpoint_eq_of_coordinates first last
      (s3_6opValid_initialRepeated_iff identity leftValid heads)
  have lhsRoute := contextualFrozenRTC_derives
    (contextualFrozenRTC_frozenHeadEndpoint identity.lhs)
  have rhsRoute := contextualFrozenRTC_derives
    (contextualFrozenRTC_frozenHeadEndpoint identity.rhs)
  rw [endpoints] at lhsRoute
  exact lhsRoute.trans rhsRoute.symm

/-! ## Exact selected and alternate intersections -/

/-- Explicit selected-pair name used by the per-class endpoint generator for
`S6_12774`, `S6_13136`, and `S6_13685`. -/
def intersectionBasisS4_116opS4_73 :
    IntersectionBasis
      FactorTables.s4_116op.semigroup
      FactorTables.s4_73.semigroup
      basis :=
  intersectionBasisFrozenHead

theorem derivesOfFactorValidS3_6opS5_1135
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy s3_6op.semigroup)
    (rightValid : identity.SatisfiedBy s5_1135.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOf_s3_6op_and_occurrences
    identity leftValid
    (SemigroupBasis.CoRoots.S5_1092Factors.S5_1135.valid_firstOccurrenceSequence_eq
      identity rightValid)
    (SemigroupBasis.CoRoots.S5_1092Factors.S5_1135.valid_lastOccurrenceSequence_eq
      identity rightValid)

def intersectionBasisS3_6opS5_1135 :
    IntersectionBasis
      s3_6op.semigroup
      s5_1135.semigroup
      basis where
  leftModels := basis_s3_6op_models
  rightModels := basis_s5_1135_models
  complete := derivesOfFactorValidS3_6opS5_1135

theorem derivesOfFactorValidS3_6opS5_1092
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy s3_6op.semigroup)
    (rightValid : identity.SatisfiedBy s5_1092.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOf_s3_6op_and_occurrences
    identity leftValid
    (SemigroupBasis.CoRoots.S5_1092Factors.S5_1092.valid_firstOccurrenceSequence_eq
      identity rightValid)
    (SemigroupBasis.CoRoots.S5_1092Factors.S5_1092.valid_lastOccurrenceSequence_eq
      identity rightValid)

def intersectionBasisS3_6opS5_1092 :
    IntersectionBasis
      s3_6op.semigroup
      s5_1092.semigroup
      basis where
  leftModels := basis_s3_6op_models
  rightModels := basis_s5_1092_models
  complete := derivesOfFactorValidS3_6opS5_1092

theorem derivesOfFactorValidS3_6opS5_1092op
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy s3_6op.semigroup)
    (rightValid : identity.SatisfiedBy s5_1092op.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOf_s3_6op_and_occurrences
    identity leftValid
    (s5_1092opValid_firstOccurrenceSequence_eq identity rightValid)
    (s5_1092opValid_lastOccurrenceSequence_eq identity rightValid)

def intersectionBasisS3_6opS5_1092op :
    IntersectionBasis
      s3_6op.semigroup
      s5_1092op.semigroup
      basis where
  leftModels := basis_s3_6op_models
  rightModels := basis_s5_1092op_models
  complete := derivesOfFactorValidS3_6opS5_1092op

theorem derivesOfFactorValidS3_6opS5_1135op
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy s3_6op.semigroup)
    (rightValid : identity.SatisfiedBy s5_1135op.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOf_s3_6op_and_occurrences
    identity leftValid
    (s5_1135opValid_firstOccurrenceSequence_eq identity rightValid)
    (s5_1135opValid_lastOccurrenceSequence_eq identity rightValid)

def intersectionBasisS3_6opS5_1135op :
    IntersectionBasis
      s3_6op.semigroup
      s5_1135op.semigroup
      basis where
  leftModels := basis_s3_6op_models
  rightModels := basis_s5_1135op_models
  complete := derivesOfFactorValidS3_6opS5_1135op

end SemigroupBasis.CoRoots.Order6L1RRank1.Gca80a5da838636f5

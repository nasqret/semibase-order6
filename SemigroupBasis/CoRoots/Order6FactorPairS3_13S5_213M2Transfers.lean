import SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_213M2Normal
import SemigroupBasis.Generated.S3_15
import SemigroupBasis.Order6Subdirect.Common

/-!
# Transfer layer for the five M2 wrappers (msg-0275 request)

EVIDENCE LABEL: source-staged, not compiled here.  Everything below is
composition of existing kernel-verified exports; the only new proof
content is the derivation-reversal plumbing in §3 (flagged).

WRAPPER MAP (codex supplies the five recorded split-subdirect maps):
  S6_5642  S3_13  x S5_213      — intersectionComplete directly
  S6_5648  S3_13  x S5_213^op   — via §3 opposite transfer
  S6_5675  S3_15  x S5_213      — via headEq_S3_15 seam
  S6_9442  S3_13  x S5_498      — via §2 theory transfer
  S6_9461  S3_15  x S5_498      — via §2 + headEq_S3_15
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_213M2

open SemigroupBasis
open SemigroupBasis.CoRoots

private def sigmaVariable (value : Nat) : Fin 3 :=
  if value = 0 then 0 else if value = 1 then 1 else 2

def HeadEqSeam (table : FiniteTable) : Prop :=
  ∀ id : Identity Nat,
    id.SatisfiedBy table.semigroup → id.lhs.head = id.rhs.head

theorem headEq_s3_13 : HeadEqSeam Generated.S3_13.table := by
  intro id valid
  rw [Generated.S3_13.table_eq_catalogue_model] at valid
  exact Examples.leftNormalBandValid_head_eq id valid

theorem headEq_s3_15 : HeadEqSeam Generated.S3_15.table := by
  intro id valid
  rw [Generated.S3_15.table_eq_catalogue_model] at valid
  exact Examples.leftNormalBandFifteenValid_head_eq id valid

theorem modelsS3_15_sigma :
    Models Generated.S3_15.table.semigroup sigma :=
  FiniteCertificate.checkModels_sound
    Generated.S3_15.table sigma sigmaVariable (by decide)

theorem modelsS5_498_sigma :
    Models Generated.Catalogue.S5_498.table.semigroup sigma :=
  FiniteCertificate.checkModels_sound
    Generated.Catalogue.S5_498.table sigma sigmaVariable (by decide)

theorem modelsS5_213_opposite_sigma :
    Models Generated.Catalogue.S5_213.table.semigroup.opposite sigma := by
  simpa only [SemigroupBasis.Order6Subdirect.oppositeTable_semigroup] using
    (FiniteCertificate.checkModels_sound
      (SemigroupBasis.Order6Subdirect.oppositeTable
        Generated.Catalogue.S5_213.table)
      sigma sigmaVariable (by decide))

/-! ## §1  S5_498 carries the SAME complete basis (zero new mathematics) -/

theorem modelsS5_498_m2 :
    Models Generated.Catalogue.S5_498.table.semigroup S5_213.basis :=
  FiniteCertificate.checkModels_sound
    Generated.Catalogue.S5_498.table S5_213.basis
    S5_213.toFinTwo (by decide)

/-- Edmunds' basis is complete for `S5_498` verbatim: signature
extraction for S5_498 + the S5_213 normalizer. -/
theorem s5_498_basis_complete :
    BasisFor Generated.Catalogue.S5_498.table.semigroup S5_213.basis := by
  refine ⟨modelsS5_498_m2, ?_⟩
  intro id valid
  exact S5_213Normalization.derives_of_sameSignature
    (S5_213Invariant.sameSignature_of_s5_498_valid id valid)

/-! ## §2  Theory transfer `S5_498 → S5_213` (composition only) -/

theorem modelsS5_213_m2 :
    Models Generated.Catalogue.S5_213.table.semigroup S5_213.basis :=
  FiniteCertificate.checkModels_sound
    Generated.Catalogue.S5_213.table S5_213.basis
    S5_213.toFinTwo (by decide)

/-- Validity transfers from `S5_498` to `S5_213`: extract the
signature, derive in M2, evaluate the derivation in `S5_213`. -/
theorem s5_213_valid_of_s5_498_valid
    (id : Identity Nat)
    (valid :
      id.SatisfiedBy Generated.Catalogue.S5_498.table.semigroup) :
    id.SatisfiedBy Generated.Catalogue.S5_213.table.semigroup := by
  have derivation :=
    S5_213Normalization.derives_of_sameSignature
      (S5_213Invariant.sameSignature_of_s5_498_valid id valid)
  intro phi
  exact derivation.sound modelsS5_213_m2 phi

/-- The `S6_9442`/`S6_9461` completeness route: reduce to the shared
normalizer through §2. -/
theorem intersectionComplete_s5_498
    (headEq :
      ∀ id : Identity Nat,
        id.SatisfiedBy Generated.S3_13.table.semigroup →
          id.lhs.head = id.rhs.head) :
    ∀ id : Identity Nat,
      id.SatisfiedBy Generated.S3_13.table.semigroup →
      id.SatisfiedBy Generated.Catalogue.S5_498.table.semigroup →
      Derives sigma id.lhs id.rhs := by
  intro id validA validB
  exact intersectionComplete headEq id validA
    (s5_213_valid_of_s5_498_valid id validB)

theorem intersectionComplete_s3_15_s5_213 :
    ∀ id : Identity Nat,
      id.SatisfiedBy Generated.S3_15.table.semigroup →
      id.SatisfiedBy Generated.Catalogue.S5_213.table.semigroup →
      Derives sigma id.lhs id.rhs := by
  intro id validA validB
  exact intersectionCompleteOfHeadEq id (headEq_s3_15 id validA) validB

theorem intersectionComplete_s3_15_s5_498 :
    ∀ id : Identity Nat,
      id.SatisfiedBy Generated.S3_15.table.semigroup →
      id.SatisfiedBy Generated.Catalogue.S5_498.table.semigroup →
      Derives sigma id.lhs id.rhs := by
  intro id validA validB
  exact intersectionCompleteOfHeadEq id (headEq_s3_15 id validA)
    (s5_213_valid_of_s5_498_valid id validB)

/-! ## §3  Opposite transfer for `S6_5648` (one flagged plumbing step)

`reversedBasis S5_213.basis` is the SAME three identities with the two
gather laws exchanged (`S5_213.reversedBasis_eq_expected`, kernel
`rfl`), so derivations over the reversed basis ARE derivations over the
basis after a membership permutation.  The only plumbing is the
standard derivation-reversal lemma; API RISK: its repository spelling
(`Derives.reversed` / the lemma underlying `BasisFor.oppositeReversed`)
— one name to align at compile. -/

private theorem reversedM2AxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ reversedBasis S5_213.basis) :
    Derives S5_213.basis identity.lhs identity.rhs := by
  rw [S5_213.reversedBasis_eq_expected] at member
  simp only [S5_213.expectedReversedBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact Derives.fromBasis (by simp [S5_213.basis])
  · exact Derives.fromBasis (by simp [S5_213.basis])
  · exact Derives.fromBasis (by simp [S5_213.basis])

/-- Validity in the opposite table transfers to the direct table. -/
theorem s5_213_valid_of_opposite_valid
    (id : Identity Nat)
    (valid :
      id.SatisfiedBy
        Generated.Catalogue.S5_213.table.semigroup.opposite) :
    id.SatisfiedBy Generated.Catalogue.S5_213.table.semigroup := by
  have reversedValid :
      id.reversed.SatisfiedBy
        Generated.Catalogue.S5_213.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed id
      Generated.Catalogue.S5_213.table.semigroup).mp valid
  have reversedDerivation :=
    S5_213Normalization.derives_of_sameSignature
      (S5_213Invariant.sameSignature_of_s5_213_valid
        id.reversed reversedValid)
  have directDerivation : Derives S5_213.basis id.lhs id.rhs := by
    have transported :=
      reversedDerivation.reverse.transport reversedM2AxiomDerives
    cases id
    simpa [Identity.reversed] using transported
  intro phi
  exact directDerivation.sound modelsS5_213_m2 phi

theorem intersectionComplete_opposite
    (headEq :
      ∀ id : Identity Nat,
        id.SatisfiedBy Generated.S3_13.table.semigroup →
          id.lhs.head = id.rhs.head) :
    ∀ id : Identity Nat,
      id.SatisfiedBy Generated.S3_13.table.semigroup →
      id.SatisfiedBy
        Generated.Catalogue.S5_213.table.semigroup.opposite →
      Derives sigma id.lhs id.rhs := by
  intro id validA validB
  exact intersectionComplete headEq id validA
    (s5_213_valid_of_opposite_valid id validB)

/-! ## §4  Concrete intersection bases

`S3_15` and `S3_13` share the left-normal-band theory (bounded receipt
msg-0085; kernel route through the shared LNB basis identification).
The wrappers for `S6_5675`/`S6_9461` consume exactly one fact, stated
here as the seam; `lnbDerives_head_eq` (in the normalizer module)
supplies the syntactic half for BOTH seams once codex wires the
respective table identifications. -/

def intersectionBasisS3_13S5_213 :
    IntersectionBasis Generated.S3_13.table.semigroup
      Generated.Catalogue.S5_213.table.semigroup sigma where
  leftModels := modelsS3_13
  rightModels := modelsS5_213
  complete := intersectionComplete headEq_s3_13

def intersectionBasisS3_13S5_213Opposite :
    IntersectionBasis Generated.S3_13.table.semigroup
      Generated.Catalogue.S5_213.table.semigroup.opposite sigma where
  leftModels := modelsS3_13
  rightModels := modelsS5_213_opposite_sigma
  complete := intersectionComplete_opposite headEq_s3_13

def intersectionBasisS3_15S5_213 :
    IntersectionBasis Generated.S3_15.table.semigroup
      Generated.Catalogue.S5_213.table.semigroup sigma where
  leftModels := modelsS3_15_sigma
  rightModels := modelsS5_213
  complete := intersectionComplete_s3_15_s5_213

def intersectionBasisS3_13S5_498 :
    IntersectionBasis Generated.S3_13.table.semigroup
      Generated.Catalogue.S5_498.table.semigroup sigma where
  leftModels := modelsS3_13
  rightModels := modelsS5_498_sigma
  complete := intersectionComplete_s5_498 headEq_s3_13

def intersectionBasisS3_15S5_498 :
    IntersectionBasis Generated.S3_15.table.semigroup
      Generated.Catalogue.S5_498.table.semigroup sigma where
  leftModels := modelsS3_15_sigma
  rightModels := modelsS5_498_sigma
  complete := intersectionComplete_s3_15_s5_498

/-! ## §5  Wrapper template (per root; codex instantiates)

For root `R` with recorded split-subdirect pair
`(π₁ : R ↠ A, π₂ : R ↠ B)` jointly injective (msg-0085 data):

  models  : `FiniteCertificate.checkModels_sound R.table sigma
             basisVariable (by decide)`
  complete: joint validity pulls back through the split pair to
             factor validity (the established `SubdirectPair`
             pullback), then the matching `intersectionComplete*`
             above yields `Derives sigma`.
  endpoint: `BasisFor R.table.semigroup sigma`, opposite via
             `oppositeReversed`.

Smallest compile targets: this module, then one wrapper
(`S6_5642` recommended), then the five-wrapper aggregate. -/

end SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_213M2

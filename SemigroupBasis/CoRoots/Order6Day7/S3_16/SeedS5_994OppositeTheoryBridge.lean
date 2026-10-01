import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_1092Family
import SemigroupBasis.Generated.CatalogueOrder5Part09
import SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma
import SemigroupBasis.Generated.S3_11

/-!
# Exact rank-003 theory transfer and the missing period-two reach obligation

The authenticated `S3_16 × S5_994ᵒᵖ` intersection has exactly the same
unrestricted identity theory as `S3_11 × S5_1092`. Four explicit finite
embeddings prove both implications for every `Nat`-identity. Independent,
already-complete regular-band presentations then identify that source with the
ACTUAL codex-S1 chartered pair `S3_11 × S5_1144`; all three use the same
displayed eleven-law system.

Consequently an independently proved source intersection or normalizer would
immediately certify both staged rank-003 classes. No such input is constructed
here. Four explicit soundness obstructions exclude the tempting unguarded
regular-band, capped-count, direct-parity, and opposite-parity shortcuts.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.TheoryBridge

open SemigroupBasis

universe u v

abbrev sourceParity : Semigroup (Fin 3) :=
  SemigroupBasis.Generated.S3_11.table.semigroup

abbrev sourceBand : Semigroup (Fin 5) :=
  SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup

abbrev charteredBand : Semigroup (Fin 5) :=
  SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup

/-- The staged target and generated source obligation use the same ordered
eleven identities, not merely the same finite truth table. -/
theorem basis_eq_sharedDisplayed :
    basis =
      SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_5f450af59e61df2f.basis := by
  decide

/-- The `S3_11` parity-with-zero detector embeds directly into the actual
opposite target factor on zero-based states `[0,1,2]`. -/
def sourceParityIntoTargetRight :
    Embedding sourceParity rightTable.semigroup where
  toFun := fun value =>
    if value = 0 then (0 : Fin 5)
    else if value = 1 then (1 : Fin 5)
    else (2 : Fin 5)
  map_mul := by
    intro first second
    apply Fin.ext
    revert first second
    decide
  injective := by
    intro first second equality
    revert first second
    decide

theorem sourceParityIntoTargetRight_values :
    List.ofFn
        (fun value : Fin 3 =>
          (sourceParityIntoTargetRight.toFun value).val) =
      [0, 1, 2] := by
  decide

/-- The complete regular-band detector embeds in the PRODUCT of the two
actual factors; neither target factor alone provides its full theory. -/
def sourceBandIntoTargetProduct :
    Embedding sourceBand
      (leftTable.semigroup.prod rightTable.semigroup) where
  toFun := fun value =>
    (if value = 2 then (2 : Fin 3)
      else if value = 3 then (1 : Fin 3)
      else (0 : Fin 3),
      if value = 0 then (2 : Fin 5)
      else if value = 1 then (3 : Fin 5)
      else if value = 2 then (2 : Fin 5)
      else if value = 3 then (0 : Fin 5)
      else (4 : Fin 5))
  map_mul := by
    intro first second
    apply Prod.ext
    · apply Fin.ext
      revert first second
      decide
    · apply Fin.ext
      revert first second
      decide
  injective := by
    intro first second equality
    revert first second
    decide

theorem sourceBandIntoTargetProduct_values :
    List.ofFn
        (fun value : Fin 5 =>
          ((sourceBandIntoTargetProduct.toFun value).1.val,
            (sourceBandIntoTargetProduct.toFun value).2.val)) =
      [(0, 2), (0, 3), (2, 2), (1, 0), (0, 4)] := by
  decide

/-- The actual left regular band embeds into `S5_1092` on zero-based states
`[0,3,2]`. -/
private def targetLeftIntoSourceBandMap (value : Fin 3) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 3
  else 2

def targetLeftIntoSourceBand :
    Embedding leftTable.semigroup sourceBand where
  toFun := targetLeftIntoSourceBandMap
  map_mul := by
    intro first second
    apply Fin.ext
    revert first second
    decide
  injective := by
    intro first second equality
    revert first second
    decide

theorem targetLeftIntoSourceBand_values :
    List.ofFn
        (fun value : Fin 3 =>
          (targetLeftIntoSourceBand.toFun value).val) =
      [0, 3, 2] := by
  decide

/-- The whole opposite `S5_994` embeds in the source parity/band product.
This proves the reverse theory implication without assuming a profile,
bounded alphabet, or unstated lower-factor completeness. -/
private def targetRightIntoSourceProductMap (value : Fin 5) :
    Fin 3 × Fin 5 :=
  (if value = 0 then 0
    else if value = 1 then 1
    else 2,
    if value = 0 then 3
    else if value = 1 then 3
    else if value = 2 then 0
    else if value = 3 then 1
    else 4)

def targetRightIntoSourceProduct :
    Embedding rightTable.semigroup
      (sourceParity.prod sourceBand) where
  toFun := targetRightIntoSourceProductMap
  map_mul := by
    intro first second
    apply Prod.ext
    · apply Fin.ext
      revert first second
      decide
    · apply Fin.ext
      revert first second
      decide
  injective := by
    intro first second equality
    revert first second
    decide

theorem targetRightIntoSourceProduct_values :
    List.ofFn
        (fun value : Fin 5 =>
          ((targetRightIntoSourceProduct.toFun value).1.val,
            (targetRightIntoSourceProduct.toFun value).2.val)) =
      [(0, 3), (1, 3), (2, 0), (2, 1), (2, 4)] := by
  decide

/-- Every identity valid in the actual target pair is valid in both source
detectors; the regular-band implication genuinely uses BOTH target factors. -/
theorem sourceTheory_of_target
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    identity.SatisfiedBy sourceParity ∧
      identity.SatisfiedBy sourceBand := by
  constructor
  · exact
      sourceParityIntoTargetRight.pullback_identity identity rightValid
  · exact
      sourceBandIntoTargetProduct.pullback_identity identity
        (Identity.satisfiedBy_prod leftValid rightValid)

/-- Conversely every identity valid in the source parity/band pair is valid
in both actual target factors. -/
theorem targetTheory_of_source
    (identity : Identity Nat)
    (parityValid : identity.SatisfiedBy sourceParity)
    (bandValid : identity.SatisfiedBy sourceBand) :
    identity.SatisfiedBy leftTable.semigroup ∧
      identity.SatisfiedBy rightTable.semigroup := by
  constructor
  · exact
      targetLeftIntoSourceBand.pullback_identity identity bandValid
  · exact
      targetRightIntoSourceProduct.pullback_identity identity
        (Identity.satisfiedBy_prod parityValid bandValid)

/-- Exact UNRESTRICTED factor-theory equivalence, over arbitrary natural-number
variable supports rather than a fixed finite alphabet. -/
theorem factor_theories_iff
    (identity : Identity Nat) :
    (identity.SatisfiedBy leftTable.semigroup ∧
      identity.SatisfiedBy rightTable.semigroup) ↔
      (identity.SatisfiedBy sourceParity ∧
        identity.SatisfiedBy sourceBand) := by
  constructor
  · intro valid
    exact sourceTheory_of_target identity valid.1 valid.2
  · intro valid
    exact targetTheory_of_source identity valid.1 valid.2

/-- Independent COMPLETE lower-order presentations prove that every
`S5_1144` identity is valid in `S5_1092`. -/
theorem sourceBand_valid_of_charteredBand_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy charteredBand) :
    identity.SatisfiedBy sourceBand := by
  have derivation :=
    SemigroupBasis.CoRoots.S5_1092Family.S5_1144.basis_complete.2
      identity valid
  exact fun valuation =>
    derivation.sound
      SemigroupBasis.CoRoots.S5_1092Family.S5_1092.models valuation

/-- The converse uses the other independently complete regular-band
presentation, not a one-direction finite table comparison. -/
theorem charteredBand_valid_of_sourceBand_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy sourceBand) :
    identity.SatisfiedBy charteredBand := by
  have derivation :=
    SemigroupBasis.CoRoots.S5_1092Family.S5_1092.basis_complete.2
      identity valid
  exact fun valuation =>
    derivation.sound
      SemigroupBasis.CoRoots.S5_1092Family.S5_1144.models valuation

/-- Exact target-to-CHARTERED-S1 unrestricted factor implication. -/
theorem charteredSourceTheory_of_target
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    identity.SatisfiedBy sourceParity ∧
      identity.SatisfiedBy charteredBand := by
  obtain ⟨parityValid, bandValid⟩ :=
    sourceTheory_of_target identity leftValid rightValid
  exact
    ⟨parityValid,
      charteredBand_valid_of_sourceBand_valid identity bandValid⟩

/-- Exact CHARTERED-S1-to-target unrestricted factor implication. -/
theorem targetTheory_of_charteredSource
    (identity : Identity Nat)
    (parityValid : identity.SatisfiedBy sourceParity)
    (bandValid : identity.SatisfiedBy charteredBand) :
    identity.SatisfiedBy leftTable.semigroup ∧
      identity.SatisfiedBy rightTable.semigroup :=
  targetTheory_of_source identity parityValid
    (sourceBand_valid_of_charteredBand_valid identity bandValid)

theorem chartered_factor_theories_iff
    (identity : Identity Nat) :
    (identity.SatisfiedBy leftTable.semigroup ∧
      identity.SatisfiedBy rightTable.semigroup) ↔
      (identity.SatisfiedBy sourceParity ∧
        identity.SatisfiedBy charteredBand) := by
  constructor
  · intro valid
    exact charteredSourceTheory_of_target identity valid.1 valid.2
  · intro valid
    exact targetTheory_of_charteredSource identity valid.1 valid.2

theorem sourceParityModels : Models sourceParity basis := by
  intro identity member
  exact
    sourceParityIntoTargetRight.pullback_identity identity
      (rightModels identity member)

theorem sourceBandModels : Models sourceBand basis := by
  intro identity member
  exact
    sourceBandIntoTargetProduct.pullback_identity identity
      (Identity.satisfiedBy_prod
        (leftModels identity member) (rightModels identity member))

theorem charteredBandModels : Models charteredBand basis := by
  intro identity member
  exact
    charteredBand_valid_of_sourceBand_valid identity
      (sourceBandModels identity member)

/-- Transfer an INDEPENDENTLY PROVED source intersection. The explicit input
is indispensable: this definition never fabricates unrestricted completeness. -/
def targetIntersection_of_source
    (source : IntersectionBasis sourceParity sourceBand basis) :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := by
    intro identity leftValid rightValid
    obtain ⟨parityValid, bandValid⟩ :=
      sourceTheory_of_target identity leftValid rightValid
    exact source.complete identity parityValid bandValid

/-- The reverse transfer is equally constructive, making the missing
unrestricted obligations mathematically equivalent. -/
def sourceIntersection_of_target
    (target : IntersectionBasis
      leftTable.semigroup rightTable.semigroup basis) :
    IntersectionBasis sourceParity sourceBand basis where
  leftModels := sourceParityModels
  rightModels := sourceBandModels
  complete := by
    intro identity parityValid bandValid
    obtain ⟨leftValid, rightValid⟩ :=
      targetTheory_of_source identity parityValid bandValid
    exact target.complete identity leftValid rightValid

theorem unrestricted_intersection_iff :
    Nonempty
        (IntersectionBasis leftTable.semigroup rightTable.semigroup basis) ↔
      Nonempty (IntersectionBasis sourceParity sourceBand basis) := by
  constructor
  · rintro ⟨target⟩
    exact ⟨sourceIntersection_of_target target⟩
  · rintro ⟨source⟩
    exact ⟨targetIntersection_of_source source⟩

/-- Consume the ACTUAL separately owned S1 rank-003 pair only after its
unrestricted owner seed exists. Both target classes then follow without a
new reach proof or any cross-family shortcut. -/
def targetIntersection_of_charteredSource
    (source : IntersectionBasis sourceParity charteredBand basis) :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := by
    intro identity leftValid rightValid
    obtain ⟨parityValid, bandValid⟩ :=
      charteredSourceTheory_of_target identity leftValid rightValid
    exact source.complete identity parityValid bandValid

def charteredSourceIntersection_of_target
    (target : IntersectionBasis
      leftTable.semigroup rightTable.semigroup basis) :
    IntersectionBasis sourceParity charteredBand basis where
  leftModels := sourceParityModels
  rightModels := charteredBandModels
  complete := by
    intro identity parityValid bandValid
    obtain ⟨leftValid, rightValid⟩ :=
      targetTheory_of_charteredSource identity parityValid bandValid
    exact target.complete identity leftValid rightValid

theorem chartered_unrestricted_intersection_iff :
    Nonempty
        (IntersectionBasis leftTable.semigroup rightTable.semigroup basis) ↔
      Nonempty (IntersectionBasis sourceParity charteredBand basis) := by
  constructor
  · rintro ⟨target⟩
    exact ⟨charteredSourceIntersection_of_target target⟩
  · rintro ⟨source⟩
    exact ⟨targetIntersection_of_charteredSource source⟩

/-- Reuse the kernel-green C1 quotient construction only AFTER the independent
source intersection has actually been supplied. -/
noncomputable def normalizer_of_source
    (source : IntersectionBasis sourceParity sourceBand basis) :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
      (targetIntersection_of_source source)

noncomputable def normalizer_of_charteredSource
    (source : IntersectionBasis sourceParity charteredBand basis) :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
      (targetIntersection_of_charteredSource source)

theorem s6_14872_representative_basis_of_source
    (source : IntersectionBasis sourceParity sourceBand basis) :
    BasisFor S6_14872.table.semigroup basis :=
  S6_14872.representative_basis_of_normalizer
    (normalizer_of_source source)

theorem s6_14872_opposite_basis_of_source
    (source : IntersectionBasis sourceParity sourceBand basis) :
    BasisFor S6_14872.table.semigroup.opposite
      (reversedBasis basis) :=
  S6_14872.opposite_basis_of_normalizer
    (normalizer_of_source source)

theorem s6_14883_representative_basis_of_source
    (source : IntersectionBasis sourceParity sourceBand basis) :
    BasisFor S6_14883.table.semigroup basis :=
  S6_14883.representative_basis_of_normalizer
    (normalizer_of_source source)

theorem s6_14883_opposite_basis_of_source
    (source : IntersectionBasis sourceParity sourceBand basis) :
    BasisFor S6_14883.table.semigroup.opposite
      (reversedBasis basis) :=
  S6_14883.opposite_basis_of_normalizer
    (normalizer_of_source source)

theorem s6_14872_representative_basis_of_charteredSource
    (source : IntersectionBasis sourceParity charteredBand basis) :
    BasisFor S6_14872.table.semigroup basis :=
  S6_14872.representative_basis_of_normalizer
    (normalizer_of_charteredSource source)

theorem s6_14872_opposite_basis_of_charteredSource
    (source : IntersectionBasis sourceParity charteredBand basis) :
    BasisFor S6_14872.table.semigroup.opposite
      (reversedBasis basis) :=
  S6_14872.opposite_basis_of_normalizer
    (normalizer_of_charteredSource source)

theorem s6_14883_representative_basis_of_charteredSource
    (source : IntersectionBasis sourceParity charteredBand basis) :
    BasisFor S6_14883.table.semigroup basis :=
  S6_14883.representative_basis_of_normalizer
    (normalizer_of_charteredSource source)

theorem s6_14883_opposite_basis_of_charteredSource
    (source : IntersectionBasis sourceParity charteredBand basis) :
    BasisFor S6_14883.table.semigroup.opposite
      (reversedBasis basis) :=
  S6_14883.opposite_basis_of_normalizer
    (normalizer_of_charteredSource source)

/-- The approved generic transport remains available, with ALL three
independent obligations retained as explicit parameters. -/
noncomputable def transportedNormalizer_of_source
    (source : IntersectionBasis sourceParity sourceBand basis)
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
    (normalizer_of_source source) lawDerivations leftTheory rightTheory

/-- Attempt 1 is IMPOSSIBLE: directly transporting the complete regular-band
normalizer would assert idempotence in the actual period-two right factor. -/
theorem regularBandIdempotence_not_derivable :
    ¬ Derives basis (Word.mk 0 []) (Word.mk 0 [0]) := by
  intro derivation
  have evaluated :=
    derivation.sound rightModels (fun _ => (1 : Fin 5))
  change (1 : Fin 5) = 0 at evaluated
  exact (by decide : (1 : Fin 5) ≠ 0) evaluated

/-- Attempt 2 is IMPOSSIBLE: the kernel-green shared capped-count engine has
period one (`xx = xxx`), while this exact pair has period two. -/
theorem cappedCountPower_not_derivable :
    ¬ Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) := by
  intro derivation
  have evaluated :=
    derivation.sound rightModels (fun _ => (1 : Fin 5))
  change (0 : Fin 5) = 1 at evaluated
  exact (by decide : (0 : Fin 5) ≠ 1) evaluated

/-- Attempt 3 is IMPOSSIBLE: the unguarded direct parity-initial gather is
false in the actual OPPOSITE right factor. -/
theorem directParityGather_not_derivable :
    ¬ Derives basis
      (Word.mk 0 [1, 0]) (Word.mk 0 [0, 1]) := by
  intro derivation
  let valuation : Nat → Fin 5 :=
    fun letter => if letter = 0 then 3 else 4
  have evaluated := derivation.sound rightModels valuation
  change (3 : Fin 5) = 4 at evaluated
  exact (by decide : (3 : Fin 5) ≠ 4) evaluated

/-- The dual shortcut also fails: the opposite parity gather is valid on the
right but false on the actual left regular band. -/
theorem oppositeParityGather_not_derivable :
    ¬ Derives basis
      (Word.mk 0 [1, 0]) (Word.mk 1 [0, 0]) := by
  intro derivation
  let valuation : Nat → Fin 3 :=
    fun letter => if letter = 0 then 0 else 2
  have evaluated := derivation.sound leftModels valuation
  change (0 : Fin 3) = 2 at evaluated
  exact (by decide : (0 : Fin 3) ≠ 2) evaluated

/-- The otherwise kernel-green C1 Condition-14 interior engine cannot be
transported literally: its endpoint-exchange axiom changes last-occurrence
order in the opposite target factor. -/
theorem condition14EndpointExchange_not_derivable :
    ¬ Derives basis
      (Word.mk 0 [1, 0, 1]) (Word.mk 0 [1, 1, 0]) := by
  intro derivation
  let valuation : Nat → Fin 5 :=
    fun letter => if letter = 0 then 3 else 4
  have evaluated := derivation.sound rightModels valuation
  change (4 : Fin 5) = 3 at evaluated
  exact (by decide : (4 : Fin 5) ≠ 3) evaluated

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.TheoryBridge

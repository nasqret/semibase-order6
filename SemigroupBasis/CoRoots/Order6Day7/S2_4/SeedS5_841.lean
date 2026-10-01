import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank002
import SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_841
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-!
# An unrestricted `S2_4 × S5_841` family seed

The actual left-zero factor fixes the initial variable. The independently
complete `S5_841` factor supplies its exact capped-multiplicity signature,
which in particular fixes the complete support. Together these two genuine
semantic implications prove validity in `S3_15`; self-duality of `S5_841`
then transfers the reversed identity into the kernel-verified rank-064
`S3_15ᵒᵖ × S5_841` seed.

Every reversed rank-064 axiom is explicitly replayed into the authenticated
rank-002 displayed basis using a concrete variable permutation. The resulting
unrestricted intersection completeness is proved before the reviewed quotient
normalizer and both class orientation endpoints are constructed.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank002.Seed

open SemigroupBasis
open SemigroupBasis.Examples

universe u v

private def renameThree
    (first second third : Nat) : Nat → Word Nat
  | 0 => Word.singleton first
  | 1 => Word.singleton second
  | 2 => Word.singleton third
  | marker + 3 => Word.singleton (marker + 3)

/-- Each reversed axiom of the already kernel-verified rank-064 seed is
present in the exact rank-002 list after its explicit variable permutation. -/
theorem reversedSourceAxiomsDeriveDisplayed
    (identity : Identity Nat)
    (member :
      identity ∈
        reversedBasis
          SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank064.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [reversedBasis,
    SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank064.basis,
    List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0])
    exact Derives.fromBasis (e := law00) (by simp [basis])
  · change Derives basis (Word.mk 0 [1, 0, 0]) (Word.mk 0 [1, 0])
    exact (Derives.fromBasis (e := law02) (by simp [basis])).symm
  · change Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 1, 0])
    exact (Derives.fromBasis (e := law01) (by simp [basis])).symm
  · change
      Derives basis
        (Word.mk 1 [0, 1, 0])
        (Word.mk 1 [0, 0, 1])
    have primitive :
        Derives basis
          (Word.mk 0 [1, 0, 1])
          (Word.mk 0 [1, 1, 0]) :=
      Derives.fromBasis (e := law03) (by simp [basis])
    simpa [renameThree, Word.bind, Word.singleton, Word.append] using
      Derives.subst primitive (renameThree 1 0 2)
  · change
      Derives basis
        (Word.mk 2 [1, 0, 1, 0])
        (Word.mk 2 [0, 1, 1, 0])
    have primitive :
        Derives basis
          (Word.mk 0 [1, 2, 1, 2])
          (Word.mk 0 [2, 1, 1, 2]) :=
      Derives.fromBasis (e := law07) (by simp [basis])
    simpa [renameThree, Word.bind, Word.singleton, Word.append] using
      Derives.subst primitive (renameThree 2 1 0)
  · change
      Derives basis
        (Word.mk 0 [2, 0, 1, 0])
        (Word.mk 0 [2, 1, 0])
    have primitive :
        Derives basis
          (Word.mk 0 [1, 0, 2, 0])
          (Word.mk 0 [1, 2, 0]) :=
      Derives.fromBasis (e := law04) (by simp [basis])
    simpa [renameThree, Word.bind, Word.singleton, Word.append] using
      Derives.subst primitive (renameThree 0 2 1)
  · change
      Derives basis
        (Word.mk 1 [2, 0, 1, 0])
        (Word.mk 1 [2, 0, 0, 1])
    have primitive :
        Derives basis
          (Word.mk 0 [1, 2, 0, 2])
          (Word.mk 0 [1, 2, 2, 0]) :=
      Derives.fromBasis (e := law06) (by simp [basis])
    simpa [renameThree, Word.bind, Word.singleton, Word.append] using
      Derives.subst primitive (renameThree 1 2 0)
  · change
      Derives basis
        (Word.mk 1 [0, 2, 1, 0])
        (Word.mk 1 [0, 2, 0, 1])
    have primitive :
        Derives basis
          (Word.mk 0 [1, 2, 0, 1])
          (Word.mk 0 [1, 2, 1, 0]) :=
      Derives.fromBasis (e := law05) (by simp [basis])
    simpa [renameThree, Word.bind, Word.singleton, Word.append] using
      Derives.subst primitive (renameThree 1 0 2)

/-- Validity in the actual `S2_4` left-zero factor fixes the initial
variable without any finite-table separation claim. -/
theorem leftValid_head
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  change identity.SatisfiedBy leftZeroTwo.semigroup at valid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 :=
    fun letter => if letter = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

/-- The actual `S5_841` capped-multiplicity signature fixes unrestricted
support, not merely the finite displayed alphabet. -/
theorem rightValid_support
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup)
    (letter : Nat) :
    letter ∈ identity.lhs.toList ↔ letter ∈ identity.rhs.toList := by
  have actual :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_841.table.semigroup := by
    exact valid
  have capped :=
    (SemigroupBasis.CoRoots.S5_841.catalogueValid_sameM20Signature
      identity actual).cappedMultiplicity letter
  change
    Nat.min (identity.lhs.toList.count letter) 2 =
      Nat.min (identity.rhs.toList.count letter) 2 at capped
  have zeros :
      identity.lhs.toList.count letter = 0 ↔
        identity.rhs.toList.count letter = 0 := by
    simp only [Nat.min_def] at capped
    split at capped <;> split at capped <;> omega
  constructor
  · intro leftMember
    apply (List.count_pos_iff).mp
    apply Nat.pos_of_ne_zero
    intro rightZero
    have leftZero := zeros.mpr rightZero
    exact (List.count_eq_zero.mp leftZero) leftMember
  · intro rightMember
    apply (List.count_pos_iff).mp
    apply Nat.pos_of_ne_zero
    intro leftZero
    have rightZero := zeros.mp leftZero
    exact (List.count_eq_zero.mp rightZero) rightMember

/-- The independent common head and unrestricted common support are exactly
the complete left-normal-band profile of the actual `S3_15` factor. -/
theorem promotedLeftValidity
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.Generated.S3_15.table.semigroup := by
  have heads := leftValid_head identity leftValid
  have supports := rightValid_support identity rightValid
  have leftExpansion :=
    leftNormalBandDerivesContentExpansion identity.lhs identity.rhs
      (fun letter member => (supports letter).mpr member)
  have rightExpansion :=
    leftNormalBandDerivesContentExpansion identity.rhs identity.lhs
      (fun letter member => (supports letter).mp member)
  have complete :
      Derives leftNormalBandThreeBasis identity.lhs identity.rhs :=
    leftExpansion.trans <|
      (leftNormalBandDerivesConcatSwap
        identity.lhs identity.rhs heads).trans rightExpansion.symm
  change identity.SatisfiedBy leftNormalBandFifteen.semigroup
  exact fun valuation =>
    Derives.sound leftNormalBandFifteenBasis_models complete valuation

/-- `S5_841` is independently self-dual, so reversing an identity preserves
validity in its actual five-element right factor. -/
theorem reversedRightValidity
    (identity : Identity Nat)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    identity.reversed.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_841.table.semigroup := by
  have oppositeValid :=
    SemigroupBasis.CoRoots.S5_841.selfDuality.pullback_identity
      identity rightValid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.Generated.Catalogue.S5_841.table.semigroup).mp
      oppositeValid

/-- Apply the independently kernel-verified rank-064 unrestricted seed to
the reversed identity, then explicitly transport its eight reversed laws. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have promoted := promotedLeftValidity identity leftValid rightValid
  have sourceLeft :
      identity.reversed.SatisfiedBy
        SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable.semigroup := by
    rw [SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable_semigroup]
    apply
      (Identity.satisfiedBy_opposite_iff_reversed identity.reversed
        SemigroupBasis.Generated.S3_15.table.semigroup).mpr
    simpa [Identity.reversed] using promoted
  have sourceRight := reversedRightValidity identity rightValid
  have source :=
    SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_841.derivesOfFactorValid
      identity.reversed sourceLeft sourceRight
  have returned :
      Derives
        (reversedBasis
          SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank064.basis)
        identity.lhs identity.rhs := by
    simpa [Identity.reversed] using source.reverse
  exact returned.transport reversedSourceAxiomsDeriveDisplayed

/-- The reviewed intersection basis appears only after genuine unrestricted
cross-family theory transfer and all eight source-law derivations. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Certified reusable rank-002 family seed. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_13356_representative_basis :
    BasisFor S6_13356.table.semigroup basis :=
  S6_13356.representative_basis_of_normalizer normalizer

theorem s6_13356_opposite_basis :
    BasisFor S6_13356.table.semigroup.opposite (reversedBasis basis) :=
  S6_13356.opposite_basis_of_normalizer normalizer

/-- Reviewed transport requires actual displayed-law derivations and both
independent unrestricted target-factor theory implications. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank002.Seed

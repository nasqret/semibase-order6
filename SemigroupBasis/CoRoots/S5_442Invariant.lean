import SemigroupBasis.CoRoots.S5_442
import SemigroupBasis.CoRoots.S5_442Factors
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Generated.S3_11
import SemigroupBasis.Generated.S4_70

namespace SemigroupBasis.CoRoots

open SemigroupBasis

namespace S5_442Invariant

open SemigroupBasis.Examples

private theorem equalEval_of_table_eq
    {source target : FiniteTable}
    (tableEq : source = target)
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin source.order,
        source.semigroup.eval valuation left =
          source.semigroup.eval valuation right) :
    ∀ valuation : Nat → Fin target.order,
      target.semigroup.eval valuation left =
        target.semigroup.eval valuation right := by
  cases tableEq
  exact equalEval

/-- Equality of the exact ordered `S4_70` component signatures. -/
def SameComponentSignature (left right : Word Nat) : Prop :=
  connectedComponentSignaturesWord left =
    connectedComponentSignaturesWord right

/-- Pointwise equality of all occurrence counts modulo two. -/
def SameOccurrenceParity (left right : Word Nat) : Prop :=
  ∀ letter,
    left.toList.count letter % 2 =
      right.toList.count letter % 2

/-- The exact invariant recorded for the `S5_442`/`S5_613` family. -/
structure SameParityComponentSignature
    (left right : Word Nat) : Prop where
  components : SameComponentSignature left right
  parity : SameOccurrenceParity left right

abbrev sameSignature (left right : Word Nat) : Prop :=
  SameParityComponentSignature left right

namespace SameParityComponentSignature

theorem refl (word : Word Nat) :
    SameParityComponentSignature word word :=
  ⟨rfl, fun _ => rfl⟩

theorem symm {left right : Word Nat}
    (same : SameParityComponentSignature left right) :
    SameParityComponentSignature right left :=
  ⟨same.components.symm, fun letter => (same.parity letter).symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameParityComponentSignature left middle)
    (second : SameParityComponentSignature middle right) :
    SameParityComponentSignature left right :=
  ⟨first.components.trans second.components,
    fun letter =>
      (first.parity letter).trans (second.parity letter)⟩

end SameParityComponentSignature

/-- Equal component signatures already imply equal support. -/
theorem sameSupport_of_sameComponentSignature
    {left right : Word Nat}
    (same : SameComponentSignature left right) :
    ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList := by
  intro letter
  have renderEq :=
    connectedComponentCanonicalRender_eq_of_signature_eq same
  rw [← connectedComponentCanonicalRender_mem_iff letter left,
    ← connectedComponentCanonicalRender_mem_iff letter right,
    renderEq]

/-- Equal `S4_70` term functions determine the exact ordered component
signature. -/
theorem sameComponentSignature_of_connectedComponentFour_equalEval
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        connectedComponentFour.semigroup.eval valuation left =
          connectedComponentFour.semigroup.eval valuation right) :
    SameComponentSignature left right := by
  have leftDerivation :=
    connectedComponentFour_derivesCanonical left
  have rightDerivation :=
    connectedComponentFour_derivesCanonical right
  have normalizedEval :
      ∀ valuation : Nat → Fin 4,
        connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender left) =
          connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender right) := by
    intro valuation
    have leftSound :=
      leftDerivation.sound
        connectedComponentFourBasis_models valuation
    have rightSound :=
      rightDerivation.sound
        connectedComponentFourBasis_models valuation
    exact leftSound.symm.trans <|
      (equalEval valuation).trans rightSound
  apply connectedComponentCanonical_eq_of_equalEval
    (connectedComponentFourSignaturesWord_canonical left)
    (connectedComponentFourSignaturesWord_canonical right)
    (connectedComponentCanonicalRender left)
    (connectedComponentCanonicalRender right)
  · change
      (connectedComponentCanonicalRender left).toList =
        connectedComponentCanonicalRenderList left.toList
    exact connectedComponentCanonicalRender_toList left
  · change
      (connectedComponentCanonicalRender right).toList =
        connectedComponentCanonicalRenderList right.toList
    exact connectedComponentCanonicalRender_toList right
  · exact normalizedEval

/-- The ordered component signature is also sufficient for equality of
`S4_70` term functions. -/
theorem connectedComponentFour_equalEval_of_sameComponentSignature
    (left right : Word Nat)
    (same : SameComponentSignature left right) :
    ∀ valuation : Nat → Fin 4,
      connectedComponentFour.semigroup.eval valuation left =
        connectedComponentFour.semigroup.eval valuation right := by
  intro valuation
  have leftSound :=
    (connectedComponentFour_derivesCanonical left).sound
      connectedComponentFourBasis_models valuation
  have rightSound :=
    (connectedComponentFour_derivesCanonical right).sound
      connectedComponentFourBasis_models valuation
  have renderEq :=
    connectedComponentCanonicalRender_eq_of_signature_eq same
  calc
    connectedComponentFour.semigroup.eval valuation left =
        connectedComponentFour.semigroup.eval valuation
          (connectedComponentCanonicalRender left) := leftSound
    _ = connectedComponentFour.semigroup.eval valuation
          (connectedComponentCanonicalRender right) := by
          rw [renderEq]
    _ = connectedComponentFour.semigroup.eval valuation right :=
      rightSound.symm

/-- A direct derivation in the cyclic group basis from equal parity vectors. -/
theorem cyclicDerives_of_sameOccurrenceParity
    (left right : Word Nat)
    (same : SameOccurrenceParity left right) :
    Derives cyclicTwoBasis left right := by
  have reducedPerm :
      (parityReduce left.toList).Perm
        (parityReduce right.toList) :=
    parityReduce_perm_of_parity_eq same
  have leftNormal := cyclicDerivesNormal left
  have rightNormal := cyclicDerivesNormal right
  cases leftReduction : parityReduce left.toList with
  | nil =>
      rw [leftReduction] at reducedPerm
      have rightReduction : parityReduce right.toList = [] :=
        reducedPerm.nil_eq.symm
      rw [leftReduction] at leftNormal
      rw [rightReduction] at rightNormal
      exact Derives.trans leftNormal <|
        Derives.trans
          (cyclicDerivesCommonSquare
            (Word.singleton left.head)
            (Word.singleton right.head))
          (Derives.symm rightNormal)
  | cons leftHead leftTail =>
      cases rightReduction : parityReduce right.toList with
      | nil =>
          rw [leftReduction, rightReduction] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons rightHead rightTail =>
          rw [leftReduction] at leftNormal
          rw [rightReduction] at rightNormal
          rw [leftReduction, rightReduction] at reducedPerm
          exact Derives.trans leftNormal <|
            Derives.trans
              (cyclicDerivesPermutation
                (⟨leftHead, leftTail⟩ : Word Nat)
                (⟨rightHead, rightTail⟩ : Word Nat)
                reducedPerm)
              (Derives.symm rightNormal)

/-- A direct derivation in the `S3_11` parity-support basis from equal
support and parity. -/
theorem commutativeParityDerives_of_sameSupportParity
    (left right : Word Nat)
    (support :
      ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList)
    (parity : SameOccurrenceParity left right) :
    Derives commutativeParityBasis left right := by
  have reducedPerm :
      (positiveParityReduce left.toList).Perm
        (positiveParityReduce right.toList) :=
    positiveParityReduce_perm support parity
  have leftNormal := positiveParityDerivesNormal left
  have rightNormal := positiveParityDerivesNormal right
  cases leftReduction : positiveParityReduce left.toList with
  | nil =>
      have present :
          left.head ∈ positiveParityReduce left.toList :=
        (mem_positiveParityReduce_iff _ _).mpr (by
          simp [Word.toList])
      exact False.elim (by simpa [leftReduction] using present)
  | cons leftHead leftTail =>
      cases rightReduction : positiveParityReduce right.toList with
      | nil =>
          rw [leftReduction, rightReduction] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons rightHead rightTail =>
          rw [leftReduction] at leftNormal
          rw [rightReduction] at rightNormal
          rw [leftReduction, rightReduction] at reducedPerm
          exact Derives.trans leftNormal <|
            Derives.trans
              (parityDerivesPermutation
                (⟨leftHead, leftTail⟩ : Word Nat)
                (⟨rightHead, rightTail⟩ : Word Nat)
                reducedPerm)
              (Derives.symm rightNormal)

theorem sameOccurrenceParity_of_cyclicTwo_equalEval
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 2,
        cyclicTwo.semigroup.eval valuation left =
          cyclicTwo.semigroup.eval valuation right) :
    SameOccurrenceParity left right :=
  cyclicValid_parity_eq
    (⟨left, right⟩ : Identity Nat) equalEval

theorem sameOccurrenceParity_of_parityZeroThree_equalEval
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 3,
        parityZeroThree.semigroup.eval valuation left =
          parityZeroThree.semigroup.eval valuation right) :
    SameOccurrenceParity left right :=
  parityZeroValid_parity
    (⟨left, right⟩ : Identity Nat) equalEval

theorem cyclicTwo_equalEval_of_sameOccurrenceParity
    (left right : Word Nat)
    (same : SameOccurrenceParity left right) :
    ∀ valuation : Nat → Fin 2,
      cyclicTwo.semigroup.eval valuation left =
        cyclicTwo.semigroup.eval valuation right :=
  (cyclicDerives_of_sameOccurrenceParity left right same).sound
    cyclicTwoBasis_models

theorem parityZeroThree_equalEval_of_sameSignature
    (left right : Word Nat)
    (same : SameParityComponentSignature left right) :
    ∀ valuation : Nat → Fin 3,
      parityZeroThree.semigroup.eval valuation left =
        parityZeroThree.semigroup.eval valuation right :=
  (commutativeParityDerives_of_sameSupportParity
      left right
      (sameSupport_of_sameComponentSignature same.components)
      same.parity).sound
    parityZeroThreeBasis_models

theorem sameSignature_of_connectedComponentFour_cyclicTwo_equalEval
    (left right : Word Nat)
    (componentEqual :
      ∀ valuation : Nat → Fin 4,
        connectedComponentFour.semigroup.eval valuation left =
          connectedComponentFour.semigroup.eval valuation right)
    (parityEqual :
      ∀ valuation : Nat → Fin 2,
        cyclicTwo.semigroup.eval valuation left =
          cyclicTwo.semigroup.eval valuation right) :
    SameParityComponentSignature left right :=
  ⟨sameComponentSignature_of_connectedComponentFour_equalEval
      left right componentEqual,
    sameOccurrenceParity_of_cyclicTwo_equalEval
      left right parityEqual⟩

theorem sameSignature_of_connectedComponentFour_parityZeroEqualEval
    (left right : Word Nat)
    (componentEqual :
      ∀ valuation : Nat → Fin 4,
        connectedComponentFour.semigroup.eval valuation left =
          connectedComponentFour.semigroup.eval valuation right)
    (parityEqual :
      ∀ valuation : Nat → Fin 3,
        parityZeroThree.semigroup.eval valuation left =
          parityZeroThree.semigroup.eval valuation right) :
    SameParityComponentSignature left right :=
  ⟨sameComponentSignature_of_connectedComponentFour_equalEval
      left right componentEqual,
    sameOccurrenceParity_of_parityZeroThree_equalEval
      left right parityEqual⟩

theorem catalogueS4_70_table_eq_connectedComponentFour :
    Generated.Catalogue.S4_70.table = connectedComponentFour := by
  rw [← Generated.S4_70.table_eq_canonical_catalogue]
  exact Generated.S4_70.table_eq_catalogue_model

theorem catalogueS2_2_table_eq_cyclicTwo :
    Generated.Catalogue.S2_2.table = cyclicTwo := by
  rw [← Generated.S2_2.table_eq_catalogue_model]
  unfold Generated.Catalogue.S2_2.table
    Generated.Catalogue.S2_2.mul Generated.S2_2.table cyclicTwoMul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext left right
  decide +revert

theorem catalogueS3_11_table_eq_parityZeroThree :
    Generated.Catalogue.S3_11.table = parityZeroThree := by
  rw [← Generated.S3_11.table_eq_canonical_catalogue]
  exact Generated.S3_11.table_eq_catalogue_model

theorem sameSignature_of_catalogue_s4_70_s2_2_equalEval
    (left right : Word Nat)
    (componentEqual :
      ∀ valuation : Nat → Fin 4,
        Generated.Catalogue.S4_70.table.semigroup.eval
            valuation left =
          Generated.Catalogue.S4_70.table.semigroup.eval
            valuation right)
    (parityEqual :
      ∀ valuation : Nat → Fin 2,
        Generated.Catalogue.S2_2.table.semigroup.eval
            valuation left =
          Generated.Catalogue.S2_2.table.semigroup.eval
            valuation right) :
    SameParityComponentSignature left right :=
  sameSignature_of_connectedComponentFour_cyclicTwo_equalEval
    left right
    (equalEval_of_table_eq
      catalogueS4_70_table_eq_connectedComponentFour
      left right componentEqual)
    (equalEval_of_table_eq
      catalogueS2_2_table_eq_cyclicTwo
      left right parityEqual)

theorem sameSignature_of_catalogue_s4_70_s3_11_equalEval
    (left right : Word Nat)
    (componentEqual :
      ∀ valuation : Nat → Fin 4,
        Generated.Catalogue.S4_70.table.semigroup.eval
            valuation left =
          Generated.Catalogue.S4_70.table.semigroup.eval
            valuation right)
    (parityEqual :
      ∀ valuation : Nat → Fin 3,
        Generated.Catalogue.S3_11.table.semigroup.eval
            valuation left =
          Generated.Catalogue.S3_11.table.semigroup.eval
            valuation right) :
    SameParityComponentSignature left right :=
  sameSignature_of_connectedComponentFour_parityZeroEqualEval
    left right
    (equalEval_of_table_eq
      catalogueS4_70_table_eq_connectedComponentFour
      left right componentEqual)
    (equalEval_of_table_eq
      catalogueS3_11_table_eq_parityZeroThree
      left right parityEqual)

theorem catalogue_s4_70_equalEval_of_sameSignature
    (left right : Word Nat)
    (same : SameParityComponentSignature left right) :
    ∀ valuation : Nat → Fin 4,
      Generated.Catalogue.S4_70.table.semigroup.eval
          valuation left =
        Generated.Catalogue.S4_70.table.semigroup.eval
          valuation right :=
  equalEval_of_table_eq
    catalogueS4_70_table_eq_connectedComponentFour.symm
    left right
    (connectedComponentFour_equalEval_of_sameComponentSignature
      left right same.components)

theorem catalogue_s2_2_equalEval_of_sameSignature
    (left right : Word Nat)
    (same : SameParityComponentSignature left right) :
    ∀ valuation : Nat → Fin 2,
      Generated.Catalogue.S2_2.table.semigroup.eval
          valuation left =
        Generated.Catalogue.S2_2.table.semigroup.eval
          valuation right :=
  equalEval_of_table_eq
    catalogueS2_2_table_eq_cyclicTwo.symm
    left right
    (cyclicTwo_equalEval_of_sameOccurrenceParity
      left right same.parity)

theorem catalogue_s3_11_equalEval_of_sameSignature
    (left right : Word Nat)
    (same : SameParityComponentSignature left right) :
    ∀ valuation : Nat → Fin 3,
      Generated.Catalogue.S3_11.table.semigroup.eval
          valuation left =
        Generated.Catalogue.S3_11.table.semigroup.eval
          valuation right :=
  equalEval_of_table_eq
    catalogueS3_11_table_eq_parityZeroThree.symm
    left right
    (parityZeroThree_equalEval_of_sameSignature
      left right same)

end S5_442Invariant

namespace S5_442

private theorem catalogueS4_70Models :
    Models Generated.Catalogue.S4_70.table.semigroup basis := by
  rw [S5_442Invariant.catalogueS4_70_table_eq_connectedComponentFour]
  exact basis_models_connectedComponentFour

private theorem catalogueS2_2Models :
    Models Generated.Catalogue.S2_2.table.semigroup basis := by
  rw [S5_442Invariant.catalogueS2_2_table_eq_cyclicTwo]
  exact basis_models_cyclicTwo

/-- The 20 laws model the catalogue representative `S5_442`. -/
theorem catalogueModels :
    Models Generated.Catalogue.S5_442.table.semigroup basis := by
  intro identity member
  exact
    (S5_442Factors.S5_442.valid_iff_factors identity).2
      ⟨catalogueS4_70Models identity member,
        catalogueS2_2Models identity member⟩

/-- Every derivation from the 20 laws preserves the exact component/parity
signature. -/
theorem derives_sameParityComponentSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_442Invariant.SameParityComponentSignature left right :=
  S5_442Invariant.sameSignature_of_connectedComponentFour_cyclicTwo_equalEval
    left right
    (fun valuation =>
      derivation.sound basis_models_connectedComponentFour valuation)
    (fun valuation =>
      derivation.sound basis_models_cyclicTwo valuation)

theorem valid_sameParityComponentSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_442.table.semigroup) :
    S5_442Invariant.SameParityComponentSignature
      identity.lhs identity.rhs :=
  S5_442Invariant.sameSignature_of_catalogue_s4_70_s2_2_equalEval
    identity.lhs identity.rhs
    (S5_442Factors.S5_442.valid_s4_70 identity valid)
    (S5_442Factors.S5_442.valid_s2_2 identity valid)

theorem valid_of_sameParityComponentSignature
    (identity : Identity Nat)
    (same :
      S5_442Invariant.SameParityComponentSignature
        identity.lhs identity.rhs) :
    identity.SatisfiedBy
      Generated.Catalogue.S5_442.table.semigroup :=
  (S5_442Factors.S5_442.valid_iff_factors identity).2
    ⟨S5_442Invariant.catalogue_s4_70_equalEval_of_sameSignature
        identity.lhs identity.rhs same,
      S5_442Invariant.catalogue_s2_2_equalEval_of_sameSignature
        identity.lhs identity.rhs same⟩

theorem satisfiedBy_iff_sameParityComponentSignature
    (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_442.table.semigroup ↔
      S5_442Invariant.SameParityComponentSignature
        identity.lhs identity.rhs :=
  ⟨valid_sameParityComponentSignature identity,
    valid_of_sameParityComponentSignature identity⟩

end S5_442

namespace S5_613

open SemigroupBasis.CoRoots.S5_442

private theorem catalogueS4_70Models :
    Models Generated.Catalogue.S4_70.table.semigroup basis := by
  rw [S5_442Invariant.catalogueS4_70_table_eq_connectedComponentFour]
  exact basis_models_connectedComponentFour

private theorem catalogueS3_11Models :
    Models Generated.Catalogue.S3_11.table.semigroup basis := by
  rw [S5_442Invariant.catalogueS3_11_table_eq_parityZeroThree]
  exact basis_models_parityZeroThree

/-- The same 20 laws model the non-self-dual catalogue endpoint `S5_613`. -/
theorem catalogueModels :
    Models Generated.Catalogue.S5_613.table.semigroup basis := by
  intro identity member
  exact
    (S5_442Factors.S5_613.valid_iff_factors identity).2
      ⟨catalogueS4_70Models identity member,
        catalogueS3_11Models identity member⟩

theorem valid_sameParityComponentSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_613.table.semigroup) :
    S5_442Invariant.SameParityComponentSignature
      identity.lhs identity.rhs :=
  S5_442Invariant.sameSignature_of_catalogue_s4_70_s3_11_equalEval
    identity.lhs identity.rhs
    (S5_442Factors.S5_613.valid_s4_70 identity valid)
    (S5_442Factors.S5_613.valid_s3_11 identity valid)

theorem valid_of_sameParityComponentSignature
    (identity : Identity Nat)
    (same :
      S5_442Invariant.SameParityComponentSignature
        identity.lhs identity.rhs) :
    identity.SatisfiedBy
      Generated.Catalogue.S5_613.table.semigroup :=
  (S5_442Factors.S5_613.valid_iff_factors identity).2
    ⟨S5_442Invariant.catalogue_s4_70_equalEval_of_sameSignature
        identity.lhs identity.rhs same,
      S5_442Invariant.catalogue_s3_11_equalEval_of_sameSignature
        identity.lhs identity.rhs same⟩

theorem satisfiedBy_iff_sameParityComponentSignature
    (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_613.table.semigroup ↔
      S5_442Invariant.SameParityComponentSignature
        identity.lhs identity.rhs :=
  ⟨valid_sameParityComponentSignature identity,
    valid_of_sameParityComponentSignature identity⟩

end S5_613

end SemigroupBasis.CoRoots

import SemigroupBasis.CoRoots.S5_400CanonicalSufficiency

namespace SemigroupBasis.Generated.S5_400PublishedRoots

open SemigroupBasis

namespace S5_400

theorem models :
    Models Generated.Catalogue.S5_400.table.semigroup
      SemigroupBasis.CoRoots.S5_400.basis :=
  SemigroupBasis.CoRoots.S5_400.catalogueS5_400Models

theorem oppositeModels :
    Models Generated.Catalogue.S5_400.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_400.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_400.oppositeBasis] using
    models.oppositeReversed

/-- The exact anti-isomorphism permutation `[1, 3, 2, 4, 5]`. -/
def selfDualValue (value : Fin 5) : Fin 5 :=
  if value = 1 then 2
  else if value = 2 then 1
  else value

def selfDualValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 5 => (selfDualValue value).val + 1

theorem selfDualValuesOneBased_certificate :
    selfDualValuesOneBased = [1, 3, 2, 4, 5] := by
  decide

@[simp]
theorem selfDualValue_involutive (value : Fin 5) :
    selfDualValue (selfDualValue value) = value := by
  decide +revert

def selfDualEmbedding :
    Embedding Generated.Catalogue.S5_400.table.semigroup.opposite
      Generated.Catalogue.S5_400.table.semigroup where
  toFun := selfDualValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality := congrArg selfDualValue equality
    simpa using inverseEquality

def selfDualReverseEmbedding :
    Embedding Generated.Catalogue.S5_400.table.semigroup
      Generated.Catalogue.S5_400.table.semigroup.opposite where
  toFun := selfDualValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality := congrArg selfDualValue equality
    simpa using inverseEquality

theorem sameIdentityTheory_opposite :
    SameIdentityTheory
      Generated.Catalogue.S5_400.table.semigroup
      Generated.Catalogue.S5_400.table.semigroup.opposite := by
  intro identity
  constructor
  · exact selfDualEmbedding.pullback_identity identity
  · exact selfDualReverseEmbedding.pullback_identity identity

theorem representativeBasisFor_of_publishedCompleteness
    (complete :
      SemigroupBasis.CoRoots.S5_400.M6CompletenessObligation) :
    BasisFor Generated.Catalogue.S5_400.table.semigroup
      SemigroupBasis.CoRoots.S5_400.basis :=
  SemigroupBasis.CoRoots.S5_400.catalogueS5_400BasisFor_of_publishedCompleteness
    complete

theorem oppositeBasisFor_of_publishedCompleteness
    (complete :
      SemigroupBasis.CoRoots.S5_400.M6CompletenessObligation) :
    BasisFor Generated.Catalogue.S5_400.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_400.oppositeBasis := by
    simpa [SemigroupBasis.CoRoots.S5_400.oppositeBasis] using
      (representativeBasisFor_of_publishedCompleteness complete).oppositeReversed

/-- Unconditional catalogue endpoint from Edmunds' canonical-form proof. -/
theorem representativeBasisFor :
    BasisFor Generated.Catalogue.S5_400.table.semigroup
      SemigroupBasis.CoRoots.S5_400.basis :=
  representativeBasisFor_of_publishedCompleteness
    SemigroupBasis.CoRoots.S5_400.m6Completeness

/-- The self-dual opposite endpoint, retaining the reversed basis. -/
theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_400.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_400.oppositeBasis :=
  oppositeBasisFor_of_publishedCompleteness
    SemigroupBasis.CoRoots.S5_400.m6Completeness

end S5_400

namespace S5_840

theorem models :
    Models Generated.Catalogue.S5_840.table.semigroup
      SemigroupBasis.CoRoots.S5_400.basis :=
  SemigroupBasis.CoRoots.S5_400.catalogueS5_840Models

theorem oppositeModels :
    Models Generated.Catalogue.S5_840.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_400.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_400.oppositeBasis] using
    models.oppositeReversed

/-- The exact anti-isomorphism permutation `[1, 2, 4, 3, 5]`. -/
def selfDualValue (value : Fin 5) : Fin 5 :=
  if value = 2 then 3
  else if value = 3 then 2
  else value

def selfDualValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 5 => (selfDualValue value).val + 1

theorem selfDualValuesOneBased_certificate :
    selfDualValuesOneBased = [1, 2, 4, 3, 5] := by
  decide

@[simp]
theorem selfDualValue_involutive (value : Fin 5) :
    selfDualValue (selfDualValue value) = value := by
  decide +revert

def selfDualEmbedding :
    Embedding Generated.Catalogue.S5_840.table.semigroup.opposite
      Generated.Catalogue.S5_840.table.semigroup where
  toFun := selfDualValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality := congrArg selfDualValue equality
    simpa using inverseEquality

def selfDualReverseEmbedding :
    Embedding Generated.Catalogue.S5_840.table.semigroup
      Generated.Catalogue.S5_840.table.semigroup.opposite where
  toFun := selfDualValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality := congrArg selfDualValue equality
    simpa using inverseEquality

theorem sameIdentityTheory_opposite :
    SameIdentityTheory
      Generated.Catalogue.S5_840.table.semigroup
      Generated.Catalogue.S5_840.table.semigroup.opposite := by
  intro identity
  constructor
  · exact selfDualEmbedding.pullback_identity identity
  · exact selfDualReverseEmbedding.pullback_identity identity

theorem representativeBasisFor_of_publishedCompleteness
    (complete :
      SemigroupBasis.CoRoots.S5_400.M19CompletenessObligation) :
    BasisFor Generated.Catalogue.S5_840.table.semigroup
      SemigroupBasis.CoRoots.S5_400.basis :=
  SemigroupBasis.CoRoots.S5_400.catalogueS5_840BasisFor_of_publishedCompleteness
    complete

theorem oppositeBasisFor_of_publishedCompleteness
    (complete :
      SemigroupBasis.CoRoots.S5_400.M19CompletenessObligation) :
    BasisFor Generated.Catalogue.S5_840.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_400.oppositeBasis := by
    simpa [SemigroupBasis.CoRoots.S5_400.oppositeBasis] using
      (representativeBasisFor_of_publishedCompleteness complete).oppositeReversed

/-- Unconditional catalogue endpoint from Edmunds' canonical-form proof. -/
theorem representativeBasisFor :
    BasisFor Generated.Catalogue.S5_840.table.semigroup
      SemigroupBasis.CoRoots.S5_400.basis :=
  representativeBasisFor_of_publishedCompleteness
    SemigroupBasis.CoRoots.S5_400.m19Completeness

/-- The self-dual opposite endpoint, retaining the reversed basis. -/
theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_840.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_400.oppositeBasis :=
  oppositeBasisFor_of_publishedCompleteness
    SemigroupBasis.CoRoots.S5_400.m19Completeness

end S5_840

/-- Historical compatibility record for the two formal completeness
propositions corresponding to Edmunds Proposition 3.1(i). Both propositions
are now proved by `m6Completeness` and `m19Completeness`. -/
structure EdmundsProposition31iFormalizationObligations : Prop where
  m6 : SemigroupBasis.CoRoots.S5_400.M6CompletenessObligation
  m19 : SemigroupBasis.CoRoots.S5_400.M19CompletenessObligation

/-- Aggregate type for the four canonical representative/opposite endpoints.
The unconditional component theorems above inhabit every field; the explicit
constructor below is retained as the legacy conditional API. -/
structure FamilyBasisEndpoints : Prop where
  s5_400 :
    BasisFor Generated.Catalogue.S5_400.table.semigroup
      SemigroupBasis.CoRoots.S5_400.basis
  s5_400_opposite :
    BasisFor Generated.Catalogue.S5_400.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_400.oppositeBasis
  s5_840 :
    BasisFor Generated.Catalogue.S5_840.table.semigroup
      SemigroupBasis.CoRoots.S5_400.basis
  s5_840_opposite :
    BasisFor Generated.Catalogue.S5_840.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_400.oppositeBasis

/-- Legacy constructor retained for callers that provide the historical
obligation bundle explicitly. The unconditional endpoints do not use it. -/
theorem endpoints_of_formalizationObligations
    (complete : EdmundsProposition31iFormalizationObligations) :
    FamilyBasisEndpoints where
  s5_400 :=
    S5_400.representativeBasisFor_of_publishedCompleteness complete.m6
  s5_400_opposite :=
    S5_400.oppositeBasisFor_of_publishedCompleteness complete.m6
  s5_840 :=
    S5_840.representativeBasisFor_of_publishedCompleteness complete.m19
  s5_840_opposite :=
    S5_840.oppositeBasisFor_of_publishedCompleteness complete.m19

end SemigroupBasis.Generated.S5_400PublishedRoots

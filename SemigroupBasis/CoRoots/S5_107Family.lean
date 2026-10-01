import SemigroupBasis.CoRoots.S5_107
import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_107Family

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107

private def swapTwoThree (a : Fin 5) : Fin 5 :=
  if a.val = 2 then ⟨3, by decide⟩ else
    if a.val = 3 then ⟨2, by decide⟩ else a

namespace S5_107

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_107.table.semigroup basis :=
  modelsOfFiniteChecks Generated.Catalogue.S5_107.table (by decide)

theorem oppositeModels :
    Models Generated.Catalogue.S5_107.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

def selfDualEmbedding :
    Embedding Generated.Catalogue.S5_107.table.semigroup.opposite
      Generated.Catalogue.S5_107.table.semigroup where
  toFun := swapTwoThree
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem selfDualInvolution (a : Fin 5) :
    selfDualEmbedding.toFun (selfDualEmbedding.toFun a) = a := by
  revert a
  decide

end S5_107

namespace S5_108

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_108.table.semigroup basis :=
  modelsOfFiniteChecks Generated.Catalogue.S5_108.table (by decide)

theorem oppositeModels :
    Models Generated.Catalogue.S5_108.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

end S5_108

namespace S5_109

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_109.table.semigroup basis :=
  modelsOfFiniteChecks Generated.Catalogue.S5_109.table (by decide)

theorem oppositeModels :
    Models Generated.Catalogue.S5_109.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

def selfDualEmbedding :
    Embedding Generated.Catalogue.S5_109.table.semigroup.opposite
      Generated.Catalogue.S5_109.table.semigroup where
  toFun := swapTwoThree
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem selfDualInvolution (a : Fin 5) :
    selfDualEmbedding.toFun (selfDualEmbedding.toFun a) = a := by
  revert a
  decide

end S5_109

end SemigroupBasis.CoRoots.S5_107Family

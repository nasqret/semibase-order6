import SemigroupBasis.Examples.RectangularBandFour
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S4_123

open SemigroupBasis
open SemigroupBasis.Examples

/-- The exact Smallsemi catalogue representative `S4_123`. -/
abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S4_123.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_123.table := rfl

/-- The promoted exact basis `x = xx`, `x = xyx`. -/
abbrev basis : List (Identity Nat) :=
  rectangularBandBasis

theorem representative_models :
    Models table.semigroup basis :=
  rectangularBandFourBasis_models

theorem basis_complete :
    BasisFor table.semigroup basis :=
  rectangularBandFourBasis_complete

theorem representative_basis :
    BasisFor table.semigroup basis :=
  basis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite basis :=
  rectangularBandFourOppositeBasis_complete

/-- Swap the row and column coordinates of the `2 x 2` rectangular band.
In one-based catalogue notation this is `[1,3,2,4]`. -/
def selfDualRelabel (a : Fin 4) : Fin 4 :=
  if a = 0 then 0
  else if a = 1 then 2
  else if a = 2 then 1
  else 3

def selfDualEmbedding :
    Embedding table.semigroup.opposite table.semigroup where
  toFun := selfDualRelabel
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equal
    revert left right
    decide

theorem selfDualRelabel_involution (a : Fin 4) :
    selfDualRelabel (selfDualRelabel a) = a := by
  apply Fin.ext
  revert a
  decide

theorem selfDualEmbedding_surjective :
    Function.Surjective selfDualEmbedding.toFun := by
  intro a
  exact ⟨selfDualRelabel a, selfDualRelabel_involution a⟩

/-- The same exact basis in the explicit self-dual orientation. -/
theorem self_dual_basis :
    BasisFor table.semigroup.opposite basis :=
  opposite_basis

end SemigroupBasis.CoRoots.S4_123

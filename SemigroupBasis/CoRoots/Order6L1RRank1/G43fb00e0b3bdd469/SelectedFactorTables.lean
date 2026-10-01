import SemigroupBasis.CoRoots.Order6L1RRank1.Common
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Generated.S4_64

/-!
# Route-local selected factor tables for G43

This isolated route exports only the exact `FactorTables` names required by
the `S4_116op x S4_64` factor pair.
-/

namespace SemigroupBasis.CoRoots.Order6L1RRank1.FactorTables

open SemigroupBasis

/-- Reverse an exact finite table's multiplication. -/
def oppositeTable (table : FiniteTable) : FiniteTable where
  order := table.order
  mul := fun left right => table.mul right left
  assoc := fun left middle right =>
    (table.assoc right middle left).symm

theorem oppositeTable_semigroup (table : FiniteTable) :
    (oppositeTable table).semigroup = table.semigroup.opposite := by
  rfl

abbrev s4_64 : FiniteTable :=
  SemigroupBasis.Generated.S4_64.table

abbrev s4_116 : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S4_116.table

def s4_116op : FiniteTable :=
  oppositeTable s4_116

theorem s4_116op_semigroup :
    s4_116op.semigroup = s4_116.semigroup.opposite :=
  oppositeTable_semigroup s4_116

end SemigroupBasis.CoRoots.Order6L1RRank1.FactorTables

import SemigroupBasis.CoRoots.Order6Astra.C8Completeness
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.Order6Astra.C8Catalogue

/-- Literal zero-based table for GAP Smallsemi [6,3842], catalogue S6_3842.
The source rows are independently repeated in the original endpoint audit. -/
abbrev table : FiniteTable := Order6SporadicSection19.table
abbrev basis : List (Identity Nat) := Order6SporadicSection19.Published.basis

theorem literal_rows :
    (List.finRange 6).map (fun (a : Fin 6) =>
      (List.finRange 6).map (fun (b : Fin 6) => (show Fin 6 from table.mul a b).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,0,1], [0,0,0,0,0,2],
       [0,0,1,0,3,0], [0,0,2,0,4,0], [0,1,1,3,3,5]] := by decide

theorem published_law_count : basis.length = 38 := by decide

theorem basisFor3842 : BasisFor table.semigroup basis := C8Completeness.basisFor

theorem basisFor3842_opposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor3842.oppositeReversed

end SemigroupBasis.CoRoots.Order6Astra.C8Catalogue

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8Catalogue.literal_rows
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8Catalogue.basisFor3842
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8Catalogue.basisFor3842_opposite

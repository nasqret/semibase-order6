import SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite

/-! S2's three exact finite observation controls for the literal S6_9726 table.
The quantified domains contain six, four and four values respectively. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.RecursiveObservationFinite

open SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726

theorem zeroLeftControl (value : Fin 6) : mul 0 value = 0 := by
  decide +revert

theorem nilStepControl (n : Fin 4) :
    mul (if n.val = 0 then (5 : Fin 6) else if n.val = 1 then 2 else if n.val = 2 then 1 else 0) 2 =
      (if n.val = 0 then (2 : Fin 6) else if n.val = 1 then 1 else 0) := by
  decide +revert

theorem markerStepControl (n : Fin 4) :
    mul (if n.val = 0 then (5 : Fin 6) else if n.val = 1 then 2 else if n.val = 2 then 1 else 0) 4 =
      (if n.val = 0 then (4 : Fin 6) else if n.val = 1 then 3 else 0) := by
  decide +revert

end SemigroupBasis.CoRoots.Order6Sunday.RecursiveObservationFinite

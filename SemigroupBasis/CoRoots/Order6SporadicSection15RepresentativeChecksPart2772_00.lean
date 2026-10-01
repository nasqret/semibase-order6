import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart00

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,3],[1,1,2,1,1,1],[1,1,1,1,2,5],[1,2,2,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 0
  | 1, 5 => 1
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 2
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 2 => 1
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 0
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 1
  | 4, 5 => 4
  | 5, 0 => 0
  | 5, 1 => 1
  | 5, 2 => 1
  | 5, 3 => 3
  | 5, 4 => 4
  | 5, 5 => 5
  | _, _ => 0

private theorem mulAssociative :
    ∀ a b c, mul (mul a b) c = mul a (mul b c) :=
  associative_of_checkAssociative6 mul (by decide)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := mulAssociative

def tableSHA256 : String :=
  "a30bec68e32c30c2a5490b53d226ddcbbc3fc3fdfd63c1bee5d39458ea16287b"

namespace Checks

def defaultValue : Fin table.order :=
  ⟨0, by decide⟩

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom56 :
    (finiteBasis.drop 56).all
      (checkIdentityOnSupport table defaultValue) = true := by
  decide

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15


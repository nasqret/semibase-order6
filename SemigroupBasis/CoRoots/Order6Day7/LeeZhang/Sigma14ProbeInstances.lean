import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14ProbeModel

/-! Six concrete instances on the authenticated literal class tables.
Every interface field is proved by ordinary finite kernel reduction.
No Python screen, unproved separator field, or abstract replacement model
is used as a proof premise. Approval: msg-0424, both exact Sigma14 lists. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14

open SemigroupBasis

def capMap (nilpotent : Fin 6) (value : Fin 3) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then nilpotent else 5

def capEmbedding2636 : Embedding Examples.commutativeExponentThree.semigroup table2636.semigroup where
  toFun := capMap 3
  map_mul := by decide
  injective := by unfold Function.Injective; decide

def probe2636 : ProbeModel table2636.semigroup true where
  capEmbedding := capEmbedding2636
  simpleMarker := 4
  driftMarker := 3
  pairLast := 2
  pairMark := 4
  pairMiddle := 0
  mul_zero := by decide
  neutral_one := by decide
  mark_one := by decide
  neutral_simple := by decide
  mark_simple := by decide
  neutral_drift := by decide
  mark_drift := by decide
  neutral_neutral := by decide
  mark_neutral := by decide
  neutral_mark := by decide
  mark_mark := by decide
  simple_ne_zero := by decide
  simple_ne_one := by decide
  simple_ne_neutral := by decide
  drift_ne_simple := by decide
  drift_ne_one := by decide
  pair_neutral_last := by decide
  pair_mark_last := by decide
  pair_neutral_middle := by decide
  pair_mark_middle := by decide
  pair_mark_one := by decide

def capEmbedding2637 : Embedding Examples.commutativeExponentThree.semigroup table2637.semigroup where
  toFun := capMap 3
  map_mul := by decide
  injective := by unfold Function.Injective; decide

def probe2637 : ProbeModel table2637.semigroup true where
  capEmbedding := capEmbedding2637
  simpleMarker := 4
  driftMarker := 3
  pairLast := 2
  pairMark := 4
  pairMiddle := 1
  mul_zero := by decide
  neutral_one := by decide
  mark_one := by decide
  neutral_simple := by decide
  mark_simple := by decide
  neutral_drift := by decide
  mark_drift := by decide
  neutral_neutral := by decide
  mark_neutral := by decide
  neutral_mark := by decide
  mark_mark := by decide
  simple_ne_zero := by decide
  simple_ne_one := by decide
  simple_ne_neutral := by decide
  drift_ne_simple := by decide
  drift_ne_one := by decide
  pair_neutral_last := by decide
  pair_mark_last := by decide
  pair_neutral_middle := by decide
  pair_mark_middle := by decide
  pair_mark_one := by decide

def capEmbedding2705 : Embedding Examples.commutativeExponentThree.semigroup table2705.semigroup where
  toFun := capMap 2
  map_mul := by decide
  injective := by unfold Function.Injective; decide

def probe2705 : ProbeModel table2705.semigroup true where
  capEmbedding := capEmbedding2705
  simpleMarker := 4
  driftMarker := 2
  pairLast := 3
  pairMark := 4
  pairMiddle := 2
  mul_zero := by decide
  neutral_one := by decide
  mark_one := by decide
  neutral_simple := by decide
  mark_simple := by decide
  neutral_drift := by decide
  mark_drift := by decide
  neutral_neutral := by decide
  mark_neutral := by decide
  neutral_mark := by decide
  mark_mark := by decide
  simple_ne_zero := by decide
  simple_ne_one := by decide
  simple_ne_neutral := by decide
  drift_ne_simple := by decide
  drift_ne_one := by decide
  pair_neutral_last := by decide
  pair_mark_last := by decide
  pair_neutral_middle := by decide
  pair_mark_middle := by decide
  pair_mark_one := by decide

def capEmbedding2676 : Embedding Examples.commutativeExponentThree.semigroup table2676.semigroup where
  toFun := capMap 2
  map_mul := by decide
  injective := by unfold Function.Injective; decide

def probe2676 : ProbeModel table2676.semigroup false where
  capEmbedding := capEmbedding2676
  simpleMarker := 3
  driftMarker := 0
  pairLast := 4
  pairMark := 3
  pairMiddle := 3
  mul_zero := by decide
  neutral_one := by decide
  mark_one := by decide
  neutral_simple := by decide
  mark_simple := by decide
  neutral_drift := by decide
  mark_drift := by decide
  neutral_neutral := by decide
  mark_neutral := by decide
  neutral_mark := by decide
  mark_mark := by decide
  simple_ne_zero := by decide
  simple_ne_one := by decide
  simple_ne_neutral := by decide
  drift_ne_simple := by decide
  drift_ne_one := by decide
  pair_neutral_last := by decide
  pair_mark_last := by decide
  pair_neutral_middle := by decide
  pair_mark_middle := by decide
  pair_mark_one := by decide

def capEmbedding2680 : Embedding Examples.commutativeExponentThree.semigroup table2680.semigroup where
  toFun := capMap 2
  map_mul := by decide
  injective := by unfold Function.Injective; decide

def probe2680 : ProbeModel table2680.semigroup false where
  capEmbedding := capEmbedding2680
  simpleMarker := 3
  driftMarker := 2
  pairLast := 4
  pairMark := 3
  pairMiddle := 3
  mul_zero := by decide
  neutral_one := by decide
  mark_one := by decide
  neutral_simple := by decide
  mark_simple := by decide
  neutral_drift := by decide
  mark_drift := by decide
  neutral_neutral := by decide
  mark_neutral := by decide
  neutral_mark := by decide
  mark_mark := by decide
  simple_ne_zero := by decide
  simple_ne_one := by decide
  simple_ne_neutral := by decide
  drift_ne_simple := by decide
  drift_ne_one := by decide
  pair_neutral_last := by decide
  pair_mark_last := by decide
  pair_neutral_middle := by decide
  pair_mark_middle := by decide
  pair_mark_one := by decide

def capEmbedding2702 : Embedding Examples.commutativeExponentThree.semigroup table2702.semigroup where
  toFun := capMap 3
  map_mul := by decide
  injective := by unfold Function.Injective; decide

def probe2702 : ProbeModel table2702.semigroup false where
  capEmbedding := capEmbedding2702
  simpleMarker := 2
  driftMarker := 0
  pairLast := 4
  pairMark := 2
  pairMiddle := 2
  mul_zero := by decide
  neutral_one := by decide
  mark_one := by decide
  neutral_simple := by decide
  mark_simple := by decide
  neutral_drift := by decide
  mark_drift := by decide
  neutral_neutral := by decide
  mark_neutral := by decide
  neutral_mark := by decide
  mark_mark := by decide
  simple_ne_zero := by decide
  simple_ne_one := by decide
  simple_ne_neutral := by decide
  drift_ne_simple := by decide
  drift_ne_one := by decide
  pair_neutral_last := by decide
  pair_mark_last := by decide
  pair_neutral_middle := by decide
  pair_mark_middle := by decide
  pair_mark_one := by decide

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14

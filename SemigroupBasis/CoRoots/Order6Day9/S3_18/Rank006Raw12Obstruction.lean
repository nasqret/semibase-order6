import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Shape

/-!
# Rank006 raw12 incompleteness: an explicit seven-state countermodel

States are zero, a, b, ab, ba, aba, bab.  Concatenation is zero when it
has length at least four or contains aa or bb.  Thus every square is zero
and every product of four factors is zero.  All twelve raw laws hold, but
aba = aaaaba fails.  The latter identity is valid in BOTH actual Rank006
factors.  This is a mathematical countermodel, not an order-six class
subdirect witness; S3's finite-witness ownership is unchanged.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Raw12Obstruction

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Shape

/-- Zero-based states [0, a, b, ab, ba, aba, bab]. -/
def counterMul (first second : Fin 7) : Fin 7 :=
  if first = 1 then
    if second = 2 then 3 else if second = 4 then 5 else 0
  else if first = 2 then
    if second = 1 then 4 else if second = 3 then 6 else 0
  else if first = 3 then
    if second = 1 then 5 else 0
  else if first = 4 then
    if second = 2 then 6 else 0
  else 0

def counterTable : FiniteTable where
  order := 7
  mul := counterMul
  assoc := by decide

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem counterTable_models_raw12 : Models counterTable.semigroup basis :=
  FiniteCertificate.checkModels_sound counterTable basis toFinThree (by decide)

/-- The second historical bounded bridge, with variables a=0 and b=1. -/
def missingLaw : Identity Nat :=
  ⟨Word.mk 0 [1, 0], Word.mk 0 [0, 0, 0, 1, 0]⟩

theorem missingLaw_leftValid : missingLaw.SatisfiedBy leftTable.semigroup := by
  have checked : Models leftTable.semigroup [missingLaw] :=
    FiniteCertificate.checkModels_sound leftTable [missingLaw] toFinThree (by decide)
  exact checked missingLaw (by decide)

theorem missingLaw_rightValid : missingLaw.SatisfiedBy rightTable.semigroup := by
  have checked : Models rightTable.semigroup [missingLaw] :=
    FiniteCertificate.checkModels_sound rightTable [missingLaw] toFinThree (by decide)
  exact checked missingLaw (by decide)

def counterValuation (letter : Nat) : Fin 7 :=
  if letter = 0 then 1 else if letter = 1 then 2 else 0

theorem counterEval_left :
    counterTable.semigroup.eval counterValuation missingLaw.lhs = (5 : Fin 7) := by
  decide

theorem counterEval_right :
    counterTable.semigroup.eval counterValuation missingLaw.rhs = (0 : Fin 7) := by
  decide

theorem missingLaw_counterInvalid :
    ¬ missingLaw.SatisfiedBy counterTable.semigroup := by
  intro valid
  have impossible : (5 : Fin 7) = 0 := by
    simpa only [counterEval_left, counterEval_right] using valid counterValuation
  exact (by decide : (5 : Fin 7) ≠ 0) impossible

/-- Unrestricted nonderivability, certified by soundness in an actual model. -/
theorem missingLaw_not_derives :
    ¬ Derives basis missingLaw.lhs missingLaw.rhs := by
  intro derivation
  exact missingLaw_counterInvalid (derivation.sound counterTable_models_raw12)

/-- The exact original twelve-law intersection is NOT complete. -/
theorem raw12_not_complete : ¬ Complete := by
  intro complete
  exact missingLaw_not_derives
    (complete missingLaw missingLaw_leftValid missingLaw_rightValid)

theorem raw12_no_intersectionBasis :
    ¬ IntersectionBasis leftTable.semigroup rightTable.semigroup basis := by
  intro intersection
  exact raw12_not_complete intersection.complete

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Raw12Obstruction

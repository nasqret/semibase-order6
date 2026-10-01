import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0428LinearObstruction
import SemigroupBasis.CoRoots.Order6Day7.S2_4.SeedS5_207
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.Generated.S3_15

/-! The exact corrected packages approved by msg0430 and reaffirmed by msg0432.
The withdrawn lists are extended by the ONE approved linear identity. Literal
class tables are reused without relabelling. Actual historical quotient maps
are separately proved split and jointly injective; none of the historical
bounded-completeness labels is imported as a proof premise. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0430

open SemigroupBasis

abbrev table2683 := Msg0428LinearObstruction.table2683
abbrev table2706 := Msg0428LinearObstruction.table2706
abbrev table5603 := Msg0428LinearObstruction.table5603
abbrev linearLaw := Msg0428LinearObstruction.missingIdentity

def pairBasis : List (Identity Nat) := Msg0428LinearObstruction.pairBasis ++ [linearLaw]
def singletonBasis : List (Identity Nat) := Msg0428LinearObstruction.singletonBasis ++ [linearLaw]

def pairBasisSHA256 : String :=
  "6b05a2c03e24db4c922e76aa7310527edb265188d9b1766391d3daf22a0cf0f2"
def singletonBasisSHA256 : String :=
  "be4cc9653b64095ba83744d27d7d7eb72aa5e388e2e59232d14c9eb91e8697a7"

theorem pair_basis_length : pairBasis.length = 8 := rfl
theorem singleton_basis_length : singletonBasis.length = 6 := rfl

theorem models2683 : Models table2683.semigroup pairBasis := by
  intro identity member
  rcases List.mem_append.mp member with old | added
  · exact Msg0428LinearObstruction.models2683 identity old
  · have equal : identity = linearLaw := List.mem_singleton.mp added
    subst identity
    exact Msg0428LinearObstruction.missing_identity_valid2683

theorem models2706 : Models table2706.semigroup pairBasis := by
  intro identity member
  rcases List.mem_append.mp member with old | added
  · exact Msg0428LinearObstruction.models2706 identity old
  · have equal : identity = linearLaw := List.mem_singleton.mp added
    subst identity
    exact Msg0428LinearObstruction.missing_identity_valid2706

theorem models5603 : Models table5603.semigroup singletonBasis := by
  intro identity member
  rcases List.mem_append.mp member with old | added
  · exact Msg0428LinearObstruction.models5603 identity old
  · have equal : identity = linearLaw := List.mem_singleton.mp added
    subst identity
    exact Msg0428LinearObstruction.missing_identity_valid5603

abbrev pairLeft : FiniteTable := Order6Subdirect.oppositeTable Generated.S3_6.table
abbrev singletonLeft : FiniteTable := Generated.S3_15.table
abbrev rightTable : FiniteTable := SemigroupBasis.CoRoots.S5_207.table

def leftMap2683 (value : Fin 6) : Fin 3 := if value = 2 then 1 else if value = 5 then 2 else 0
def leftMap2706 (value : Fin 6) : Fin 3 := if value = 3 then 1 else if value = 5 then 2 else 0
def leftMap5603 (value : Fin 6) : Fin 3 := if value = 4 then 1 else if value = 5 then 2 else 0
def rightMap2683 (value : Fin 6) : Fin 5 :=
  if value = 1 then 1 else if value = 3 then 2 else if value = 4 then 3 else if value = 5 then 4 else 0
def rightMap2706 (value : Fin 6) : Fin 5 :=
  if value = 1 then 1 else if value = 2 ∨ value = 3 then 2 else if value = 4 then 3 else if value = 5 then 4 else 0
def rightMap5603 (value : Fin 6) : Fin 5 :=
  if value = 0 then 0 else if value = 1 then 1 else if value = 2 then 2 else if value = 3 then 3 else 4

def leftSection (marker : Fin 6) (value : Fin 3) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then marker else 5
def rightSectionPair (marker : Fin 6) (value : Fin 5) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 1 else if value = 2 then marker else if value = 3 then 4 else 5
def rightSection5603 (value : Fin 5) : Fin 6 := ⟨value.val, by omega⟩

def left2683 : SplitSurjection table2683.semigroup pairLeft.semigroup where
  toFun := leftMap2683
  map_mul := by decide
  preimage := leftSection 2
  right_inverse := by decide

def left2706 : SplitSurjection table2706.semigroup pairLeft.semigroup where
  toFun := leftMap2706
  map_mul := by decide
  preimage := leftSection 3
  right_inverse := by decide

def left5603 : SplitSurjection table5603.semigroup singletonLeft.semigroup where
  toFun := leftMap5603
  map_mul := by decide
  preimage := leftSection 4
  right_inverse := by decide

def right2683 : SplitSurjection table2683.semigroup rightTable.semigroup where
  toFun := rightMap2683
  map_mul := by decide
  preimage := rightSectionPair 3
  right_inverse := by decide

def right2706 : SplitSurjection table2706.semigroup rightTable.semigroup where
  toFun := rightMap2706
  map_mul := by decide
  preimage := rightSectionPair 2
  right_inverse := by decide

def right5603 : SplitSurjection table5603.semigroup rightTable.semigroup where
  toFun := rightMap5603
  map_mul := by decide
  preimage := rightSection5603
  right_inverse := by decide

def subdirect2683 : SubdirectPair table2683.semigroup pairLeft.semigroup rightTable.semigroup where
  left := left2683
  right := right2683
  jointlyInjective := by unfold Function.Injective; decide

def subdirect2706 : SubdirectPair table2706.semigroup pairLeft.semigroup rightTable.semigroup where
  left := left2706
  right := right2706
  jointlyInjective := by unfold Function.Injective; decide

def subdirect5603 : SubdirectPair table5603.semigroup singletonLeft.semigroup rightTable.semigroup where
  left := left5603
  right := right5603
  jointlyInjective := by unfold Function.Injective; decide

theorem pairLeftModels : Models pairLeft.semigroup pairBasis :=
  fun identity member => left2683.pushforwardIdentity identity (models2683 identity member)
theorem pairRightModels : Models rightTable.semigroup pairBasis :=
  fun identity member => right2683.pushforwardIdentity identity (models2683 identity member)
theorem singletonLeftModels : Models singletonLeft.semigroup singletonBasis :=
  fun identity member => left5603.pushforwardIdentity identity (models5603 identity member)
theorem singletonRightModels : Models rightTable.semigroup singletonBasis :=
  fun identity member => right5603.pushforwardIdentity identity (models5603 identity member)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0430

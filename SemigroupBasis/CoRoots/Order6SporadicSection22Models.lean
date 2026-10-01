import SemigroupBasis.CoRoots.Order6SporadicSection22Basis
import SemigroupBasis.CoRoots.Order6SporadicSection22Tables

/-! Closed, typed finite checks for every expanded published law.
The proved fused checker transfers finite-variable validity to Nat.
This establishes soundness, not the remaining completeness obligations. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6SporadicSection22
open SemigroupBasis

namespace E5
namespace FiniteChecks

def finitePower : Identity (Fin 1) := ⟨⟨0, [0, 0]⟩, ⟨0, [0]⟩⟩
def decodePower (_ : Fin 1) : Nat := 0
theorem roundTripPower : finitePower.map decodePower = lawPower := by decide

def finiteLeft : Identity (Fin 2) := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def decodeLeft (a : Fin 2) : Nat := if a = 0 then 0 else 1
theorem roundTripLeft : finiteLeft.map decodeLeft = lawLeft := by decide

def finiteRight : Identity (Fin 2) := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def decodeRight (a : Fin 2) : Nat := if a = 0 then 0 else 1
theorem roundTripRight : finiteRight.map decodeRight = lawRight := by decide

def finiteMove : Identity (Fin 3) := ⟨⟨2, [2, 0, 1, 0]⟩, ⟨2, [2, 1, 0, 0]⟩⟩
def decodeMove (a : Fin 3) : Nat := if a = 0 then 0 else if a = 1 then 1 else 2
theorem roundTripMove : finiteMove.map decodeMove = lawMove := by decide

def finiteSwap : Identity (Fin 3) := ⟨⟨2, [2, 0, 0, 1, 1]⟩, ⟨2, [2, 1, 1, 0, 0]⟩⟩
def decodeSwap (a : Fin 3) : Nat := if a = 0 then 0 else if a = 1 then 1 else 2
theorem roundTripSwap : finiteSwap.map decodeSwap = lawSwap := by decide

end FiniteChecks
open FiniteChecks

theorem modelsPower : lawPower.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finitePower = true := by decide
  have valid := table.checkIdentityFused_sound finitePower checked
  have mapped := finitePower.satisfiedBy_map decodePower table.semigroup valid
  rw [roundTripPower] at mapped
  exact mapped

theorem modelsLeft : lawLeft.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteLeft = true := by decide
  have valid := table.checkIdentityFused_sound finiteLeft checked
  have mapped := finiteLeft.satisfiedBy_map decodeLeft table.semigroup valid
  rw [roundTripLeft] at mapped
  exact mapped

theorem modelsRight : lawRight.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteRight = true := by decide
  have valid := table.checkIdentityFused_sound finiteRight checked
  have mapped := finiteRight.satisfiedBy_map decodeRight table.semigroup valid
  rw [roundTripRight] at mapped
  exact mapped

theorem modelsMove : lawMove.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteMove = true := by decide
  have valid := table.checkIdentityFused_sound finiteMove checked
  have mapped := finiteMove.satisfiedBy_map decodeMove table.semigroup valid
  rw [roundTripMove] at mapped
  exact mapped

theorem modelsSwap : lawSwap.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwap = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwap checked
  have mapped := finiteSwap.satisfiedBy_map decodeSwap table.semigroup valid
  rw [roundTripSwap] at mapped
  exact mapped

theorem models : Models table.semigroup basis := by
  intro law member
  simp only [basis,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact modelsPower
  · exact modelsLeft
  · exact modelsRight
  · exact modelsMove
  · exact modelsSwap

#print axioms models
end E5

namespace E7
namespace FiniteChecks

def finitePower : Identity (Fin 1) := ⟨⟨0, [0, 0]⟩, ⟨0, [0]⟩⟩
def decodePower (_ : Fin 1) : Nat := 0
theorem roundTripPower : finitePower.map decodePower = lawPower := by decide

def finitePowerH : Identity (Fin 2) := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def decodePowerH (a : Fin 2) : Nat := if a = 0 then 0 else 2
theorem roundTripPowerH : finitePowerH.map decodePowerH = lawPowerH := by decide

def finiteDelete : Identity (Fin 2) := ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1]⟩⟩
def decodeDelete (a : Fin 2) : Nat := if a = 0 then 0 else 1
theorem roundTripDelete : finiteDelete.map decodeDelete = lawDelete := by decide

def finiteDeleteK : Identity (Fin 3) := ⟨⟨0, [1, 2, 0, 1]⟩, ⟨0, [1, 2, 1]⟩⟩
def decodeDeleteK (a : Fin 3) : Nat := if a = 0 then 0 else if a = 1 then 1 else 3
theorem roundTripDeleteK : finiteDeleteK.map decodeDeleteK = lawDeleteK := by decide

def finiteDeleteH : Identity (Fin 3) := ⟨⟨0, [2, 1, 0, 1]⟩, ⟨0, [2, 1, 1]⟩⟩
def decodeDeleteH (a : Fin 3) : Nat := if a = 0 then 0 else if a = 1 then 1 else 2
theorem roundTripDeleteH : finiteDeleteH.map decodeDeleteH = lawDeleteH := by decide

def finiteDeleteHK : Identity (Fin 4) := ⟨⟨0, [2, 1, 3, 0, 1]⟩, ⟨0, [2, 1, 3, 1]⟩⟩
def decodeDeleteHK (a : Fin 4) : Nat := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else 3
theorem roundTripDeleteHK : finiteDeleteHK.map decodeDeleteHK = lawDeleteHK := by decide

def finiteReverse : Identity (Fin 2) := ⟨⟨0, [1, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def decodeReverse (a : Fin 2) : Nat := if a = 0 then 0 else 1
theorem roundTripReverse : finiteReverse.map decodeReverse = lawReverse := by decide

def finiteReverseK : Identity (Fin 3) := ⟨⟨0, [1, 2, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩
def decodeReverseK (a : Fin 3) : Nat := if a = 0 then 0 else if a = 1 then 1 else 3
theorem roundTripReverseK : finiteReverseK.map decodeReverseK = lawReverseK := by decide

def finiteReverseH : Identity (Fin 3) := ⟨⟨0, [2, 1, 1, 0]⟩, ⟨0, [2, 1, 0]⟩⟩
def decodeReverseH (a : Fin 3) : Nat := if a = 0 then 0 else if a = 1 then 1 else 2
theorem roundTripReverseH : finiteReverseH.map decodeReverseH = lawReverseH := by decide

def finiteReverseHK : Identity (Fin 4) := ⟨⟨0, [2, 1, 3, 1, 0]⟩, ⟨0, [2, 1, 3, 0]⟩⟩
def decodeReverseHK (a : Fin 4) : Nat := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else 3
theorem roundTripReverseHK : finiteReverseHK.map decodeReverseHK = lawReverseHK := by decide

end FiniteChecks
open FiniteChecks

theorem modelsPower : lawPower.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finitePower = true := by decide
  have valid := table.checkIdentityFused_sound finitePower checked
  have mapped := finitePower.satisfiedBy_map decodePower table.semigroup valid
  rw [roundTripPower] at mapped
  exact mapped

theorem modelsPowerH : lawPowerH.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finitePowerH = true := by decide
  have valid := table.checkIdentityFused_sound finitePowerH checked
  have mapped := finitePowerH.satisfiedBy_map decodePowerH table.semigroup valid
  rw [roundTripPowerH] at mapped
  exact mapped

theorem modelsDelete : lawDelete.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteDelete = true := by decide
  have valid := table.checkIdentityFused_sound finiteDelete checked
  have mapped := finiteDelete.satisfiedBy_map decodeDelete table.semigroup valid
  rw [roundTripDelete] at mapped
  exact mapped

theorem modelsDeleteK : lawDeleteK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteDeleteK = true := by decide
  have valid := table.checkIdentityFused_sound finiteDeleteK checked
  have mapped := finiteDeleteK.satisfiedBy_map decodeDeleteK table.semigroup valid
  rw [roundTripDeleteK] at mapped
  exact mapped

theorem modelsDeleteH : lawDeleteH.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteDeleteH = true := by decide
  have valid := table.checkIdentityFused_sound finiteDeleteH checked
  have mapped := finiteDeleteH.satisfiedBy_map decodeDeleteH table.semigroup valid
  rw [roundTripDeleteH] at mapped
  exact mapped

theorem modelsDeleteHK : lawDeleteHK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteDeleteHK = true := by decide
  have valid := table.checkIdentityFused_sound finiteDeleteHK checked
  have mapped := finiteDeleteHK.satisfiedBy_map decodeDeleteHK table.semigroup valid
  rw [roundTripDeleteHK] at mapped
  exact mapped

theorem modelsReverse : lawReverse.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteReverse = true := by decide
  have valid := table.checkIdentityFused_sound finiteReverse checked
  have mapped := finiteReverse.satisfiedBy_map decodeReverse table.semigroup valid
  rw [roundTripReverse] at mapped
  exact mapped

theorem modelsReverseK : lawReverseK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteReverseK = true := by decide
  have valid := table.checkIdentityFused_sound finiteReverseK checked
  have mapped := finiteReverseK.satisfiedBy_map decodeReverseK table.semigroup valid
  rw [roundTripReverseK] at mapped
  exact mapped

theorem modelsReverseH : lawReverseH.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteReverseH = true := by decide
  have valid := table.checkIdentityFused_sound finiteReverseH checked
  have mapped := finiteReverseH.satisfiedBy_map decodeReverseH table.semigroup valid
  rw [roundTripReverseH] at mapped
  exact mapped

theorem modelsReverseHK : lawReverseHK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteReverseHK = true := by decide
  have valid := table.checkIdentityFused_sound finiteReverseHK checked
  have mapped := finiteReverseHK.satisfiedBy_map decodeReverseHK table.semigroup valid
  rw [roundTripReverseHK] at mapped
  exact mapped

theorem models : Models table.semigroup basis := by
  intro law member
  simp only [basis,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact modelsPower
  · exact modelsPowerH
  · exact modelsDelete
  · exact modelsDeleteK
  · exact modelsDeleteH
  · exact modelsDeleteHK
  · exact modelsReverse
  · exact modelsReverseK
  · exact modelsReverseH
  · exact modelsReverseHK

#print axioms models
end E7

end SemigroupBasis.CoRoots.Order6SporadicSection22

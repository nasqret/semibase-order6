import SemigroupBasis.CoRoots.Order6SporadicSection16Tables
import SemigroupBasis.CoRoots.Order6SporadicSection16Basis

/-! Exact finite Models checks for the unchanged ten-law Section16 basis.
Each law uses its own finite variable set, so the total is2310 assignments
per table. Closed decide plus the proved fused-checker soundness theorem;
no native evaluation or bounded-to-unrestricted promotion. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis

namespace FiniteChecks

def finitePower : Identity (Fin 1) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0]⟩⟩
def decodePower (a : Fin 1) : Nat := 0
theorem roundTripPower : (finitePower.map decodePower) = lawPower := by decide

def finiteLeft : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def decodeLeft (a : Fin 2) : Nat := if a = 0 then 0 else 1
theorem roundTripLeft : (finiteLeft.map decodeLeft) = lawLeft := by decide

def finiteRight : Identity (Fin 2) :=
  ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def decodeRight (a : Fin 2) : Nat := if a = 0 then 0 else 1
theorem roundTripRight : (finiteRight.map decodeRight) = lawRight := by decide

def finiteCollect : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [0, 1, 2, 2]⟩⟩
def decodeCollect (a : Fin 3) : Nat := if a = 0 then 0 else if a = 1 then 1 else 2
theorem roundTripCollect : (finiteCollect.map decodeCollect) = lawCollect := by decide

def finiteAnchor : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
def decodeAnchor (a : Fin 2) : Nat := if a = 0 then 0 else 1
theorem roundTripAnchor : (finiteAnchor.map decodeAnchor) = lawAnchor := by decide

def finiteAnchorH : Identity (Fin 3) :=
  ⟨⟨0, [0, 2, 1, 1]⟩, ⟨0, [2, 1, 1, 0]⟩⟩
def decodeAnchorH (a : Fin 3) : Nat := if a = 0 then 0 else if a = 1 then 1 else 3
theorem roundTripAnchorH : (finiteAnchorH.map decodeAnchorH) = lawAnchorH := by decide

def finiteSwap : Identity (Fin 2) :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
def decodeSwap (a : Fin 2) : Nat := if a = 0 then 0 else 1
theorem roundTripSwap : (finiteSwap.map decodeSwap) = lawSwap := by decide

def finiteSwapK : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 1]⟩, ⟨0, [1, 2, 1, 0]⟩⟩
def decodeSwapK (a : Fin 3) : Nat := if a = 0 then 0 else if a = 1 then 1 else 4
theorem roundTripSwapK : (finiteSwapK.map decodeSwapK) = lawSwapK := by decide

def finiteSwapH : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0, 1]⟩, ⟨0, [2, 1, 1, 0]⟩⟩
def decodeSwapH (a : Fin 3) : Nat := if a = 0 then 0 else if a = 1 then 1 else 3
theorem roundTripSwapH : (finiteSwapH.map decodeSwapH) = lawSwapH := by decide

def finiteSwapHK : Identity (Fin 4) :=
  ⟨⟨0, [2, 1, 3, 0, 1]⟩, ⟨0, [2, 1, 3, 1, 0]⟩⟩
def decodeSwapHK (a : Fin 4) : Nat := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 3 else 4
theorem roundTripSwapHK : (finiteSwapHK.map decodeSwapHK) = lawSwapHK := by decide

end FiniteChecks

open FiniteChecks


namespace S6_3813

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

theorem modelsCollect : lawCollect.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteCollect = true := by decide
  have valid := table.checkIdentityFused_sound finiteCollect checked
  have mapped := finiteCollect.satisfiedBy_map decodeCollect table.semigroup valid
  rw [roundTripCollect] at mapped
  exact mapped

theorem modelsAnchor : lawAnchor.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteAnchor = true := by decide
  have valid := table.checkIdentityFused_sound finiteAnchor checked
  have mapped := finiteAnchor.satisfiedBy_map decodeAnchor table.semigroup valid
  rw [roundTripAnchor] at mapped
  exact mapped

theorem modelsAnchorH : lawAnchorH.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteAnchorH = true := by decide
  have valid := table.checkIdentityFused_sound finiteAnchorH checked
  have mapped := finiteAnchorH.satisfiedBy_map decodeAnchorH table.semigroup valid
  rw [roundTripAnchorH] at mapped
  exact mapped

theorem modelsSwap : lawSwap.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwap = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwap checked
  have mapped := finiteSwap.satisfiedBy_map decodeSwap table.semigroup valid
  rw [roundTripSwap] at mapped
  exact mapped

theorem modelsSwapK : lawSwapK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapK = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapK checked
  have mapped := finiteSwapK.satisfiedBy_map decodeSwapK table.semigroup valid
  rw [roundTripSwapK] at mapped
  exact mapped

theorem modelsSwapH : lawSwapH.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapH = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapH checked
  have mapped := finiteSwapH.satisfiedBy_map decodeSwapH table.semigroup valid
  rw [roundTripSwapH] at mapped
  exact mapped

theorem modelsSwapHK : lawSwapHK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapHK = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapHK checked
  have mapped := finiteSwapHK.satisfiedBy_map decodeSwapHK table.semigroup valid
  rw [roundTripSwapHK] at mapped
  exact mapped

theorem models_basis : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · exact modelsPower

  · exact modelsLeft

  · exact modelsRight

  · exact modelsCollect

  · exact modelsAnchor

  · exact modelsAnchorH

  · exact modelsSwap

  · exact modelsSwapK

  · exact modelsSwapH

  · exact modelsSwapHK

#print axioms models_basis
end S6_3813


namespace S6_3815

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

theorem modelsCollect : lawCollect.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteCollect = true := by decide
  have valid := table.checkIdentityFused_sound finiteCollect checked
  have mapped := finiteCollect.satisfiedBy_map decodeCollect table.semigroup valid
  rw [roundTripCollect] at mapped
  exact mapped

theorem modelsAnchor : lawAnchor.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteAnchor = true := by decide
  have valid := table.checkIdentityFused_sound finiteAnchor checked
  have mapped := finiteAnchor.satisfiedBy_map decodeAnchor table.semigroup valid
  rw [roundTripAnchor] at mapped
  exact mapped

theorem modelsAnchorH : lawAnchorH.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteAnchorH = true := by decide
  have valid := table.checkIdentityFused_sound finiteAnchorH checked
  have mapped := finiteAnchorH.satisfiedBy_map decodeAnchorH table.semigroup valid
  rw [roundTripAnchorH] at mapped
  exact mapped

theorem modelsSwap : lawSwap.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwap = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwap checked
  have mapped := finiteSwap.satisfiedBy_map decodeSwap table.semigroup valid
  rw [roundTripSwap] at mapped
  exact mapped

theorem modelsSwapK : lawSwapK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapK = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapK checked
  have mapped := finiteSwapK.satisfiedBy_map decodeSwapK table.semigroup valid
  rw [roundTripSwapK] at mapped
  exact mapped

theorem modelsSwapH : lawSwapH.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapH = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapH checked
  have mapped := finiteSwapH.satisfiedBy_map decodeSwapH table.semigroup valid
  rw [roundTripSwapH] at mapped
  exact mapped

theorem modelsSwapHK : lawSwapHK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapHK = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapHK checked
  have mapped := finiteSwapHK.satisfiedBy_map decodeSwapHK table.semigroup valid
  rw [roundTripSwapHK] at mapped
  exact mapped

theorem models_basis : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · exact modelsPower

  · exact modelsLeft

  · exact modelsRight

  · exact modelsCollect

  · exact modelsAnchor

  · exact modelsAnchorH

  · exact modelsSwap

  · exact modelsSwapK

  · exact modelsSwapH

  · exact modelsSwapHK

#print axioms models_basis
end S6_3815


namespace S6_3826

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

theorem modelsCollect : lawCollect.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteCollect = true := by decide
  have valid := table.checkIdentityFused_sound finiteCollect checked
  have mapped := finiteCollect.satisfiedBy_map decodeCollect table.semigroup valid
  rw [roundTripCollect] at mapped
  exact mapped

theorem modelsAnchor : lawAnchor.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteAnchor = true := by decide
  have valid := table.checkIdentityFused_sound finiteAnchor checked
  have mapped := finiteAnchor.satisfiedBy_map decodeAnchor table.semigroup valid
  rw [roundTripAnchor] at mapped
  exact mapped

theorem modelsAnchorH : lawAnchorH.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteAnchorH = true := by decide
  have valid := table.checkIdentityFused_sound finiteAnchorH checked
  have mapped := finiteAnchorH.satisfiedBy_map decodeAnchorH table.semigroup valid
  rw [roundTripAnchorH] at mapped
  exact mapped

theorem modelsSwap : lawSwap.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwap = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwap checked
  have mapped := finiteSwap.satisfiedBy_map decodeSwap table.semigroup valid
  rw [roundTripSwap] at mapped
  exact mapped

theorem modelsSwapK : lawSwapK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapK = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapK checked
  have mapped := finiteSwapK.satisfiedBy_map decodeSwapK table.semigroup valid
  rw [roundTripSwapK] at mapped
  exact mapped

theorem modelsSwapH : lawSwapH.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapH = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapH checked
  have mapped := finiteSwapH.satisfiedBy_map decodeSwapH table.semigroup valid
  rw [roundTripSwapH] at mapped
  exact mapped

theorem modelsSwapHK : lawSwapHK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapHK = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapHK checked
  have mapped := finiteSwapHK.satisfiedBy_map decodeSwapHK table.semigroup valid
  rw [roundTripSwapHK] at mapped
  exact mapped

theorem models_basis : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · exact modelsPower

  · exact modelsLeft

  · exact modelsRight

  · exact modelsCollect

  · exact modelsAnchor

  · exact modelsAnchorH

  · exact modelsSwap

  · exact modelsSwapK

  · exact modelsSwapH

  · exact modelsSwapHK

#print axioms models_basis
end S6_3826


namespace S6_3828

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

theorem modelsCollect : lawCollect.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteCollect = true := by decide
  have valid := table.checkIdentityFused_sound finiteCollect checked
  have mapped := finiteCollect.satisfiedBy_map decodeCollect table.semigroup valid
  rw [roundTripCollect] at mapped
  exact mapped

theorem modelsAnchor : lawAnchor.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteAnchor = true := by decide
  have valid := table.checkIdentityFused_sound finiteAnchor checked
  have mapped := finiteAnchor.satisfiedBy_map decodeAnchor table.semigroup valid
  rw [roundTripAnchor] at mapped
  exact mapped

theorem modelsAnchorH : lawAnchorH.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteAnchorH = true := by decide
  have valid := table.checkIdentityFused_sound finiteAnchorH checked
  have mapped := finiteAnchorH.satisfiedBy_map decodeAnchorH table.semigroup valid
  rw [roundTripAnchorH] at mapped
  exact mapped

theorem modelsSwap : lawSwap.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwap = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwap checked
  have mapped := finiteSwap.satisfiedBy_map decodeSwap table.semigroup valid
  rw [roundTripSwap] at mapped
  exact mapped

theorem modelsSwapK : lawSwapK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapK = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapK checked
  have mapped := finiteSwapK.satisfiedBy_map decodeSwapK table.semigroup valid
  rw [roundTripSwapK] at mapped
  exact mapped

theorem modelsSwapH : lawSwapH.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapH = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapH checked
  have mapped := finiteSwapH.satisfiedBy_map decodeSwapH table.semigroup valid
  rw [roundTripSwapH] at mapped
  exact mapped

theorem modelsSwapHK : lawSwapHK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapHK = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapHK checked
  have mapped := finiteSwapHK.satisfiedBy_map decodeSwapHK table.semigroup valid
  rw [roundTripSwapHK] at mapped
  exact mapped

theorem models_basis : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · exact modelsPower

  · exact modelsLeft

  · exact modelsRight

  · exact modelsCollect

  · exact modelsAnchor

  · exact modelsAnchorH

  · exact modelsSwap

  · exact modelsSwapK

  · exact modelsSwapH

  · exact modelsSwapHK

#print axioms models_basis
end S6_3828


namespace S6_6437

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

theorem modelsCollect : lawCollect.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteCollect = true := by decide
  have valid := table.checkIdentityFused_sound finiteCollect checked
  have mapped := finiteCollect.satisfiedBy_map decodeCollect table.semigroup valid
  rw [roundTripCollect] at mapped
  exact mapped

theorem modelsAnchor : lawAnchor.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteAnchor = true := by decide
  have valid := table.checkIdentityFused_sound finiteAnchor checked
  have mapped := finiteAnchor.satisfiedBy_map decodeAnchor table.semigroup valid
  rw [roundTripAnchor] at mapped
  exact mapped

theorem modelsAnchorH : lawAnchorH.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteAnchorH = true := by decide
  have valid := table.checkIdentityFused_sound finiteAnchorH checked
  have mapped := finiteAnchorH.satisfiedBy_map decodeAnchorH table.semigroup valid
  rw [roundTripAnchorH] at mapped
  exact mapped

theorem modelsSwap : lawSwap.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwap = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwap checked
  have mapped := finiteSwap.satisfiedBy_map decodeSwap table.semigroup valid
  rw [roundTripSwap] at mapped
  exact mapped

theorem modelsSwapK : lawSwapK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapK = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapK checked
  have mapped := finiteSwapK.satisfiedBy_map decodeSwapK table.semigroup valid
  rw [roundTripSwapK] at mapped
  exact mapped

theorem modelsSwapH : lawSwapH.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapH = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapH checked
  have mapped := finiteSwapH.satisfiedBy_map decodeSwapH table.semigroup valid
  rw [roundTripSwapH] at mapped
  exact mapped

theorem modelsSwapHK : lawSwapHK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapHK = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapHK checked
  have mapped := finiteSwapHK.satisfiedBy_map decodeSwapHK table.semigroup valid
  rw [roundTripSwapHK] at mapped
  exact mapped

theorem models_basis : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · exact modelsPower

  · exact modelsLeft

  · exact modelsRight

  · exact modelsCollect

  · exact modelsAnchor

  · exact modelsAnchorH

  · exact modelsSwap

  · exact modelsSwapK

  · exact modelsSwapH

  · exact modelsSwapHK

#print axioms models_basis
end S6_6437


namespace S6_6444

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

theorem modelsCollect : lawCollect.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteCollect = true := by decide
  have valid := table.checkIdentityFused_sound finiteCollect checked
  have mapped := finiteCollect.satisfiedBy_map decodeCollect table.semigroup valid
  rw [roundTripCollect] at mapped
  exact mapped

theorem modelsAnchor : lawAnchor.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteAnchor = true := by decide
  have valid := table.checkIdentityFused_sound finiteAnchor checked
  have mapped := finiteAnchor.satisfiedBy_map decodeAnchor table.semigroup valid
  rw [roundTripAnchor] at mapped
  exact mapped

theorem modelsAnchorH : lawAnchorH.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteAnchorH = true := by decide
  have valid := table.checkIdentityFused_sound finiteAnchorH checked
  have mapped := finiteAnchorH.satisfiedBy_map decodeAnchorH table.semigroup valid
  rw [roundTripAnchorH] at mapped
  exact mapped

theorem modelsSwap : lawSwap.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwap = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwap checked
  have mapped := finiteSwap.satisfiedBy_map decodeSwap table.semigroup valid
  rw [roundTripSwap] at mapped
  exact mapped

theorem modelsSwapK : lawSwapK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapK = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapK checked
  have mapped := finiteSwapK.satisfiedBy_map decodeSwapK table.semigroup valid
  rw [roundTripSwapK] at mapped
  exact mapped

theorem modelsSwapH : lawSwapH.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapH = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapH checked
  have mapped := finiteSwapH.satisfiedBy_map decodeSwapH table.semigroup valid
  rw [roundTripSwapH] at mapped
  exact mapped

theorem modelsSwapHK : lawSwapHK.SatisfiedBy table.semigroup := by
  have checked : table.checkIdentityFused finiteSwapHK = true := by decide
  have valid := table.checkIdentityFused_sound finiteSwapHK checked
  have mapped := finiteSwapHK.satisfiedBy_map decodeSwapHK table.semigroup valid
  rw [roundTripSwapHK] at mapped
  exact mapped

theorem models_basis : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · exact modelsPower

  · exact modelsLeft

  · exact modelsRight

  · exact modelsCollect

  · exact modelsAnchor

  · exact modelsAnchorH

  · exact modelsSwap

  · exact modelsSwapK

  · exact modelsSwapH

  · exact modelsSwapHK

#print axioms models_basis
end S6_6444


end SemigroupBasis.CoRoots.Order6SporadicSection16

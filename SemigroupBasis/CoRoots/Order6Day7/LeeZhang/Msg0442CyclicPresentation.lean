import SemigroupBasis.Generated.S3_6
import SemigroupBasis.Generated.S4_11
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Order6Subdirect.Common
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-! Exact msg0442 cyclic-marker presentations. Variables retain the literal
encoding x=0,y=1,z=2,t=3. The actual catalogue tables and split subdirect maps
are closed finite checks; no bounded completeness certificate is imported. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Cyclic

open SemigroupBasis

def prefixSwapLaw : Identity Nat := ⟨⟨2, [3, 1]⟩, ⟨3, [2, 1]⟩⟩
def sandwichLaw : Identity Nat := ⟨⟨2, [3, 2]⟩, ⟨3, [2, 3]⟩⟩
def duplicationLaw : Identity Nat := ⟨⟨0, [1, 2, 3]⟩, ⟨0, [1, 1, 2, 3]⟩⟩
def suffixSwapLaw : Identity Nat := ⟨⟨3, [1, 2]⟩, ⟨3, [2, 1]⟩⟩
def terminalSwitchLaw : Identity Nat := ⟨⟨2, [2, 3]⟩, ⟨3, [3, 2]⟩⟩

def pairBasis : List (Identity Nat) := [prefixSwapLaw, sandwichLaw, duplicationLaw]
def singletonBasis : List (Identity Nat) := [suffixSwapLaw, terminalSwitchLaw, duplicationLaw]
def pairBasisSHA256 : String := "f6046a9189682a0e2d994fbe748fddb8512cf63a5f182e5b4fa580c15c593504"
def singletonBasisSHA256 : String := "55b2d15d68b836a82769d0ce2baa2a3b4b9148f18c2c293b756072c987a8b9a5"

theorem pair_basis_length : pairBasis.length = 3 := rfl
theorem singleton_basis_length : singletonBasis.length = 3 := rfl

def mul2797 (a b : Fin 6) : Fin 6 :=
  if a = 1 then if b = 4 then 2 else 0
  else if a = 4 then if b = 1 then 2 else if b = 4 then 1 else 0
  else if a = 5 then if b = 3 then 3 else if b = 5 then 5 else 0
  else 0
def mul2798 (a b : Fin 6) : Fin 6 :=
  if a = 1 then if b = 4 then 2 else 0
  else if a = 4 then if b = 1 then 2 else if b = 4 then 1 else 0
  else if a = 5 then if b = 3 ∨ b = 4 then 3 else if b = 5 then 5 else 0
  else 0
def mul5480 (a b : Fin 6) : Fin 6 :=
  if a = 4 then 4
  else if a = 5 then if b = 4 ∨ b = 5 then 4 else 5
  else if b = 4 ∨ b = 5 then 4
  else if a = 1 ∧ b = 3 then 2
  else if a = 3 then if b = 1 then 2 else if b = 3 then 1 else 0
  else 0

def table2797 : FiniteTable := ⟨6, mul2797, by decide⟩
def table2798 : FiniteTable := ⟨6, mul2798, by decide⟩
def table5480 : FiniteTable := ⟨6, mul5480, by decide⟩

theorem table2797_rows_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul2797 a b).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,2,0], [0,0,0,0,0,0],
       [0,0,0,0,0,0], [0,2,0,0,1,0], [0,0,0,3,0,5]] := by decide
theorem table2798_rows_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul2798 a b).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,2,0], [0,0,0,0,0,0],
       [0,0,0,0,0,0], [0,2,0,0,1,0], [0,0,0,3,3,5]] := by decide
theorem table5480_rows_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul5480 a b).val)) =
      [[0,0,0,0,4,4], [0,0,0,2,4,4], [0,0,0,0,4,4],
       [0,2,0,1,4,4], [4,4,4,4,4,4], [5,5,5,5,4,4]] := by decide

abbrev markerTable := Generated.S3_6.table
abbrev cyclicTable := Generated.S4_11.table
abbrev initialTable := Order6Subdirect.oppositeTable markerTable

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem pairMarkerModels : Models markerTable.semigroup pairBasis :=
  FiniteCertificate.checkModels_sound markerTable pairBasis toFinFour (by decide)
theorem pairCyclicModels : Models cyclicTable.semigroup pairBasis :=
  FiniteCertificate.checkModels_sound cyclicTable pairBasis toFinFour (by decide)
theorem singletonMarkerModels : Models initialTable.semigroup singletonBasis :=
  FiniteCertificate.checkModels_sound initialTable singletonBasis toFinFour (by decide)
theorem singletonCyclicModels : Models cyclicTable.semigroup singletonBasis :=
  FiniteCertificate.checkModels_sound cyclicTable singletonBasis toFinFour (by decide)

def markerMap2797 (x : Fin 6) : Fin 3 := if x = 3 then 1 else if x = 5 then 2 else 0
def markerMap2798 (x : Fin 6) : Fin 3 := if x = 3 ∨ x = 4 then 1 else if x = 5 then 2 else 0
def cyclicMapPair (x : Fin 6) : Fin 4 := if x = 1 then 1 else if x = 2 then 2 else if x = 4 then 3 else 0
def markerMap5480 (x : Fin 6) : Fin 3 := if x = 4 then 0 else if x = 5 then 1 else 2
def cyclicMap5480 (x : Fin 6) : Fin 4 := if x = 1 then 1 else if x = 2 then 2 else if x = 3 then 3 else 0
def markerSectionPair (x : Fin 3) : Fin 6 := if x = 0 then 0 else if x = 1 then 3 else 5
def cyclicSectionPair (x : Fin 4) : Fin 6 := if x = 0 then 0 else if x = 1 then 1 else if x = 2 then 2 else 4
def markerSection5480 (x : Fin 3) : Fin 6 := if x = 0 then 4 else if x = 1 then 5 else 0
def cyclicSection5480 (x : Fin 4) : Fin 6 := ⟨x.val, by omega⟩

def marker2797 : SplitSurjection table2797.semigroup markerTable.semigroup where
  toFun := markerMap2797
  map_mul := by decide
  preimage := markerSectionPair
  right_inverse := by decide
def marker2798 : SplitSurjection table2798.semigroup markerTable.semigroup where
  toFun := markerMap2798
  map_mul := by decide
  preimage := markerSectionPair
  right_inverse := by decide
def marker5480 : SplitSurjection table5480.semigroup initialTable.semigroup where
  toFun := markerMap5480
  map_mul := by decide
  preimage := markerSection5480
  right_inverse := by decide
def cyclic2797 : SplitSurjection table2797.semigroup cyclicTable.semigroup where
  toFun := cyclicMapPair
  map_mul := by decide
  preimage := cyclicSectionPair
  right_inverse := by decide
def cyclic2798 : SplitSurjection table2798.semigroup cyclicTable.semigroup where
  toFun := cyclicMapPair
  map_mul := by decide
  preimage := cyclicSectionPair
  right_inverse := by decide
def cyclic5480 : SplitSurjection table5480.semigroup cyclicTable.semigroup where
  toFun := cyclicMap5480
  map_mul := by decide
  preimage := cyclicSection5480
  right_inverse := by decide

def subdirect2797 : SubdirectPair table2797.semigroup markerTable.semigroup cyclicTable.semigroup where
  left := marker2797
  right := cyclic2797
  jointlyInjective := by unfold Function.Injective; decide
def subdirect2798 : SubdirectPair table2798.semigroup markerTable.semigroup cyclicTable.semigroup where
  left := marker2798
  right := cyclic2798
  jointlyInjective := by unfold Function.Injective; decide
def subdirect5480 : SubdirectPair table5480.semigroup initialTable.semigroup cyclicTable.semigroup where
  left := marker5480
  right := cyclic5480
  jointlyInjective := by unfold Function.Injective; decide

theorem models2797 : Models table2797.semigroup pairBasis :=
  FiniteCertificate.checkModels_sound table2797 pairBasis toFinFour (by decide)
theorem models2798 : Models table2798.semigroup pairBasis :=
  FiniteCertificate.checkModels_sound table2798 pairBasis toFinFour (by decide)
theorem models5480 : Models table5480.semigroup singletonBasis :=
  FiniteCertificate.checkModels_sound table5480 singletonBasis toFinFour (by decide)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Cyclic

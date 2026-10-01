import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442InitialMarkerJoin
import SemigroupBasis.CoRoots.S5_83Family
import SemigroupBasis.CoRoots.S5_240Completeness

/-! Actual factor maps and exact ordered seven-law presentations for
msg0441's four-class system and msg0442's S6_2979 singleton. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Initial

open SemigroupBasis

abbrev markerTable := InitialMarkerJoin.markerTable
def toFinite : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

namespace Group1040

def law00 : Identity Nat := ⟨⟨3, [3]⟩, ⟨3, [3, 3]⟩⟩
def law01 : Identity Nat := ⟨⟨2, [3, 2]⟩, ⟨3, [2, 3]⟩⟩
def law02 : Identity Nat := ⟨⟨2, [3, 2]⟩, ⟨3, [3, 2, 3]⟩⟩
def law03 : Identity Nat := ⟨⟨3, [1, 2, 1]⟩, ⟨3, [2, 1, 1]⟩⟩
def law04 : Identity Nat := ⟨⟨1, [2, 3, 1]⟩, ⟨3, [1, 2, 3]⟩⟩
def law05 : Identity Nat := ⟨⟨1, [2, 3, 1]⟩, ⟨3, [2, 1, 3]⟩⟩
abbrev law06 := Msg0442Cyclic.duplicationLaw
def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06]
def basisSHA256 : String := "ffcbc0db77b0ab08f86c090facf05e368e8dec9298e70ec1247397521153fe53"
theorem basis_length : basis.length = 7 := rfl

def mul1040 (a b : Fin 6) : Fin 6 :=
  if a = 3 then if b = 5 then 3 else 0
  else if a = 4 then if b = 2 then 1 else 0
  else if a = 5 then if b = 1 then 1 else if b = 4 then 4 else if b = 5 then 5 else 0
  else 0
def mul1042 (a b : Fin 6) : Fin 6 :=
  if a = 3 then if b = 5 then 3 else 0
  else if a = 4 then if b = 2 then 1 else 0
  else if a = 5 then if b = 1 ∨ b = 2 then 1 else if b = 4 then 4 else if b = 5 then 5 else 0
  else 0
def mul1098 (a b : Fin 6) : Fin 6 :=
  if a = 2 ∨ a = 3 then if b = 5 then 2 else 0
  else if a = 4 then if b = 3 then 1 else 0
  else if a = 5 then if b = 1 then 1 else if b = 4 then 4 else if b = 5 then 5 else 0
  else 0
def mul1099 (a b : Fin 6) : Fin 6 :=
  if a = 2 ∨ a = 3 then if b = 5 then 2 else 0
  else if a = 4 then if b = 3 then 1 else 0
  else if a = 5 then if b = 1 ∨ b = 3 then 1 else if b = 4 then 4 else if b = 5 then 5 else 0
  else 0

def table1040 : FiniteTable := ⟨6, mul1040, by decide⟩
def table1042 : FiniteTable := ⟨6, mul1042, by decide⟩
def table1098 : FiniteTable := ⟨6, mul1098, by decide⟩
def table1099 : FiniteTable := ⟨6, mul1099, by decide⟩

theorem rows1040 :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul1040 a b).val)) =
      [[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,3],[0,0,1,0,0,0],[0,1,0,0,4,5]] := by decide
theorem rows1042 :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul1042 a b).val)) =
      [[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,3],[0,0,1,0,0,0],[0,1,1,0,4,5]] := by decide
theorem rows1098 :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul1098 a b).val)) =
      [[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,2],[0,0,0,0,0,2],[0,0,0,1,0,0],[0,1,0,0,4,5]] := by decide
theorem rows1099 :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul1099 a b).val)) =
      [[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,2],[0,0,0,0,0,2],[0,0,0,1,0,0],[0,1,0,1,4,5]] := by decide

abbrev right83 := Generated.Catalogue.S5_83.table
abbrev right84 := Generated.Catalogue.S5_84.table
theorem markerModels : Models markerTable.semigroup basis :=
  FiniteCertificate.checkModels_sound markerTable basis toFinite (by decide)
theorem right83Models : Models right83.semigroup basis :=
  FiniteCertificate.checkModels_sound right83 basis toFinite (by decide)
theorem right84Models : Models right84.semigroup basis :=
  FiniteCertificate.checkModels_sound right84 basis toFinite (by decide)
theorem right83LeftReductive : InitialMarkerJoin.LeftReductive right83.semigroup := by
  unfold InitialMarkerJoin.LeftReductive
  decide
theorem right84LeftReductive : InitialMarkerJoin.LeftReductive right84.semigroup := by
  unfold InitialMarkerJoin.LeftReductive
  decide

abbrev markerMap1040 := Msg0442Cyclic.markerMap2797
def markerMap1098 (x : Fin 6) : Fin 3 := if x = 2 ∨ x = 3 then 1 else if x = 5 then 2 else 0
def rightMap1040 (x : Fin 6) : Fin 5 :=
  if x = 1 then 1 else if x = 2 then 2 else if x = 4 then 3 else if x = 5 then 4 else 0
def rightMap1098 (x : Fin 6) : Fin 5 :=
  if x = 1 then 1 else if x = 3 then 2 else if x = 4 then 3 else if x = 5 then 4 else 0
abbrev markerSection1040 := Msg0442Cyclic.markerSectionPair
def markerSection1098 (x : Fin 3) : Fin 6 := if x = 0 then 0 else if x = 1 then 2 else 5
def rightSection (middle : Fin 6) (x : Fin 5) : Fin 6 :=
  if x = 0 then 0 else if x = 1 then 1 else if x = 2 then middle else if x = 3 then 4 else 5

def marker1040 : SplitSurjection table1040.semigroup markerTable.semigroup where
  toFun := markerMap1040
  map_mul := by decide
  preimage := markerSection1040
  right_inverse := by decide
def marker1042 : SplitSurjection table1042.semigroup markerTable.semigroup where
  toFun := markerMap1040
  map_mul := by decide
  preimage := markerSection1040
  right_inverse := by decide
def marker1098 : SplitSurjection table1098.semigroup markerTable.semigroup where
  toFun := markerMap1098
  map_mul := by decide
  preimage := markerSection1098
  right_inverse := by decide
def marker1099 : SplitSurjection table1099.semigroup markerTable.semigroup where
  toFun := markerMap1098
  map_mul := by decide
  preimage := markerSection1098
  right_inverse := by decide
def right1040 : SplitSurjection table1040.semigroup right83.semigroup where
  toFun := rightMap1040
  map_mul := by decide
  preimage := rightSection 2
  right_inverse := by decide
def right1042 : SplitSurjection table1042.semigroup right84.semigroup where
  toFun := rightMap1040
  map_mul := by decide
  preimage := rightSection 2
  right_inverse := by decide
def right1098 : SplitSurjection table1098.semigroup right83.semigroup where
  toFun := rightMap1098
  map_mul := by decide
  preimage := rightSection 3
  right_inverse := by decide
def right1099 : SplitSurjection table1099.semigroup right84.semigroup where
  toFun := rightMap1098
  map_mul := by decide
  preimage := rightSection 3
  right_inverse := by decide

def subdirect1040 : SubdirectPair table1040.semigroup markerTable.semigroup right83.semigroup :=
  ⟨marker1040, right1040, by unfold Function.Injective; decide⟩
def subdirect1042 : SubdirectPair table1042.semigroup markerTable.semigroup right84.semigroup :=
  ⟨marker1042, right1042, by unfold Function.Injective; decide⟩
def subdirect1098 : SubdirectPair table1098.semigroup markerTable.semigroup right83.semigroup :=
  ⟨marker1098, right1098, by unfold Function.Injective; decide⟩
def subdirect1099 : SubdirectPair table1099.semigroup markerTable.semigroup right84.semigroup :=
  ⟨marker1099, right1099, by unfold Function.Injective; decide⟩

theorem models1040 : Models table1040.semigroup basis := FiniteCertificate.checkModels_sound table1040 basis toFinite (by decide)
theorem models1042 : Models table1042.semigroup basis := FiniteCertificate.checkModels_sound table1042 basis toFinite (by decide)
theorem models1098 : Models table1098.semigroup basis := FiniteCertificate.checkModels_sound table1098 basis toFinite (by decide)
theorem models1099 : Models table1099.semigroup basis := FiniteCertificate.checkModels_sound table1099 basis toFinite (by decide)

end Group1040

namespace Single2979

abbrev law00 := Group1040.law00
def law01 : Identity Nat := ⟨⟨3, [2, 3]⟩, ⟨3, [3, 2, 3]⟩⟩
def law02 : Identity Nat := ⟨⟨3, [1, 2, 2]⟩, ⟨3, [2, 1, 1]⟩⟩
def law03 : Identity Nat := ⟨⟨2, [3, 2, 1]⟩, ⟨3, [2, 3, 1]⟩⟩
def law04 : Identity Nat := ⟨⟨2, [2, 3, 3]⟩, ⟨3, [2, 2, 3]⟩⟩
abbrev law05 := Msg0442Cyclic.duplicationLaw
def law06 : Identity Nat := ⟨⟨0, [1, 2, 0, 3]⟩, ⟨1, [0, 2, 1, 3]⟩⟩
def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06]
def basisSHA256 : String := "425c664a1f65aaa8f01bd9416742c79c4c6c76d98984e5b97cb43b542e4bd14f"
theorem basis_length : basis.length = 7 := rfl

def mul2979 (a b : Fin 6) : Fin 6 :=
  if a = 2 then if b = 5 then 1 else 0
  else if a = 3 then if b = 4 ∨ b = 5 then 3 else 0
  else if a = 4 ∨ a = 5 then if b = 1 then 1 else if b = 2 then 2 else if b = 4 ∨ b = 5 then 4 else 0
  else 0
def table2979 : FiniteTable := ⟨6, mul2979, by decide⟩
theorem rows2979 :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul2979 a b).val)) =
      [[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,1],[0,0,0,0,3,3],[0,1,2,0,4,4],[0,1,2,0,4,4]] := by decide

abbrev rightTable := Generated.Catalogue.S5_240.table
theorem markerModels : Models markerTable.semigroup basis :=
  FiniteCertificate.checkModels_sound markerTable basis toFinite (by decide)
theorem rightModels : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinite (by decide)
theorem rightLeftReductive : InitialMarkerJoin.LeftReductive rightTable.semigroup := by
  unfold InitialMarkerJoin.LeftReductive
  decide

def markerMap2979 (x : Fin 6) : Fin 3 := if x = 3 then 1 else if x = 4 ∨ x = 5 then 2 else 0
def markerSection2979 (x : Fin 3) : Fin 6 := if x = 0 then 0 else if x = 1 then 3 else 4
def marker2979 : SplitSurjection table2979.semigroup markerTable.semigroup where
  toFun := markerMap2979
  map_mul := by decide
  preimage := markerSection2979
  right_inverse := by decide
def right2979 : SplitSurjection table2979.semigroup rightTable.semigroup where
  toFun := Group1040.rightMap1040
  map_mul := by decide
  preimage := Group1040.rightSection 2
  right_inverse := by decide
def subdirect2979 : SubdirectPair table2979.semigroup markerTable.semigroup rightTable.semigroup :=
  ⟨marker2979, right2979, by unfold Function.Injective; decide⟩
theorem models2979 : Models table2979.semigroup basis :=
  FiniteCertificate.checkModels_sound table2979 basis toFinite (by decide)

end Single2979
end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Initial

import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442CyclicMoves
import SemigroupBasis.CoRoots.Order6FactorPairS3_18S4_20Prelude

/-! Exact msg0443 displayed laws and actual finite table interfaces. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Single9095

open SemigroupBasis

def law00 : Identity Nat := (Identity.mk (Word.mk 2 [2]) (Word.mk 2 [2, 2, 2, 2]))
def law01 : Identity Nat := (Identity.mk (Word.mk 1 [1, 2, 2]) (Word.mk 2 [1, 1, 2]))
def law02 : Identity Nat := (Identity.mk (Word.mk 1 [1, 2, 2]) (Word.mk 2 [2, 1, 1]))
def law03 : Identity Nat := (Identity.mk (Word.mk 2 [0, 1, 1]) (Word.mk 2 [1, 0, 1]))
def law04 : Identity Nat := (Identity.mk (Word.mk 2 [0, 1, 2]) (Word.mk 2 [1, 0, 2]))
def law05 : Identity Nat := (Identity.mk (Word.mk 2 [1, 2, 0]) (Word.mk 2 [2, 1, 0]))
def law06 : Identity Nat := (Identity.mk (Word.mk 0 [1, 0]) (Word.mk 0 [0, 0, 0, 1, 0]))
def law07 : Identity Nat := (Identity.mk (Word.mk 0 [1, 0]) (Word.mk 0 [1, 1, 1, 1, 0]))
def law08 : Identity Nat := (Identity.mk (Word.mk 0 [1, 2]) (Word.mk 0 [1, 1, 1, 1, 2]))
def law09 : Identity Nat := (Identity.mk (Word.mk 0 [1, 2, 3]) (Word.mk 0 [2, 1, 3]))
def law10 : Identity Nat := (Identity.mk (Word.mk 0 [0, 0, 1, 0]) (Word.mk 1 [0, 1, 1, 1]))
def law11 : Identity Nat := (Identity.mk (Word.mk 0 [0, 0, 1, 1]) (Word.mk 1 [0, 0, 0, 1]))
def law12 : Identity Nat := (Identity.mk (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [1, 1, 2, 0]))
def law13 : Identity Nat := (Identity.mk (Word.mk 0 [0, 1, 2, 1]) (Word.mk 1 [0, 0, 2, 1]))
def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10, law11, law12, law13]
def basisSHA256 : String := "024c153ad2761c1b2e6a13d0acea471a3019195df88f55a455c67cb42d21da22"
theorem basis_length : basis.length = 14 := rfl

abbrev leftTable := Generated.S3_18.table
abbrev expandedTable := Generated.Catalogue.S4_124.table
abbrev rightTable := Generated.S4_20.table
def toFinite : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem leftModels : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinite (by decide)
theorem rightModels : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinite (by decide)
theorem expandedModels : Models expandedTable.semigroup basis :=
  FiniteCertificate.checkModels_sound expandedTable basis toFinite (by decide)

def mul9095 (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 2 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else if b = 3 then 3 else if b = 4 then 4 else 5) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else if b = 3 then 4 else if b = 4 then 5 else 3) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else if b = 3 then 5 else if b = 4 then 3 else 4)
def table9095 : FiniteTable := ⟨6, mul9095, by decide⟩
theorem rows9095 :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul9095 a b).val)) =
      [[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,2,2,2],[0,1,0,3,4,5],[0,1,0,4,5,3],[0,1,0,5,3,4]] := by decide
def cyclicMap (value : Fin 3) : Fin 6 := if value = 0 then 3 else if value = 1 then 4 else 5
def cyclicEmbedding : Embedding leftTable.semigroup table9095.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  injective := by unfold Function.Injective; decide
def quotientMap (value : Fin 6) : Fin 4 := if value = 0 then 0 else if value = 1 then 1 else if value = 2 then 2 else if value = 3 then 3 else if value = 4 then 3 else 3
def quotientSection (value : Fin 4) : Fin 6 := if value = 0 then 0 else if value = 1 then 1 else if value = 2 then 2 else 3
def endpointQuotient : SplitSurjection table9095.semigroup rightTable.semigroup where
  toFun := quotientMap
  map_mul := by decide
  preimage := quotientSection
  right_inverse := by decide

def expandedMap (value : Fin 6) : Fin 4 :=
  if value = 3 then 1 else if value = 4 then 2 else if value = 5 then 3 else 0
def expandedSection (value : Fin 4) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 3 else if value = 2 then 4 else 5
def expandedQuotient : SplitSurjection table9095.semigroup expandedTable.semigroup where
  toFun := expandedMap
  map_mul := by decide
  preimage := expandedSection
  right_inverse := by decide
def subdirect9095 : SubdirectPair table9095.semigroup expandedTable.semigroup rightTable.semigroup where
  left := expandedQuotient
  right := endpointQuotient
  jointlyInjective := by unfold Function.Injective; decide
def cyclicCoreMap (value : Fin 3) : Fin 4 := if value = 0 then 1 else if value = 1 then 2 else 3
def cyclicCoreEmbedding : Embedding leftTable.semigroup expandedTable.semigroup where
  toFun := cyclicCoreMap
  map_mul := by decide
  injective := by unfold Function.Injective; decide

theorem models9095 : Models table9095.semigroup basis := by
  intro identity member
  exact (subdirect9095.satisfiedBy_iff identity).mpr ⟨expandedModels identity member, rightModels identity member⟩

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Single9095

import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443InitialMarkerLongJoin
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442InitialRules
import SemigroupBasis.CoRoots.Order6Day7.S2_4.SeedS5_203
import SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_203Prelude

/-! The exact msg0443 ten-law repair, distinct from refuted raw15 and the
unapproved candidate16. Literal variables remain x=0,y=1,z=2,t=3. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Pair2675

open SemigroupBasis

def law00 : Identity Nat := ⟨⟨2, [3, 2]⟩, ⟨3, [2, 3]⟩⟩
def law01 : Identity Nat := ⟨⟨3, [3, 2]⟩, ⟨3, [3, 3, 2]⟩⟩
def law02 : Identity Nat := ⟨⟨2, [3, 2]⟩, ⟨3, [3, 2, 3]⟩⟩
def law03 : Identity Nat := ⟨⟨1, [2, 3, 1]⟩, ⟨3, [1, 2, 3]⟩⟩
def law04 : Identity Nat := ⟨⟨1, [2, 3, 1]⟩, ⟨3, [2, 1, 3]⟩⟩
def law05 : Identity Nat := ⟨⟨0, [1, 2, 3]⟩, ⟨0, [1, 1, 2, 3]⟩⟩
def law06 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1, 1]⟩⟩
def law07 : Identity Nat := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 1, 2, 1]⟩⟩
def law08 : Identity Nat := ⟨⟨0, [0, 1, 2, 2]⟩, ⟨0, [1, 0, 2, 2]⟩⟩
def law09 : Identity Nat := ⟨⟨0, [0, 1, 2, 3]⟩, ⟨0, [1, 0, 2, 3]⟩⟩
def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09]
def basisSHA256 : String := "21e045f4e61955e0d5bfacdce1364852e60875d2adc67307b927a3a186843545"
theorem basis_length : basis.length = 10 := rfl

abbrev markerTable := InitialMarkerJoin.markerTable
abbrev rightTable := S5_203.table
abbrev table2675 := Order6FactorPairS3_6opS5_203.S6_2675.table
abbrev table2677 := Order6FactorPairS3_6opS5_203.S6_2677.table
abbrev subdirect2675 := Order6FactorPairS3_6opS5_203.S6_2675.pair
abbrev subdirect2677 := Order6FactorPairS3_6opS5_203.S6_2677.pair

theorem markerModels : Models markerTable.semigroup basis :=
  FiniteCertificate.checkModels_sound markerTable basis Msg0442Initial.toFinite (by decide)
theorem rightModels : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis Msg0442Initial.toFinite (by decide)
theorem models2675 : Models table2675.semigroup basis :=
  FiniteCertificate.checkModels_sound table2675 basis Msg0442Initial.toFinite (by decide)
theorem models2677 : Models table2677.semigroup basis :=
  FiniteCertificate.checkModels_sound table2677 basis Msg0442Initial.toFinite (by decide)
theorem rightLeftReductive : InitialMarkerJoin.LeftReductive rightTable.semigroup := by
  unfold InitialMarkerJoin.LeftReductive
  decide

/-- The certified lower derivation isolates every short word literally. -/
theorem shortOrLong (identity : Identity Nat) (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.lhs = identity.rhs ∨ (3 ≤ identity.lhs.toList.length ∧ 3 ≤ identity.rhs.toList.length) :=
  SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank044.Seed.lowerDerivation_shortOrLong
    (S5_203Family.S5_203.basisFor.2 identity valid)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Pair2675

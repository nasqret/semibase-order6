import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op

/-!
# Exact B20 data for the Lee--Zhang Proposition 23.9 pair

The d021 design packet records a twenty-law displayed basis for the two
classes `S6_8448` and `S6_11262`.  Its first four identities are literally
the published Proposition 23.9 basis, in the existing source order.  The
sixteen identities below are the recorded bridge suffix.

This module contains only authenticated data and finite-model soundness.
It deliberately does not invoke `BasisFor.replace`, close the B4
derivational obligation, or export order-six representative endpoints.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

namespace SemigroupBasis.CoRoots.Order6LeeZhang23_9B20Data

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-! ## The exact sixteen-law suffix -/

/-- `cabcac = cacabc`. -/
def bridge00 : Identity Nat :=
  Identity.mk (w 2 [0, 1, 2, 0, 2]) (w 2 [0, 2, 0, 1, 2])

/-- `cacac = caac`. -/
def bridge01 : Identity Nat :=
  Identity.mk (w 2 [0, 2, 0, 2]) (w 2 [0, 0, 2])

/-- `abba = ababa`. -/
def bridge02 : Identity Nat :=
  Identity.mk (w 0 [1, 1, 0]) (w 0 [1, 0, 1, 0])

/-- `caabcb = caacbb`. -/
def bridge03 : Identity Nat :=
  Identity.mk (w 2 [0, 0, 1, 2, 1]) (w 2 [0, 0, 2, 1, 1])

/-- `bacbc = bcbabc`. -/
def bridge04 : Identity Nat :=
  Identity.mk (w 1 [0, 2, 1, 2]) (w 1 [2, 1, 0, 1, 2])

/-- `aaccb = acacb`. -/
def bridge05 : Identity Nat :=
  Identity.mk (w 0 [0, 2, 2, 1]) (w 0 [2, 0, 2, 1])

/-- `babacc = bbacac`. -/
def bridge06 : Identity Nat :=
  Identity.mk (w 1 [0, 1, 0, 2, 2]) (w 1 [1, 0, 2, 0, 2])

/-- `cbbca = cbcbca`. -/
def bridge07 : Identity Nat :=
  Identity.mk (w 2 [1, 1, 2, 0]) (w 2 [1, 2, 1, 2, 0])

/-- `babcc = bbacc`. -/
def bridge08 : Identity Nat :=
  Identity.mk (w 1 [0, 1, 2, 2]) (w 1 [1, 0, 2, 2])

/-- `cabcb = ccabb`. -/
def bridge09 : Identity Nat :=
  Identity.mk (w 2 [0, 1, 2, 1]) (w 2 [2, 0, 1, 1])

/-- `aacbb = abacb`. -/
def bridge10 : Identity Nat :=
  Identity.mk (w 0 [0, 2, 1, 1]) (w 0 [1, 0, 2, 1])

/-- `abccb = acbcb`. -/
def bridge11 : Identity Nat :=
  Identity.mk (w 0 [1, 2, 2, 1]) (w 0 [2, 1, 2, 1])

/-- `cbaba = cabba`. -/
def bridge12 : Identity Nat :=
  Identity.mk (w 2 [1, 0, 1, 0]) (w 2 [0, 1, 1, 0])

/-- `babcb = bcbab`. -/
def bridge13 : Identity Nat :=
  Identity.mk (w 1 [0, 1, 2, 1]) (w 1 [2, 1, 0, 1])

/-- `babca = bbcaa`. -/
def bridge14 : Identity Nat :=
  Identity.mk (w 1 [0, 1, 2, 0]) (w 1 [1, 2, 0, 0])

/-- `ccbaa = cacba`. -/
def bridge15 : Identity Nat :=
  Identity.mk (w 2 [2, 1, 0, 0]) (w 2 [0, 2, 1, 0])

/-- The exact ordered bridge suffix recorded by the accepted d021 packet. -/
def bridgeBasis16 : List (Identity Nat) :=
  [bridge00, bridge01, bridge02, bridge03,
    bridge04, bridge05, bridge06, bridge07,
    bridge08, bridge09, bridge10, bridge11,
    bridge12, bridge13, bridge14, bridge15]

theorem bridgeBasis16_length : bridgeBasis16.length = 16 := by
  decide

/-! ## Literal B4-prefix assembly and packet metadata -/

/-- The accepted B20 list, with the published B4 list as a literal prefix. -/
def b20Basis : List (Identity Nat) :=
  SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.publishedBasis ++
    bridgeBasis16

/-- Recorded hash of the four-law displayed prefix. -/
def displayedB4SHA256 : String :=
  "9811132f6732c7505584a1480a81d042b31ed20238041c682f14fe37032e113b"

/-- Recorded raw displayed-list hash of the accepted twenty-law list. -/
def displayedBasisSHA256 : String :=
  "7ec16079273858e127e48f8afc6344408a63498f2f90a3f5c640953294bc4142"

theorem displayedBasisSHA256_exact :
    displayedBasisSHA256 =
      "7ec16079273858e127e48f8afc6344408a63498f2f90a3f5c640953294bc4142" := by
  decide

theorem b20Basis_length : b20Basis.length = 20 := by
  decide

/-- Kernel-visible witness that B4 enters B20 only as the literal left
prefix; the bridge suffix is not allowed to reorder the published laws. -/
theorem b20Basis_eq_published_append_bridges :
    b20Basis =
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.publishedBasis ++
        bridgeBasis16 :=
  rfl

/-! ## Independent finite-table soundness -/

/-- The bridge suffix uses only the displayed names `0, 1, 2`.  Mapping
only the bridge suffix to `Fin 3` keeps exhaustive checking stack-bounded;
`FiniteCertificate.checkModels` still checks the exact round trip for every
identity, so no accidental variable collapse is trusted.  The published B4
prefix uses the hull's existing dedicated stack-bounded six-variable
certificate. -/
private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem leftBridgeModelsChecked :
    FiniteCertificate.checkModels
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.leftTable
      bridgeBasis16 toFinThree = true := by
  decide

private theorem rightBridgeModelsChecked :
    FiniteCertificate.checkModels
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.rightTable
      bridgeBasis16 toFinThree = true := by
  decide

private theorem models_left_bridges :
    Models
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.leftTable.semigroup
      bridgeBasis16 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.leftTable
    bridgeBasis16 toFinThree leftBridgeModelsChecked

private theorem models_right_bridges :
    Models
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.rightTable.semigroup
      bridgeBasis16 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.rightTable
    bridgeBasis16 toFinThree rightBridgeModelsChecked

/-- Every one of the twenty literal laws is valid in `S2_4`. -/
theorem models_left :
    Models
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.G
      b20Basis := by
  intro identity member
  rw [b20Basis_eq_published_append_bridges] at member
  rcases List.mem_append.mp member with publishedMember | bridgeMember
  · exact
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.models_left
        identity publishedMember
  · change identity.SatisfiedBy
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.leftTable.semigroup
    exact models_left_bridges identity bridgeMember

/-- Every one of the twenty literal laws is valid in `S5_402^op`. -/
theorem models_right :
    Models
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.H
      b20Basis := by
  intro identity member
  rw [b20Basis_eq_published_append_bridges] at member
  rcases List.mem_append.mp member with publishedMember | bridgeMember
  · exact
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.models_right
        identity publishedMember
  · change identity.SatisfiedBy
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.rightTable.semigroup
    exact models_right_bridges identity bridgeMember

/-- Componentwise soundness of B20 in the selected product hull. -/
theorem models_prod :
    Models
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.P
      b20Basis := by
  intro identity member
  exact Identity.satisfiedBy_prod
    (models_left identity member) (models_right identity member)

end SemigroupBasis.CoRoots.Order6LeeZhang23_9B20Data

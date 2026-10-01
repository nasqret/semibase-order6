import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityNormalization
import SemigroupBasis.CoRoots.S5_831Completeness
import SemigroupBasis.Generated.S3_11
import SemigroupBasis.Order6Subdirect.HullFamilyTransfers
import SemigroupBasis.Order6Subdirect.S6_11165Subdirect
import SemigroupBasis.Order6Subdirect.S6_11166Subdirect

/-!
# Proposition 23.1 B23 replacement and order-six endpoints

The hard normalization theorem proves completeness of the published B15 for
`S3_11 x S5_831`. This module adds the eight sound separator identities,
uses `BasisFor.replace` in the safe prefix-extension direction, transfers the
B15 obligation to `S5_832`, and exposes the two direct and two opposite
order-six endpoints.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull23_1PhaseParityB23Endpoints

open SemigroupBasis.Order6Subdirect

/-- The eight separator bridges in the accepted B23 order. -/
def bridgeFinBasis : List (Identity (Fin 3)) :=
  [⟨⟨0, [1, 1, 2, 0]⟩, ⟨0, [1, 0, 2, 1]⟩⟩,
   ⟨⟨0, [2, 0, 2, 1, 1]⟩, ⟨0, [2, 0, 1, 1, 2]⟩⟩,
   ⟨⟨1, [1, 2, 0, 1, 2]⟩, ⟨1, [1, 1, 2, 0, 2]⟩⟩,
   ⟨⟨1, [0, 1, 2, 1]⟩, ⟨1, [0, 0, 2, 0]⟩⟩,
   ⟨⟨0, [2, 0, 1, 0]⟩, ⟨0, [2, 2, 1, 2]⟩⟩,
   ⟨⟨0, [2, 0, 1, 2]⟩, ⟨0, [2, 2, 1, 0]⟩⟩,
   ⟨⟨0, [0, 1, 0, 2, 1]⟩, ⟨0, [0, 1, 1, 2, 0]⟩⟩,
   ⟨⟨2, [2, 1, 1, 0, 2]⟩, ⟨2, [2, 1, 2, 0, 1]⟩⟩]

/-- The bridge system over the campaign's `Nat` variable type. -/
def bridgeBasis : List (Identity Nat) :=
  bridgeFinBasis.map (Identity.map Fin.val)

/-- The accepted 23-law display: the published B15 followed by eight bridges. -/
def displayedBasis : List (Identity Nat) :=
  Hull23_1_S3_11_S5_831.publishedBasis ++ bridgeBasis

/-- A fully literal copy of the accepted 23-law display. -/
def literalBasis : List (Identity Nat) :=
  [⟨⟨0, [0, 1, 0]⟩, ⟨0, [0, 0, 1, 1, 1]⟩⟩,
   ⟨⟨0, [0, 0, 0]⟩, ⟨0, [0]⟩⟩,
   ⟨⟨0, [1, 0, 0, 0]⟩, ⟨0, [1, 0]⟩⟩,
   ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 1, 1]⟩⟩,
   ⟨⟨0, [1, 2, 0, 0]⟩, ⟨0, [1, 2, 2, 2]⟩⟩,
   ⟨⟨0, [1, 1, 1, 0]⟩, ⟨0, [1, 0]⟩⟩,
   ⟨⟨0, [1, 2, 2, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩,
   ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩,
   ⟨⟨0, [1, 2, 0, 1]⟩, ⟨0, [1, 2, 1, 0]⟩⟩,
   ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩,
   ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩,
   ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 1, 2, 2, 1, 0]⟩⟩,
   ⟨⟨0, [1, 0, 2, 3, 3]⟩, ⟨0, [1, 1, 2, 3, 3, 1, 0]⟩⟩,
   ⟨⟨0, [1, 2, 0, 3, 3]⟩, ⟨0, [1, 2, 2, 3, 3, 2, 0]⟩⟩,
   ⟨⟨0, [1, 2, 0, 3, 4, 4]⟩, ⟨0, [1, 2, 2, 3, 4, 4, 2, 0]⟩⟩,
   ⟨⟨0, [1, 1, 2, 0]⟩, ⟨0, [1, 0, 2, 1]⟩⟩,
   ⟨⟨0, [2, 0, 2, 1, 1]⟩, ⟨0, [2, 0, 1, 1, 2]⟩⟩,
   ⟨⟨1, [1, 2, 0, 1, 2]⟩, ⟨1, [1, 1, 2, 0, 2]⟩⟩,
   ⟨⟨1, [0, 1, 2, 1]⟩, ⟨1, [0, 0, 2, 0]⟩⟩,
   ⟨⟨0, [2, 0, 1, 0]⟩, ⟨0, [2, 2, 1, 2]⟩⟩,
   ⟨⟨0, [2, 0, 1, 2]⟩, ⟨0, [2, 2, 1, 0]⟩⟩,
   ⟨⟨0, [0, 1, 0, 2, 1]⟩, ⟨0, [0, 1, 1, 2, 0]⟩⟩,
   ⟨⟨2, [2, 1, 1, 0, 2]⟩, ⟨2, [2, 1, 2, 0, 1]⟩⟩]

theorem displayedBasis_eq_literalBasis : displayedBasis = literalBasis := by
  decide

theorem displayedBasis_length : displayedBasis.length = 23 := by
  decide

private theorem modelsBridge (table : FiniteTable)
    (checked : bridgeFinBasis.all table.checkIdentity = true) :
    Models table.semigroup bridgeBasis := by
  simpa [bridgeBasis] using
    (models_of_finite_checks table bridgeFinBasis checked)

theorem models_bridge_831_left :
    Models Hull23_1_S3_11_S5_831.G bridgeBasis := by
  simpa [Hull23_1_S3_11_S5_831.G] using
    modelsBridge Hull23_1_S3_11_S5_831.leftTable (by decide)

theorem models_bridge_831_right :
    Models Hull23_1_S3_11_S5_831.H bridgeBasis := by
  simpa [Hull23_1_S3_11_S5_831.H] using
    modelsBridge Hull23_1_S3_11_S5_831.rightTable (by decide)

theorem models_bridge_832_left :
    Models Hull23_1_S3_11_S5_832.G bridgeBasis := by
  simpa [Hull23_1_S3_11_S5_832.G] using
    modelsBridge Hull23_1_S3_11_S5_832.leftTable (by decide)

theorem models_bridge_832_right :
    Models Hull23_1_S3_11_S5_832.H bridgeBasis := by
  simpa [Hull23_1_S3_11_S5_832.H] using
    modelsBridge Hull23_1_S3_11_S5_832.rightTable (by decide)

private theorem modelsProd {A B : Type}
    (left : Semigroup A) (right : Semigroup B)
    {basis : List (Identity Nat)}
    (modelsLeft : Models left basis) (modelsRight : Models right basis) :
    Models (left.prod right) basis := by
  intro identity member
  exact Identity.satisfiedBy_prod
    (modelsLeft identity member) (modelsRight identity member)

private theorem modelsAppend {S : Type} (semigroup : Semigroup S)
    {first second : List (Identity Nat)}
    (modelsFirst : Models semigroup first)
    (modelsSecond : Models semigroup second) :
    Models semigroup (first ++ second) := by
  intro identity member
  rcases List.mem_append.mp member with firstMember | secondMember
  · exact modelsFirst identity firstMember
  · exact modelsSecond identity secondMember

theorem models_displayed_831 :
    Models Hull23_1_S3_11_S5_831.P displayedBasis := by
  simpa [displayedBasis] using
    modelsAppend Hull23_1_S3_11_S5_831.P
      Hull23_1_S3_11_S5_831.models_prod
      (modelsProd Hull23_1_S3_11_S5_831.G
        Hull23_1_S3_11_S5_831.H
        models_bridge_831_left models_bridge_831_right)

theorem models_displayed_832 :
    Models Hull23_1_S3_11_S5_832.P displayedBasis := by
  have modelsPrefix :
      Models Hull23_1_S3_11_S5_832.P
        Hull23_1_S3_11_S5_831.publishedBasis := by
    intro identity member
    apply Hull23_1_S3_11_S5_832.models_prod identity
    simpa only [HullFamilyTransfers.hull23_basis_831_eq_832] using member
  simpa [displayedBasis] using
    modelsAppend Hull23_1_S3_11_S5_832.P modelsPrefix
      (modelsProd Hull23_1_S3_11_S5_832.G
        Hull23_1_S3_11_S5_832.H
        models_bridge_832_left models_bridge_832_right)

private theorem parity_of_left_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy Hull23_1_S3_11_S5_831.G) :
    forall z, identity.lhs.toList.count z % 2 =
      identity.rhs.toList.count z % 2 := by
  have catalogueValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
    simpa [Hull23_1_S3_11_S5_831.G,
      Hull23_1_S3_11_S5_831.leftTable] using valid
  have generatedValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_11.table.semigroup := by
    rw [SemigroupBasis.Generated.S3_11.table_eq_canonical_catalogue]
    exact catalogueValid
  have parityValid :
      identity.SatisfiedBy
        SemigroupBasis.Examples.parityZeroThree.semigroup := by
    rw [SemigroupBasis.Generated.S3_11.table_eq_catalogue_model] at generatedValid
    exact generatedValid
  exact SemigroupBasis.Examples.parityZeroValid_parity identity parityValid

private theorem phase_of_right_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy Hull23_1_S3_11_S5_831.H) :
    SemigroupBasis.CoRoots.S5_831.phaseProfile identity.lhs =
      SemigroupBasis.CoRoots.S5_831.phaseProfile identity.rhs := by
  apply SemigroupBasis.CoRoots.S5_831.valid_samePhaseOccupancySignature identity
  simpa [Hull23_1_S3_11_S5_831.H,
    Hull23_1_S3_11_S5_831.rightTable] using valid

theorem obligation831 :
    Hull23_1_S3_11_S5_831.DerivationalObligation := by
  intro identity validLeft validRight
  exact Order6Hull23_1PhaseParityNormalization.phaseParityNormalization
    (phase_of_right_valid identity validRight)
    (parity_of_left_valid identity validLeft)

theorem obligation832 :
    Hull23_1_S3_11_S5_832.DerivationalObligation :=
  HullFamilyTransfers.hull23_832_of_831 obligation831

theorem product831B15 :
    BasisFor Hull23_1_S3_11_S5_831.P
      Hull23_1_S3_11_S5_831.publishedBasis :=
  Hull23_1_S3_11_S5_831.prod_basisFor_of_obligation obligation831

theorem product832B15 :
    BasisFor Hull23_1_S3_11_S5_832.P
      Hull23_1_S3_11_S5_832.publishedBasis :=
  Hull23_1_S3_11_S5_832.prod_basisFor_of_obligation obligation832

private theorem published831_derives_displayed
    (identity : Identity Nat)
    (member : identity ∈ Hull23_1_S3_11_S5_831.publishedBasis) :
    Derives displayedBasis identity.lhs identity.rhs := by
  apply Derives.fromBasis
  exact List.mem_append_left bridgeBasis member

private theorem published832_derives_displayed
    (identity : Identity Nat)
    (member : identity ∈ Hull23_1_S3_11_S5_832.publishedBasis) :
    Derives displayedBasis identity.lhs identity.rhs := by
  apply published831_derives_displayed
  simpa only [HullFamilyTransfers.hull23_basis_831_eq_832] using member

theorem product831B23 :
    BasisFor Hull23_1_S3_11_S5_831.P displayedBasis :=
  BasisFor.replace product831B15 models_displayed_831
    published831_derives_displayed

theorem product832B23 :
    BasisFor Hull23_1_S3_11_S5_832.P displayedBasis :=
  BasisFor.replace product832B15 models_displayed_832
    published832_derives_displayed

theorem S6_11165_basisFor :
    BasisFor Order6Subdirect.S6_11165.table.semigroup displayedBasis :=
  (Order6Subdirect.S6_11165.basisFor_iff displayedBasis).mpr product831B23

theorem S6_11166_basisFor :
    BasisFor Order6Subdirect.S6_11166.table.semigroup displayedBasis :=
  (Order6Subdirect.S6_11166.basisFor_iff displayedBasis).mpr product832B23

theorem S6_11165_opposite_basisFor :
    BasisFor Order6Subdirect.S6_11165.table.semigroup.opposite
      (reversedBasis displayedBasis) :=
  S6_11165_basisFor.oppositeReversed

theorem S6_11166_opposite_basisFor :
    BasisFor Order6Subdirect.S6_11166.table.semigroup.opposite
      (reversedBasis displayedBasis) :=
  S6_11166_basisFor.oppositeReversed

end Order6Hull23_1PhaseParityB23Endpoints
end CoRoots
end SemigroupBasis
